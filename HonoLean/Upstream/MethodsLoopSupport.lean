import HonoLean.Upstream.NodeParamLoop.Correctness
import HonoLean.Upstream.SearchEntry.Row
import HonoLean.Upstream.SearchEntry.MethodChoice

namespace HonoLean.Upstream.MethodsLoopSupport

open SourceSubset ECMA2025 NodeParamLoop

/-- The independent lazy-choice relation is functional at a fixed state. The
proof uses actual direct/fallback reads and binding identity, not execution. -/
theorem choice_unique (before : State) (row : ObjectRef) (method : JSString) (left right : Value)
    (first : SearchEntry.Choice before row method left)
    (second : SearchEntry.Choice before row method right) : left = right := by
  obtain ⟨directLeft, leftRead, leftCases⟩ := first
  obtain ⟨directRight, rightRead, rightCases⟩ := second
  have sameDirect : directLeft = directRight := Except.ok.inj (leftRead.symm.trans rightRead)
  subst directRight
  rcases leftCases with ⟨leftTruthy, leftEqual⟩ | ⟨leftFalsy, leftKey, leftImported, leftFallback⟩
  · rcases rightCases with ⟨_, rightEqual⟩ | ⟨rightFalsy, _, _, _⟩
    · exact leftEqual.trans rightEqual.symm
    · exact False.elim (rightFalsy leftTruthy)
  · rcases rightCases with ⟨rightTruthy, _⟩ | ⟨_, rightKey, rightImported, rightFallback⟩
    · exact False.elim (leftFalsy rightTruthy)
    · have sameKey : leftKey = rightKey := Value.string.inj (Option.some.inj (leftImported.symm.trans rightImported))
      subst rightKey
      exact Except.ok.inj (leftFallback.symm.trans rightFallback)

theorem prefix_zero {snapshot : Snapshot} {object : OrdinaryObject}
    (captured : Prefix snapshot 0 object) : object = emptyNullObject := by
  obtain ⟨entries, captures, rfl⟩ := captured
  cases captures
  rfl

theorem entry_empty_keys (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot)
    (empty : before.heap[keysArray]? = some []) : snapshot.keys = [] := by
  have mapped : snapshot.keys.map Value.string = [] := Option.some.inj (entry.keysFound.symm.trans empty)
  exact List.map_eq_nil_iff.mp mapped

/-- With no possible keys the independent capture endpoint is exactly reset
and append. Snapshot functions cannot manufacture an arbitrary extra mutation. -/
theorem contract_empty_keys (before after : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (snapshot : Snapshot)
    (empty : snapshot.keys = [])
    (contract : BlockContract before after handlerSet handler handlerSets priorHandlers snapshot) :
    after = setupState before handlerSet handler handlerSets priorHandlers := by
  obtain ⟨output, captured, equal⟩ := contract
  have emptyPrefix : Prefix snapshot 0 output := by simpa only [empty, List.length_nil] using captured
  have outputEqual := prefix_zero emptyPrefix
  rw [outputEqual] at equal
  have fresh := setup_fresh_cell before handlerSet handler handlerSets priorHandlers
  obtain ⟨inside, atFresh⟩ := List.getElem?_eq_some_iff.mp fresh
  have unchanged : (setupState before handlerSet handler handlerSets priorHandlers).objects.set
      before.objects.length emptyNullObject = (setupState before handlerSet handler handlerSets priorHandlers).objects := by
    rw [← atFresh, List.set_getElem_self inside]
  simpa only [unchanged] using equal

/-- Extra fuel is available beneath an enclosing counted loop. The proof still
executes every key and derives its prefix, rather than assuming a body trace. -/
theorem execute_counted_padded (extra limit : Nat) (base : State)
    (handlerSet output keysArray nodeParams : Nat) (parameterReceiver : Value) (snapshot : Snapshot)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot) :
    ∃ finalObject, Prefix snapshot snapshot.keys.length finalObject ∧
      execute (extra + snapshot.keys.length + 62) limit [.countedFor initializers condition "i" body] base =
        .ok (.normal {base with objects := base.objects.set output finalObject}) := by
  obtain ⟨finalObject, complete, iterated⟩ := execute_iterations_padded extra snapshot.keys.length limit base
    handlerSet output keysArray nodeParams 0 parameterReceiver snapshot emptyNullObject facts
    (prefix_empty snapshot) (by omega)
  refine ⟨finalObject, complete, ?_⟩
  have initialized := initialize_header (extra + snapshot.keys.length + 53) limit base handlerSet keysArray snapshot.keys
    facts.handlerBinding facts.handlerKeys facts.keysFound
  rw [show extra + snapshot.keys.length + 62 = (extra + snapshot.keys.length + 61) + 1 by omega, execute]
  change (do
    let state ← initializeBindings (extra + snapshot.keys.length + 61) limit initializers
      {base with environment := withoutBindings base.environment ["i", "len"]}
    let completion ← executeFor (extra + snapshot.keys.length + 61) limit condition "i" body state
    match restoreCompletion base.environment completion with
    | .normal state => execute (extra + snapshot.keys.length + 61) limit [] state
    | .returned value state => pure (Completion.returned value state)) = _
  rw [initialized]
  simp only [bind, Except.bind]
  rw [← loopState_empty base output snapshot.keys.length facts.outputEmpty, iterated]
  simp [restoreCompletion, execute, loopState]

/-- The actual chosen-handler body executes at any larger sufficient budget.
It has no direct declarations, so it preserves its incoming value environment;
the nested key-loop owns and restores its own i/len/key bindings. -/
theorem capture_execute_satisfies (extra limit : Nat) (before : State)
    (handlerSet : ObjectRef) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ after,
      execute (extra + snapshot.keys.length + 64) limit program before = .ok (.normal after) ∧
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  let base := setupState before handlerSet handler handlerSets priorHandlers
  have facts := entry_loopFacts before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot entry
  obtain ⟨finalObject, complete, executed⟩ := execute_counted_padded extra limit base
    handlerSet before.objects.length keysArray nodeParams parameterReceiver snapshot facts
  let after := {base with objects := base.objects.set before.objects.length finalObject}
  refine ⟨after, ?_, finalObject, complete, rfl⟩
  change execute ((extra + snapshot.keys.length + 52) + 12) limit
    (.assign allocation :: .evaluate pushExpr :: [.countedFor initializers condition "i" body]) before = _
  rw [execute_leading (extra + snapshot.keys.length + 52) limit _ before handlerSet handler handlerSets priorHandlers entry.toSetupFacts]
  exact executed

theorem capture_execute_correct (extra limit : Nat) (before after : State)
    (handlerSet : ObjectRef) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    execute (extra + snapshot.keys.length + 64) limit program before = .ok (.normal after) ↔
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  obtain ⟨completed, execution, contract⟩ := capture_execute_satisfies extra limit before handlerSet handler
    handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot entry
  constructor
  · intro observed
    rw [execution] at observed
    simp only [Except.ok.injEq, Completion.normal.injEq] at observed
    exact observed ▸ contract
  · intro desired
    have equal := block_contract_unique before completed after handlerSet handler handlerSets priorHandlers snapshot contract desired
    rw [← equal]
    exact execution

theorem capture_environment (before after : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (snapshot : Snapshot)
    (contract : BlockContract before after handlerSet handler handlerSets priorHandlers snapshot) :
    after.environment = before.environment := by
  obtain ⟨output, _, rfl⟩ := contract
  rfl

theorem capture_runBlock_satisfies (extra : Nat) (before : State)
    (handlerSet : ObjectRef) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ after,
      runBlock (extra + snapshot.keys.length + 64) program before = .ok (.normal after) ∧
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  obtain ⟨after, execution, contract⟩ := capture_execute_satisfies extra defaultSplitLimit before
    handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot entry
  refine ⟨after, ?_, contract⟩
  have scopeNames : withoutBindings before.environment (declaredNames program) = before.environment := by
    simp [program, declaredNames, withoutBindings]
  simp only [runBlock, scopeNames, execution, bind, Except.bind, restoreCompletion]
  rw [← capture_environment before after handlerSet handler handlerSets priorHandlers snapshot contract]
  rfl

/-- Raw declaration sequencing beneath the enclosing loop's own body scope.
No second standalone-fragment filter is inserted between declarations. -/
theorem row_continuation (extra limit : Nat) (tail : List Stmt) (before : State)
    (owner stamp methods index : Nat) (entries : List Value) (row : Value)
    (inputs : SearchEntry.RowInputs before owner stamp methods index entries row) :
    execute (extra + 35) limit (SearchEntry.rowProgram ++ tail) before =
      execute (extra + 34) limit tail {before with environment := ("m", row) :: before.environment} := by
  obtain ⟨object, ownerFound⟩ := inputs.ownerFound
  obtain ⟨fields, fieldsFound, slotFound⟩ := inputs.privateSlot
  simp [SearchEntry.rowProgram, execute, evalExpression, lookupVariable,
    inputs.nodeBinding, inputs.indexBinding, privateGet, inputs.privateName, ownerFound,
    fieldsFound, slotFound, readProperty, inputs.methodsFound, inputs.rowRead,
    bind, pure, Except.bind, Except.pure]

theorem choice_continuation (extra limit : Nat) (tail : List Stmt) (before : State)
    (row : ObjectRef) (method : JSString) (chosen : Value)
    (bindings : SearchEntry.ChoiceBindings before row method)
    (choice : SearchEntry.Choice before row method chosen) :
    execute (extra + 35) limit (SearchEntry.selectionProgram ++ tail) before =
      execute (extra + 34) limit tail
        {before with environment := ("handlerSet", chosen) :: before.environment} := by
  obtain ⟨direct, read, cases⟩ := choice
  rcases cases with ⟨truth, rfl⟩ | ⟨falsy, key, imported, rightRead⟩
  · have truthValue := (NodeParamAssignment.truthy_iff chosen).mpr truth
    simp [SearchEntry.selectionProgram, SearchEntry.selectionExpression, execute, evalExpression,
      lookupVariable, bindings.rowBinding, bindings.methodBinding, readProperty, read,
      truthValue, Except.mapError, bind, pure, Except.bind, Except.pure, -truthy]
  · have truthValue : truthy direct = false := by
      cases observed : truthy direct
      · rfl
      · exact False.elim (falsy ((NodeParamAssignment.truthy_iff direct).mp observed))
    simp [SearchEntry.selectionProgram, SearchEntry.selectionExpression, execute, evalExpression,
      lookupVariable, bindings.rowBinding, bindings.methodBinding, readProperty, read,
      imported, rightRead, truthValue, Except.mapError, bind, pure, Except.bind, Except.pure, -truthy]

/-- A falsy source guard skips the entire capture body. None of the body's
handler shape, helper binding, params or collector premises are needed. -/
theorem guard_skips (extra limit : Nat) (tail : List Stmt) (before : State) (chosen : Value)
    (binding : before.environment.lookup "handlerSet" = some chosen)
    (falsy : truthy chosen = false) :
    execute (extra + 3) limit (.branch (.variable "handlerSet") program :: tail) before =
      execute (extra + 2) limit tail before := by
  simp [execute, evalExpression, lookupVariable, binding, falsy,
    bind, pure, Except.bind, Except.pure, -truthy]

/-- The actual truthy guard runs the source body with the established record
domain. A type assertion alone cannot provide that domain. -/
theorem guard_capture_satisfies (extra limit : Nat) (before : State)
    (handlerSet : ObjectRef) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ after,
      execute (extra + snapshot.keys.length + 65) limit
        [.branch (.variable "handlerSet") program] before = .ok (.normal after) ∧
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  obtain ⟨after, executed, contract⟩ := capture_execute_satisfies extra limit before handlerSet handler
    handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot entry
  refine ⟨after, ?_, contract⟩
  rw [show extra + snapshot.keys.length + 65 = (extra + snapshot.keys.length + 64) + 1 by omega, execute]
  have evaluated : evalExpression (extra + snapshot.keys.length + 64) limit (.variable "handlerSet") before =
      .ok (.object handlerSet, before) := by
    simp only [evalExpression, lookupVariable, entry.handlerBinding]
    rfl
  rw [evaluated]
  simp only [bind, Except.bind, truthy, ↓reduceIte, executed]
  simp [execute]

/-- info: 'HonoLean.Upstream.MethodsLoopSupport.capture_execute_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capture_execute_correct

end HonoLean.Upstream.MethodsLoopSupport
