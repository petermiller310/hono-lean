import HonoLean.Upstream.MethodsLoop.Contract

namespace HonoLean.Upstream.MethodsLoop

open SourceSubset ECMA2025

theorem body_names : declaredNames body = ["m", "handlerSet"] := rfl

theorem body_lookup_other (before : State) (name : String)
    (notM : name ≠ "m") (notHandler : name ≠ "handlerSet") :
    (bodyEntry before).environment.lookup name = before.environment.lookup name :=
  lookup_withoutBindings _ _ _ (by simp [notM, notHandler])

theorem row_lookup_other (before : State) (row : ObjectRef) (name : String)
    (notM : name ≠ "m") (notHandler : name ≠ "handlerSet") :
    (rowState before row).environment.lookup name = before.environment.lookup name := by
  simpa [rowState, List.lookup_cons, beq_false_of_ne notM] using
    body_lookup_other before name notM notHandler

theorem choice_row (before : State) (row : ObjectRef) (method : JSString) (chosen : Value)
    (choice : SearchEntry.Choice before row method chosen) :
    SearchEntry.Choice (rowState before row) row method chosen := by
  obtain ⟨direct, read, cases⟩ := choice
  refine ⟨direct, read, ?_⟩
  rcases cases with direct | ⟨falsy, key, imported, fallback⟩
  · exact Or.inl direct
  · refine Or.inr ⟨falsy, key, ?_, fallback⟩
    rw [row_lookup_other before row "METHOD_NAME_ALL" (by decide) (by decide)]
    exact imported

theorem choice_exists (before : State) (row : ObjectRef) (method : JSString)
    (domain : SearchEntry.ChoiceDomain before row method) :
    ∃ chosen, SearchEntry.Choice before row method chosen := by
  obtain ⟨direct, read, fallback⟩ := domain
  by_cases truth : NodeParamAssignment.Truthy direct
  · exact ⟨direct, direct, read, Or.inl ⟨truth, rfl⟩⟩
  · obtain ⟨key, chosen, imported, rightRead⟩ := fallback truth
    exact ⟨chosen, direct, read, Or.inr ⟨truth, key, imported, rightRead⟩⟩

theorem row_inputs {origin before : State} {rows : List Value} {method : JSString}
    {owner stamp methods collector count row : Nat} {selected : List ObjectRef}
    (inputs : Inputs origin owner stamp methods collector rows method)
    (trace : Processed origin rows method collector count before selected)
    (atRow : rows[count]? = some (.object row)) :
    SearchEntry.RowInputs (bodyEntry before) owner stamp methods count rows (.object row) := by
  have env := processed_environment trace
  have frames := processed_frames trace inputs.separate
  obtain ⟨object, ownerFound⟩ := inputs.ownerFound
  obtain ⟨ownerBound, _⟩ := List.getElem?_eq_some_iff.mp ownerFound
  have ownerBoundNow : owner < before.objects.length := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [body_lookup_other before "node" (by decide) (by decide), env, header,
      NodeParamLoop.header_lookup_other _ _ _ "node" (by decide) (by decide)]
    exact inputs.nodeBinding
  · rw [body_lookup_other before "i" (by decide) (by decide), env]
    exact NodeParamLoop.header_lookup_i _ _ _
  · exact ⟨before.objects[owner], List.getElem?_eq_getElem ownerBoundNow⟩
  · simpa [bodyEntry, frames.1] using inputs.privateName
  · simpa [bodyEntry, frames.1] using inputs.privateSlot
  · exact frames.2.1.trans inputs.methodsFound
  · simp [atRow]

theorem method_binding {origin before : State} {rows : List Value} {method : JSString}
    {owner stamp methods collector count : Nat} {selected : List ObjectRef}
    (inputs : Inputs origin owner stamp methods collector rows method)
    (trace : Processed origin rows method collector count before selected) :
    before.environment.lookup "method" = some (.string method) := by
  rw [processed_environment trace, header,
    NodeParamLoop.header_lookup_other _ _ _ "method" (by decide) (by decide)]
  exact inputs.methodBinding

theorem execute_body_step (extra limit : Nat) {origin before : State} {rows : List Value} {method : JSString}
    {owner stamp methods collector count keyBound : Nat} {selected : List ObjectRef}
    (inputs : Inputs origin owner stamp methods collector rows method)
    (trace : Processed origin rows method collector count before selected)
    (domain : NormalPrefixes origin rows method collector keyBound) (inside : count < rows.length) :
    ∃ after selected',
      execute (extra + keyBound + 100) limit body (bodyEntry before) = .ok (.normal after) ∧
      Processed origin rows method collector (count + 1)
        (nextState origin.environment count rows.length after) selected' := by
  obtain ⟨row, atRow, reads, captures⟩ := domain count before selected trace inside
  obtain ⟨chosen, choice⟩ := choice_exists before row method reads
  have rowRun := MethodsLoopSupport.row_continuation (extra + keyBound + 65) limit
    (SearchEntry.selectionProgram ++ [.branch (.variable "handlerSet") NodeParamLoop.program])
    (bodyEntry before) owner stamp methods count rows (.object row) (row_inputs inputs trace atRow)
  have choiceBindings : SearchEntry.ChoiceBindings (rowState before row) row method := by
    refine ⟨by simp [rowState], ?_⟩
    rw [row_lookup_other before row "method" (by decide) (by decide)]
    exact method_binding inputs trace
  have choiceRun := MethodsLoopSupport.choice_continuation (extra + keyBound + 64) limit
    [.branch (.variable "handlerSet") NodeParamLoop.program] (rowState before row) row method chosen
    choiceBindings (choice_row before row method chosen choice)
  have leading : execute (extra + keyBound + 100) limit body (bodyEntry before) =
      execute (extra + keyBound + 98) limit [.branch (.variable "handlerSet") NodeParamLoop.program]
        (selectedState before row chosen) := by
    simpa [body, rowState, selectedState, Nat.add_assoc] using rowRun.trans choiceRun
  by_cases truth : NodeParamAssignment.Truthy chosen
  · obtain ⟨handlerRef, handler, keysArray, priorHandlers, parameterReceiver, nodeParams, snapshot,
      equal, entry, keyCount⟩ := captures chosen choice truth
    subst chosen
    have budget : (extra + (keyBound - snapshot.keys.length) + 33) + snapshot.keys.length + 65 =
        extra + keyBound + 98 := by omega
    obtain ⟨after, run, contract⟩ := MethodsLoopSupport.guard_capture_satisfies
      (extra + (keyBound - snapshot.keys.length) + 33) limit
      (selectedState before row (.object handlerRef)) handlerRef handler collector keysArray priorHandlers
      parameterReceiver nodeParams snapshot entry
    rw [budget] at run
    refine ⟨after, selected ++ [handlerRef], leading.trans run, ?_⟩
    exact .capture trace atRow choice entry contract
  · have binding : (selectedState before row chosen).environment.lookup "handlerSet" = some chosen := by
      simp [selectedState]
    have falseValue : truthy chosen = false := by
      cases observed : truthy chosen
      · rfl
      · exact False.elim (truth ((NodeParamAssignment.truthy_iff chosen).mp observed))
    have skip := MethodsLoopSupport.guard_skips (extra + keyBound + 95) limit []
      (selectedState before row chosen) chosen binding falseValue
    have skipRun : execute (extra + keyBound + 98) limit
        [.branch (.variable "handlerSet") NodeParamLoop.program] (selectedState before row chosen) =
        .ok (.normal (selectedState before row chosen)) := by
      simpa [Nat.add_assoc, execute] using skip
    refine ⟨selectedState before row chosen, selected, leading.trans skipRun, ?_⟩
    have skipped := Processed.skip trace atRow choice truth
    simpa [nextState, selectedState, rowState, bodyEntry] using skipped

theorem initialize_header (extra limit : Nat) (origin : State)
    (owner stamp methods collector : Nat) (rows : List Value) (method : JSString)
    (inputs : Inputs origin owner stamp methods collector rows method) :
    initializeBindings (extra + 8) limit initializers
      {origin with environment := withoutBindings origin.environment ["i", "len"]} =
      .ok {origin with environment := header origin.environment 0 rows.length} := by
  obtain ⟨object, ownerFound⟩ := inputs.ownerFound
  obtain ⟨fields, fieldsFound, slotFound⟩ := inputs.privateSlot
  have binding : (withoutBindings origin.environment ["i", "len"]).lookup "node" = some (.object owner) := by
    rw [lookup_withoutBindings _ _ _ (by decide)]
    exact inputs.nodeBinding
  simp [initializers, initializeBindings, evalExpression, methodsExpression, lookupVariable, binding,
    privateGet, inputs.privateName, ownerFound, fieldsFound, slotFound, readProperty,
    inputs.methodsFound, NodeParamLoop.lengthKey, header, NodeParamLoop.headerEnvironment,
    List.lookup_cons, bind, pure, Except.bind, Except.pure]

theorem execute_iterations (remaining keyBound limit : Nat) {origin before : State} {rows : List Value}
    {method : JSString} {owner stamp methods collector count : Nat} {selected : List ObjectRef}
    (inputs : Inputs origin owner stamp methods collector rows method)
    (domain : NormalPrefixes origin rows method collector keyBound)
    (trace : Processed origin rows method collector count before selected)
    (remainingCount : count + remaining = rows.length) :
    ∃ completed allSelected, Processed origin rows method collector rows.length completed allSelected ∧
      executeFor (remaining + keyBound + 102) limit condition "i" body before = .ok (.normal completed) := by
  induction remaining generalizing count before selected with
  | zero =>
    have atEnd : count = rows.length := by omega
    refine ⟨before, selected, ?_, ?_⟩
    · simpa [atEnd] using trace
    · have test := NodeParamLoop.eval_condition (keyBound + 98) limit before origin.environment count rows.length
        (processed_environment trace)
      rw [show 0 + keyBound + 102 = (keyBound + 101) + 1 by omega]
      rw [executeFor]
      rw [show evalExpression (keyBound + 101) limit condition before =
        .ok (.boolean (decide (count < rows.length)), before) by simpa [condition, NodeParamLoop.condition, Nat.add_assoc] using test]
      simp [atEnd, bind, pure, Except.bind, Except.pure, truthy]
  | succ remaining ih =>
    have inside : count < rows.length := by omega
    obtain ⟨after, selected', bodyRun, nextTrace⟩ := execute_body_step (remaining + 2) limit inputs trace domain inside
    obtain ⟨completed, allSelected, complete, iterated⟩ := ih nextTrace (by omega)
    refine ⟨completed, allSelected, complete, ?_⟩
    have test := NodeParamLoop.eval_condition (remaining + keyBound + 99) limit before origin.environment count rows.length
      (processed_environment trace)
    have conditionRun : evalExpression (remaining + keyBound + 102) limit condition before =
        .ok (.boolean true, before) := by
      simpa [condition, NodeParamLoop.condition, inside, Nat.add_assoc] using test
    have currentBody : execute (remaining + keyBound + 102) limit body (bodyEntry before) =
        .ok (.normal after) := by
      rwa [show remaining + 2 + keyBound + 100 = remaining + keyBound + 102 by omega] at bodyRun
    have increment : incrementVariable "i" {after with environment := before.environment} =
        .ok (nextState origin.environment count rows.length after) := by
      have stepped := NodeParamLoop.increment_header {after with environment := before.environment}
        origin.environment count rows.length (by change before.environment = _; exact processed_environment trace)
      simpa [nextState, header] using stepped
    rw [show remaining + 1 + keyBound + 102 = (remaining + keyBound + 102) + 1 by omega]
    rw [executeFor]
    rw [conditionRun]
    simp only [bind, Except.bind, truthy, ↓reduceIte]
    change (do
      let completion ← execute (remaining + keyBound + 102) limit body (bodyEntry before)
      match restoreCompletion before.environment completion with
      | .returned value state => pure (Completion.returned value state)
      | .normal state => do
        let state ← incrementVariable "i" state
        executeFor (remaining + keyBound + 102) limit condition "i" body state) = _
    rw [currentBody]
    simp only [bind, Except.bind, restoreCompletion]
    rw [increment]
    exact iterated

/-- The source constructs its saved methods length, executes each original row
in index order, skips falsy choices, and derives captures for admitted truthy
records. NormalPrefixes remains an explicit trajectory-wide structural domain;
no successful future execution or completed output is supplied as a premise. -/
theorem parsed_loop_satisfies (keyBound : Nat) (origin : State)
    (owner stamp methods collector : Nat) (rows : List Value) (method : JSString)
    (inputs : Inputs origin owner stamp methods collector rows method)
    (domain : NormalPrefixes origin rows method collector keyBound) :
    ∃ after,
      (parseBlock pinnedSource bindings ["methods"]).map
        (fun source => runBlock (rows.length + keyBound + 103) source origin) = some (.ok (.normal after)) ∧
      LoopContract origin after rows method collector := by
  obtain ⟨completed, selected, trace, iterated⟩ := execute_iterations rows.length keyBound defaultSplitLimit inputs domain
    (Processed.start (origin := origin) (rows := rows) (method := method) (collector := collector)) (by omega)
  let after := {completed with environment := origin.environment}
  refine ⟨after, ?_, completed, selected, trace, rfl⟩
  have initialized := initialize_header (rows.length + keyBound + 94) defaultSplitLimit origin
    owner stamp methods collector rows method inputs
  rw [show rows.length + keyBound + 94 + 8 = rows.length + keyBound + 102 by omega] at initialized
  have noDeclarations : declaredNames program = [] := rfl
  have filter : withoutBindings origin.environment [] = origin.environment := by simp [withoutBindings]
  rw [parses_source, Option.map_some]
  apply congrArg some
  simp only [runBlock, noDeclarations, filter]
  simp only [program]
  rw [show rows.length + keyBound + 103 = (rows.length + keyBound + 102) + 1 by omega]
  rw [execute]
  simp only [show initializers.map Prod.fst = ["i", "len"] from rfl]
  rw [initialized]
  simp only [bind, Except.bind]
  rw [iterated]
  simp [restoreCompletion, execute, after, pure, Except.pure]

theorem parsed_loop_correct (keyBound : Nat) (origin after : State)
    (owner stamp methods collector : Nat) (rows : List Value) (method : JSString)
    (inputs : Inputs origin owner stamp methods collector rows method)
    (domain : NormalPrefixes origin rows method collector keyBound)
    (observed : (parseBlock pinnedSource bindings ["methods"]).map
      (fun source => runBlock (rows.length + keyBound + 103) source origin) = some (.ok (.normal after))) :
    LoopContract origin after rows method collector := by
  obtain ⟨completed, execution, contract⟩ := parsed_loop_satisfies keyBound origin owner stamp methods collector rows method inputs domain
  rw [execution] at observed
  simp only [Option.some.injEq, Except.ok.injEq, Completion.normal.injEq] at observed
  exact observed ▸ contract

/-- info: 'HonoLean.Upstream.MethodsLoop.parsed_loop_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_loop_satisfies

end HonoLean.Upstream.MethodsLoop
