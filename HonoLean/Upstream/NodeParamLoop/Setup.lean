import HonoLean.Upstream.NodeParamLoop.Contract
import HonoLean.Upstream.CreateNullObject.Correctness

namespace HonoLean.Upstream.NodeParamLoop

open SourceSubset ECMA2025

def allocation : Assignment :=
  ⟨.property (.variable "handlerSet") NodeParamAssignment.paramsKey,
    .invoke (.variable "createNullObject") []⟩

def pushExpr : Expr := .call (.variable "handlerSets") "push" [.variable "handlerSet"]

/-- Structural descriptor conditions, not an assumption about Set's outcome.
Both a first absent field and a prior ordinary W/E/C data field are admitted.
The receiver's existing data flags are deliberately restricted to all true. -/
def Resettable (heap : ObjectHeap) (reference : ObjectRef) (handler : OrdinaryObject) : Prop :=
  (lookupProperty propertyFuel heap reference NodeParamAssignment.paramsKey = .ok none ∨
    ∃ value enumerable configurable,
      lookupProperty propertyFuel heap reference NodeParamAssignment.paramsKey =
        .ok (some (.data value true enumerable configurable))) ∧
  ((handler.own.lookup NodeParamAssignment.paramsKey = none ∧ handler.extensible = true) ∨
    ∃ value, handler.own.lookup NodeParamAssignment.paramsKey = some (.data value true true true))

structure SetupFacts (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) : Prop where
  handlerBinding : before.environment.lookup "handlerSet" = some (.object handlerSet)
  handlersBinding : before.environment.lookup "handlerSets" = some (.array handlerSets)
  helper : ∃ reference environment,
    before.environment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  handlerFound : before.objects[handlerSet]? = some handler
  resettable : Resettable before.objects handlerSet handler
  closed : PrototypeClosed before.objects before.objects.length
  handlersFound : before.heap[handlerSets]? = some priorHandlers

theorem write_fresh_output_field (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (found : before.objects[handlerSet]? = some handler)
    (closed : PrototypeClosed before.objects before.objects.length)
    (resettable : Resettable before.objects handlerSet handler) :
    setProperty propertyFuel (before.objects ++ [emptyNullObject]) handlerSet NodeParamAssignment.paramsKey
      (.object before.objects.length) =
      .ok ((before.objects.set handlerSet
        (newDataObject handler NodeParamAssignment.paramsKey (.object before.objects.length))) ++ [emptyNullObject]) := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
  have frame : ∀ reference, reference < before.objects.length →
      before.objects[reference]? = (before.objects ++ [emptyNullObject])[reference]? := by
    intro reference bound
    exact (List.getElem?_append_left bound).symm
  have lookup := lookupProperty_frame propertyFuel before.objects (before.objects ++ [emptyNullObject])
    before.objects.length frame closed handlerSet inside NodeParamAssignment.paramsKey
  have foundAfter : (before.objects ++ [emptyNullObject])[handlerSet]? = some handler :=
    (List.getElem?_append_left inside).trans found
  rcases resettable with ⟨dispatch, own⟩
  rcases dispatch with missing | ⟨value, enumerable, configurable, inherited⟩
  · rcases own with ⟨absent, extensible⟩ | ⟨old, existing⟩
    · simp [setProperty, ← lookup, missing, writeOwnData, foundAfter, absent, extensible,
        List.set_append_left _ _ inside, bind, Except.bind]
    · simp [setProperty, ← lookup, missing, writeOwnData, foundAfter, existing,
        newDataObject, List.set_append_left _ _ inside, bind, Except.bind]
  · rcases own with ⟨absent, extensible⟩ | ⟨old, existing⟩
    · simp [setProperty, ← lookup, inherited, writeOwnData, foundAfter, absent, extensible,
        List.set_append_left _ _ inside, bind, Except.bind]
    · simp [setProperty, ← lookup, inherited, writeOwnData, foundAfter, existing,
        newDataObject, List.set_append_left _ _ inside, bind, Except.bind]

theorem invoke_helper (fuel limit : Nat) (before : State) (reference : Nat)
    (environment : List (String × Value))
    (binding : before.environment.lookup "createNullObject" = some (.function reference))
    (found : before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩)
    (standard : StandardObjectBinding {before with environment}) :
    evalExpression (fuel + 8) limit (.invoke (.variable "createNullObject") []) before =
      .ok (.object before.objects.length,
        {before with objects := before.objects ++ [emptyNullObject]}) := by
  rcases standard with ambient | ambient <;>
    simp [evalExpression, evalArguments, lookupVariable, binding, found, CreateNullObject.createProgram,
      ambient, intrinsic, createNull, bind, pure, Except.bind, Except.pure]

theorem execute_allocation (fuel limit : Nat) (before : State) (handlerSet : ObjectRef)
    (handler : OrdinaryObject) (handlerSets : Nat) (priorHandlers : List Value)
    (facts : SetupFacts before handlerSet handler handlerSets priorHandlers) :
    executeAssignment (fuel + 10) limit allocation before =
      .ok (.object before.objects.length, resetState before handlerSet handler) := by
  obtain ⟨reference, environment, binding, functionFound, standard⟩ := facts.helper
  have called := invoke_helper (fuel + 1) limit before reference environment binding functionFound standard
  have write := write_fresh_output_field before handlerSet handler facts.handlerFound facts.closed facts.resettable
  have captured : evalReference (fuel + 9) limit allocation.target before =
      .ok (⟨.object handlerSet, .string NodeParamAssignment.paramsKey⟩, before) := by
    simp [allocation, evalReference, evalExpression, lookupVariable, facts.handlerBinding,
      bind, pure, Except.bind, Except.pure]
  simp only [allocation] at captured
  simp only [executeAssignment, evalAssignmentReference, allocation]
  rw [captured]
  simp only [bind, Except.bind, pure, Except.pure, putAssignmentReference]
  change (do
    let (value, state) ← evalExpression (fuel + 9) limit (.invoke (.variable "createNullObject") []) before
    let state ← putReference ⟨.object handlerSet, .string NodeParamAssignment.paramsKey⟩ value state
    pure (value, state)) = _
  rw [called]
  simp [putReference, write, resetState, Except.mapError, bind, pure, Except.bind, Except.pure]

theorem eval_push (fuel limit : Nat) (before : State) (handlerSet : ObjectRef)
    (handler : OrdinaryObject) (handlerSets : Nat) (priorHandlers : List Value)
    (facts : SetupFacts before handlerSet handler handlerSets priorHandlers) :
    evalExpression (fuel + 10) limit pushExpr (resetState before handlerSet handler) =
      .ok (.number (Int.ofNat (priorHandlers.length + 1)),
        setupState before handlerSet handler handlerSets priorHandlers) := by
  simp [pushExpr, evalExpression, evalArguments, lookupVariable, resetState, setupState,
    facts.handlerBinding, facts.handlersBinding, facts.handlersFound, intrinsic,
    bind, pure, Except.bind, Except.pure]

/-- Execute the actual first two statement ASTs, leaving an arbitrary source
continuation to execute in the independently described post-reset/push state. -/
theorem execute_leading (fuel limit : Nat) (tail : List Stmt) (before : State)
    (handlerSet : ObjectRef) (handler : OrdinaryObject) (handlerSets : Nat)
    (priorHandlers : List Value) (facts : SetupFacts before handlerSet handler handlerSets priorHandlers) :
    execute (fuel + 12) limit (.assign allocation :: .evaluate pushExpr :: tail) before =
      execute (fuel + 10) limit tail (setupState before handlerSet handler handlerSets priorHandlers) := by
  simp only [execute]
  rw [execute_allocation (fuel + 1) limit before handlerSet handler handlerSets priorHandlers facts]
  simp only [bind, Except.bind]
  rw [eval_push fuel limit before handlerSet handler handlerSets priorHandlers facts]

/-- info: 'HonoLean.Upstream.NodeParamLoop.execute_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_leading

end HonoLean.Upstream.NodeParamLoop
