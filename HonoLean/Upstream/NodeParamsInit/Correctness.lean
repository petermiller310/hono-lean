import HonoLean.Upstream.NodeParamsInit.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeParamsInit
open SourceSubset ECMA2025

theorem writable_read (before : State) (owner identity source : Nat)
    (writable : NodePrivateWrite.Writable before owner identity (.object source)) :
    privateGet (.object owner) "params" before = .ok (.object source) := by
  obtain ⟨object, found⟩ := writable.allocated
  obtain ⟨fields, brand, field⟩ := writable.data
  apply privateGet_field before owner identity "params" object _ (.object source) writable.scope found
  · rw [PrivateStore.slots_lookup, brand]
    rfl
  · rw [lookup_map_values, field]
    rfl

theorem writable_append (before : State) (owner identity : Nat) (value : Value) (extra : ObjectHeap)
    (writable : NodePrivateWrite.Writable before owner identity value) :
    NodePrivateWrite.Writable {before with objects := before.objects ++ extra} owner identity value := by
  obtain ⟨object, found⟩ := writable.allocated
  exact ⟨writable.scope, ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩, writable.data⟩

theorem header_append (before : State) (owner identity source empty : Nat) (extra : ObjectHeap)
    (inputs : HeaderInputs before owner identity source empty) :
    HeaderInputs {before with objects := before.objects ++ extra} owner identity source empty := by
  obtain ⟨shared, sharedFound⟩ := inputs.emptyFound
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  exact ⟨inputs.nodeBinding, inputs.emptyBinding,
    ⟨shared, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp sharedFound).1).trans sharedFound⟩,
    writable_append before owner identity _ extra inputs.writable,
    ⟨root, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp rootFound).1).trans rootFound⟩⟩

theorem eval_params_read (extra : Nat) (before : State) (owner identity source empty : Nat)
    (inputs : HeaderInputs before owner identity source empty) :
    evalExpression (extra + 4) defaultSplitLimit paramsRead before = .ok (.object source, before) := by
  simp [paramsRead, evalExpression, lookupVariable, inputs.nodeBinding, writable_read before owner identity source inputs.writable,
    bind, Except.bind, pure, Except.pure]

theorem eval_condition (extra : Nat) (before : State) (owner identity source empty : Nat)
    (inputs : HeaderInputs before owner identity source empty) :
    evalExpression (extra + 6) defaultSplitLimit condition before = .ok (.boolean (decide (source = empty)), before) := by
  have read := eval_params_read (extra + 1) before owner identity source empty inputs
  change evalExpression ((extra + 5) + 1) defaultSplitLimit (.strictEqual paramsRead (.variable "emptyParams")) before = _
  rw [evalExpression, read]
  simp [evalExpression, lookupVariable, inputs.emptyBinding, bind, Except.bind, pure, Except.pure]

def emptyState (before : State) : State :=
  {before with
    environment := ("params", .object before.objects.length) :: before.environment
    objects := before.objects ++ [emptyLiteralObject]}

theorem empty_contract (before : State) (owner identity source empty : Nat)
    (inputs : HeaderInputs before owner identity source empty) (equal : source = empty) :
    InitContract before (emptyState before) owner identity source empty := by
  refine ⟨inputs, rfl, by simp, by simp [emptyState], ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact ⟨emptyLiteralObject, by simp [emptyState], rfl, rfl, by simp [WellFormedObject, emptyLiteralObject], Or.inl ⟨equal, rfl⟩⟩
  · intro reference allocated
    exact List.getElem?_append_left allocated
  · have writable := writable_append before owner identity _ [emptyLiteralObject] inputs.writable
    exact writable_read (emptyState before) owner identity source ⟨writable.scope, writable.allocated, writable.data⟩

theorem enumerableData_ready (object : OrdinaryObject) (eligible : EnumerableData object) : CopyReady object := by
  intro key getter setter configurable found
  obtain ⟨value, writable, config, impossible⟩ := eligible.2 key _ found rfl
  cases impossible

theorem enumerableData_of_ready (object : OrdinaryObject) (wellFormed : WellFormedObject object) (ready : CopyReady object) :
    EnumerableData object := by
  refine ⟨wellFormed, ?_⟩
  intro key descriptor found enumerable
  cases descriptor with
  | data value writable enum configurable =>
    cases enum with
    | false => cases enumerable
    | true => exact ⟨value, writable, configurable, rfl⟩
  | accessor getter setter enum configurable =>
    cases enum with
    | false => cases enumerable
    | true => exact False.elim (ready key getter setter configurable found)

theorem copiedFields_of_lookup (source target : OrdinaryObject)
    (lookup : ∀ key, target.own.lookup key = copiedDescriptor source key) : CopiedFields source target := by
  intro key descriptor
  rw [lookup]
  cases own : source.own.lookup key with
  | none => simp [copiedDescriptor, spreadValue, OwnEnumerableValue, own]
  | some property =>
    cases property with
    | data value writable enumerable configurable =>
      cases enumerable <;> simp [copiedDescriptor, spreadValue, OwnEnumerableValue, own, eq_comm]
    | accessor getter setter enumerable configurable =>
      simp [copiedDescriptor, spreadValue, OwnEnumerableValue, own]

def allocatedState (before : State) : State := {before with objects := before.objects ++ [emptyLiteralObject]}
def copiedObject (source : OrdinaryObject) : OrdinaryObject := spreadFold source (ownStringKeys source) emptyLiteralObject
def copiedState (before : State) (object : OrdinaryObject) : State :=
  {before with
    environment := ("params", .object before.objects.length) :: before.environment
    objects := before.objects ++ [copiedObject object]}

theorem eval_shared_initializer (extra : Nat) (before : State) (owner identity source empty : Nat)
    (inputs : HeaderInputs before owner identity source empty) (equal : source = empty) :
    evalObjectInitExpression (extra + 16) defaultSplitLimit initializer before = .ok (.object before.objects.length, allocatedState before) := by
  have guard := eval_condition (extra + 9) before owner identity source empty inputs
  simp only [equal, decide_true] at guard
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  change evalObjectInitExpression ((extra + 15) + 1) defaultSplitLimit
    (.conditional condition (.objectLiteral []) (.objectLiteral [.spread paramsRead])) before = _
  rw [evalObjectInitExpression, guard]
  simp [evalObjectInitExpression, evalObjectInitItems, createLiteralObject, ordinaryObjectPrototype, rootFound,
    allocatedState, bind, Except.bind, pure, Except.pure]

theorem source_shared_satisfies (extra : Nat) (before : State) (owner identity source empty : Nat)
    (inputs : HeaderInputs before owner identity source empty) (equal : source = empty) :
    sourceInit (extra + 16) before = some (.ok (emptyState before)) ∧ InitContract before (emptyState before) owner identity source empty := by
  have evaluated := eval_shared_initializer extra before owner identity source empty inputs equal
  have run : executeObjectInitDeclaration (extra + 16) defaultSplitLimit program before = .ok (emptyState before) := by
    simp [executeObjectInitDeclaration, executeObjectInit, program, evaluated, emptyState, allocatedState, bind, Except.bind, pure, Except.pure]
  exact ⟨by simpa [sourceInit, parses_source] using congrArg some run, empty_contract before owner identity source empty inputs equal⟩

theorem copy_after_allocation (extra : Nat) (before : State) (owner identity source empty : Nat) (object : OrdinaryObject)
    (inputs : CopyInputs before owner identity source empty object) :
    copyDataProperties (extra + (ownStringKeys object).length + 13) before.objects.length source (allocatedState before) =
      .ok {before with objects := before.objects ++ [copiedObject object]} := by
  have sourceBound := (List.getElem?_eq_some_iff.mp inputs.sourceFound).1
  have found : (allocatedState before).objects[source]? = some object :=
    (List.getElem?_append_left sourceBound).trans inputs.sourceFound
  have targetFound : (allocatedState before).objects[before.objects.length]? = some emptyLiteralObject := by simp [allocatedState]
  have copy := copyDataPropertiesInOrder_exec (extra + 12) before.objects.length source (ownStringKeys object) (allocatedState before)
    object emptyLiteralObject found targetFound (by omega) (enumerableData_ready object inputs.eligible) emptyLiteral_spreadReady
  unfold copyDataProperties
  rw [found]
  simp only [bind, Except.bind]
  rw [show extra + (ownStringKeys object).length + 13 = extra + 12 + (ownStringKeys object).length + 1 by omega, copy]
  simp [allocatedState, copiedObject, List.set_append_right]

theorem eval_copy_initializer (extra : Nat) (before : State) (owner identity source empty : Nat) (object : OrdinaryObject)
    (inputs : CopyInputs before owner identity source empty object) :
    evalObjectInitExpression (extra + (ownStringKeys object).length + 16) defaultSplitLimit initializer before =
      .ok (.object before.objects.length, {before with objects := before.objects ++ [copiedObject object]}) := by
  have guard := eval_condition (extra + (ownStringKeys object).length + 9) before owner identity source empty inputs.toHeaderInputs
  simp only [inputs.different, decide_false] at guard
  have reread := eval_params_read (extra + (ownStringKeys object).length + 9) (allocatedState before) owner identity source empty
    (header_append before owner identity source empty [emptyLiteralObject] inputs.toHeaderInputs)
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  have made := createLiteralObject_of_root before root rootFound
  have copy := copy_after_allocation extra before owner identity source empty object inputs
  change evalObjectInitExpression ((extra + (ownStringKeys object).length + 15) + 1) defaultSplitLimit
    (.conditional condition (.objectLiteral []) (.objectLiteral [.spread paramsRead])) before = _
  rw [evalObjectInitExpression, guard]
  simp only [bind, Except.bind, truthy]
  change evalObjectInitExpression ((extra + (ownStringKeys object).length + 14) + 1) defaultSplitLimit
    (.objectLiteral [.spread paramsRead]) before = _
  rw [evalObjectInitExpression, made]
  simp only [bind, Except.bind]
  change (do
    let state ← evalObjectInitItems (extra + (ownStringKeys object).length + 14) defaultSplitLimit before.objects.length [.spread paramsRead] (allocatedState before)
    pure (Value.object before.objects.length, state)) = _
  rw [evalObjectInitItems, reread]
  simp only [bind, Except.bind]
  rw [copy]
  rfl

theorem copy_contract (before : State) (owner identity source empty : Nat) (object : OrdinaryObject)
    (inputs : CopyInputs before owner identity source empty object) :
    InitContract before (copiedState before object) owner identity source empty := by
  have ready := spreadFold_ready object (ownStringKeys object) emptyLiteralObject emptyLiteral_spreadReady
  have well := spreadFold_wellFormed object (ownStringKeys object) emptyLiteralObject (by simp [WellFormedObject, emptyLiteralObject])
  have fields := copiedFields_of_lookup object (copiedObject object)
    (spreadFold_all_keys object (ownStringKeys object) (ownStringKeys_order object inputs.eligible.1))
  refine ⟨inputs.toHeaderInputs, rfl, by simp, by simp [copiedState], ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact ⟨copiedObject object, by simp [copiedState], spreadFold_prototype object _ _, ready.extensible,
      well, Or.inr ⟨inputs.different, object, inputs.sourceFound, inputs.eligible, fields⟩⟩
  · intro reference allocated
    exact List.getElem?_append_left allocated
  · have writable := writable_append before owner identity _ [copiedObject object] inputs.writable
    exact writable_read (copiedState before object) owner identity source ⟨writable.scope, writable.allocated, writable.data⟩

theorem source_copy_satisfies (extra : Nat) (before : State) (owner identity source empty : Nat) (object : OrdinaryObject)
    (inputs : CopyInputs before owner identity source empty object) :
    sourceInit (extra + (ownStringKeys object).length + 16) before = some (.ok (copiedState before object)) ∧
      InitContract before (copiedState before object) owner identity source empty := by
  have evaluated := eval_copy_initializer extra before owner identity source empty object inputs
  have run : executeObjectInitDeclaration (extra + (ownStringKeys object).length + 16) defaultSplitLimit program before = .ok (copiedState before object) := by
    simp [executeObjectInitDeclaration, executeObjectInit, program, evaluated, copiedState, bind, Except.bind, pure, Except.pure]
  exact ⟨by simpa [sourceInit, parses_source] using congrArg some run, copy_contract before owner identity source empty object inputs⟩

/-- The next copy/guard readiness follows from what this source produced. It
is not a desired future clone/readiness premise. -/
theorem result_data_only (before after : State) (owner identity source empty : Nat)
    (contract : InitContract before after owner identity source empty) :
    ∃ target, after.objects[before.objects.length]? = some target ∧ EnumerableData target := by
  obtain ⟨target, found, _, _, well, branch⟩ := contract.object
  refine ⟨target, found, well, ?_⟩
  intro key descriptor present _
  rcases branch with ⟨_, none⟩ | ⟨_, prior, _, _, fields⟩
  · simp [EmptyFields] at none
    simp [none] at present
  · obtain ⟨value, _, copied⟩ := (fields key descriptor).mp present
    exact ⟨value, true, true, copied⟩

/-- info: 'HonoLean.Upstream.NodeParamsInit.source_shared_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_shared_satisfies
/-- info: 'HonoLean.Upstream.NodeParamsInit.source_copy_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_copy_satisfies

end HonoLean.Upstream.NodeParamsInit
