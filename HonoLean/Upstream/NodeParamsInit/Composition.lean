import HonoLean.Upstream.NodeParamsInit.Correctness
import HonoLean.Upstream.NodeCaptureGuard.Composition
import HonoLean.Upstream.NodeSearchSetup.Correctness
import HonoLean.Upstream.NodePrivateWrite.Correctness
import HonoLean.Upstream.SourceSubset.PrivateWrite

set_option autoImplicit false
namespace HonoLean.Upstream.NodeParamsInit
open SourceSubset ECMA2025

/-- Explicit fragment-entry activation, not a proof that the omitted search
pattern loop selected this owner. The prior environment is retained as a tail. -/
def nodeActivation (state : State) (owner : Nat) : State :=
  {state with environment := ("node", .object owner) :: state.environment}
def childActivation (state : State) (child : Nat) : State :=
  {state with environment := ("child", .object child) :: state.environment}

theorem writable_written (before : State) (owner identity : Nat) (old value : Value)
    (writable : NodePrivateWrite.Writable before owner identity old) :
    NodePrivateWrite.Writable (writePrivateDataState before owner identity value) owner identity value := by
  obtain ⟨fields, brand, field⟩ := writable.data
  exact ⟨writable.scope, writable.allocated, replacePrivateData identity value fields,
    replacePrivateOwner_found before.privates.elements owner identity value fields brand,
    replacePrivateData_found fields identity value (.data old) field⟩

theorem writable_init_frame (before after : State) (owner identity source empty target field : Nat) (old : Value)
    (contract : InitContract before after owner identity source empty) (writable : NodePrivateWrite.Writable before target field old) :
    NodePrivateWrite.Writable after target field old := by
  obtain ⟨object, found⟩ := writable.allocated
  exact ⟨by simpa [contract.privates] using writable.scope,
    ⟨object, (contract.oldObjects target (List.getElem?_eq_some_iff.mp found).1).trans found⟩,
    by simpa [contract.privates] using writable.data⟩

theorem startup_shared_inputs (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle empty : Nat) (old : Value) (path : JSString)
    (inputs : NodeSearchSetup.Inputs before methods functions closure owner identity handle empty old path)
    (sharedFound : ∃ shared, before.objects[empty]? = some shared) (rootFound : ∃ root, before.objects[0]? = some root) :
    HeaderInputs (nodeActivation (NodeSearchSetup.resultState before owner identity empty (NodeSearchSetup.producedParts path)) owner)
      owner identity empty empty := by
  have writable := writable_written before owner identity old (.object empty) inputs.writable
  refine ⟨rfl, ?_, sharedFound, ⟨writable.scope, writable.allocated, writable.data⟩, rootFound⟩
  simpa [nodeActivation, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup] using inputs.emptyBinding

/-- Actual startup resets private params to the actual shared module object.
The later exact123 activation derives the empty branch; no source-map copy
readiness, offset table or completed future initializer is assumed. -/
theorem startup_then_shared_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle empty : Nat) (old : Value) (path : JSString)
    (inputs : NodeSearchSetup.Inputs before methods functions closure owner identity handle empty old path)
    (sharedFound : ∃ shared, before.objects[empty]? = some shared) (rootFound : ∃ root, before.objects[0]? = some root) :
    let started := NodeSearchSetup.resultState before owner identity empty (NodeSearchSetup.producedParts path)
    let active := nodeActivation started owner
    (parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true).map
      (fun source => executeFunctionStatements 100 defaultSplitLimit methods functions source before) = some (.ok (.normal started)) ∧
    NodeSearchSetup.StartupContract before started owner identity empty old path (NodeSearchSetup.producedParts path) ∧
    sourceInit (extra + 16) active = some (.ok (emptyState active)) ∧ InitContract active (emptyState active) owner identity empty empty := by
  dsimp only
  obtain ⟨run, startup⟩ := NodeSearchSetup.startup_satisfies before methods functions closure owner identity handle empty old path inputs
  exact ⟨run, startup, source_shared_satisfies extra _ owner identity empty empty
    (startup_shared_inputs before methods functions closure owner identity handle empty old path inputs sharedFound rootFound) rfl⟩

def capturedObject (name captured : JSString) : OrdinaryObject := newDataObject emptyLiteralObject name (.string captured)
def capturedState (before : State) (name captured : JSString) : State :=
  {before with
    environment := ("params", .object before.objects.length) :: before.environment
    objects := before.objects ++ [capturedObject name captured]}

theorem captured_object_eligible (name captured : JSString) : EnumerableData (capturedObject name captured) := by
  have ready := newDataObject_spreadReady emptyLiteralObject name (.string captured) emptyLiteral_spreadReady
  refine ⟨newDataObject_wellFormed emptyLiteralObject name (.string captured) (by simp [WellFormedObject, emptyLiteralObject]), ?_⟩
  intro key descriptor found _
  obtain ⟨value, same⟩ := ready.ownData key descriptor found
  exact ⟨value, true, true, same⟩

theorem guard_written_eq (before : State) (name captured : JSString) :
    NodeCaptureGuard.writtenState (emptyState before) before.objects.length emptyLiteralObject name captured = capturedState before name captured := by
  simp [NodeCaptureGuard.writtenState, emptyState, capturedState, capturedObject, List.set_append_right]

/-- These before-state root descriptors and matched-array facts derive the
capture guard's readiness after exact123 creates ordinary params. -/
theorem guard_inputs (before : State) (owner identity empty : Nat) (name : JSString) (matched : Nat) (values : List Value)
    (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before owner identity empty empty) (standard : StandardObjectBinding before)
    (nameBinding : before.environment.lookup "name" = some (.string name))
    (matchedBinding : before.environment.lookup "m" = some (.array matched)) (matchedFound : before.heap[matched]? = some values)
    (capturedFound : values[0]? = some (.string captured)) (lengthBound : values.length ≤ maximumArrayLength)
    (rootPath : NodeCaptureGuard.DescriptorPath before.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel) :
    NodeCaptureGuard.AbsentInputs (emptyState before) before.objects.length emptyLiteralObject name matched values captured descriptor (depth + 1) := by
  obtain ⟨root, found⟩ := inputs.rootFound
  exact NodeCaptureGuard.literal_absent_inputs before root name matched values captured descriptor depth found standard nameBinding
    matchedBinding matchedFound capturedFound lengthBound rootPath pathBound

theorem captured_child_writable (before : State) (child identity : Nat) (old : Value) (name captured : JSString)
    (writable : NodePrivateWrite.Writable before child identity old) :
    NodePrivateWrite.Writable (capturedState before name captured) child identity old := by
  obtain ⟨object, found⟩ := writable.allocated
  exact ⟨writable.scope, ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩, writable.data⟩

def storedState (before : State) (child identity : Nat) (name captured : JSString) : State :=
  writePrivateDataState (capturedState before name captured) child identity (.object before.objects.length)

theorem stored_copy_inputs (before : State) (owner identity empty child : Nat) (old : Value) (name captured : JSString)
    (inputs : HeaderInputs before owner identity empty empty) (childWritable : NodePrivateWrite.Writable before child identity old) :
    CopyInputs (nodeActivation (storedState before child identity name captured) child) child identity before.objects.length empty (capturedObject name captured) := by
  have writable := writable_written (capturedState before name captured) child identity old (.object before.objects.length)
    (captured_child_writable before child identity old name captured childWritable)
  obtain ⟨shared, sharedFound⟩ := inputs.emptyFound
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  have sharedBound := (List.getElem?_eq_some_iff.mp sharedFound).1
  have rootBound := (List.getElem?_eq_some_iff.mp rootFound).1
  refine ⟨⟨rfl, ?_, ⟨shared, ?_⟩, ⟨writable.scope, writable.allocated, writable.data⟩, ⟨root, ?_⟩⟩,
    by omega, ?_, captured_object_eligible name captured⟩
  · simpa [nodeActivation, storedState, writePrivateDataState, capturedState, List.lookup] using inputs.emptyBinding
  · exact (List.getElem?_append_left sharedBound).trans sharedFound
  · exact (List.getElem?_append_left rootBound).trans rootFound
  · simp [nodeActivation, storedState, writePrivateDataState, capturedState]

/-- Four separate actual source activations:123 creates params,158–160 captures
an initial match string,202 stores the produced pointer, then a new node entry
runs123's nonshared arm. Child activation is restored before re-entry. Earlier
matcher.exec/search/pattern selection is not claimed by this protocol. -/
theorem init_capture_store_reinit_satisfies (extra : Nat) (before : State) (owner identity empty child : Nat) (old : Value)
    (name : JSString) (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before owner identity empty empty) (childWritable : NodePrivateWrite.Writable before child identity old)
    (standard : StandardObjectBinding before) (nameBinding : before.environment.lookup "name" = some (.string name))
    (matchedBinding : before.environment.lookup "m" = some (.array matched)) (matchedFound : before.heap[matched]? = some values)
    (capturedFound : values[0]? = some (.string captured)) (lengthBound : values.length ≤ maximumArrayLength)
    (rootPath : NodeCaptureGuard.DescriptorPath before.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel)
    (classified : NodeCaptureGuard.action descriptor true = .create) :
    let first := emptyState before
    let guarded := capturedState before name captured
    let stored := storedState before child identity name captured
    let active := nodeActivation stored child
    sourceInit (extra + 16) before = some (.ok first) ∧ InitContract before first owner identity empty empty ∧
    NodeCaptureGuard.sourceGuard (extra + 27) first = some (.ok (.normal guarded)) ∧
    NodeCaptureGuard.CreatedContract first guarded before.objects.length emptyLiteralObject name captured ∧
    (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
      (fun source => executeAssignment 32 defaultSplitLimit source (childActivation guarded child)) =
      some (.ok (.object before.objects.length, childActivation stored child)) ∧
    sourceInit (extra + (ownStringKeys (capturedObject name captured)).length + 16) active = some (.ok (copiedState active (capturedObject name captured))) ∧
    InitContract active (copiedState active (capturedObject name captured)) child identity before.objects.length empty := by
  dsimp only
  obtain ⟨initialRun, initialContract⟩ := source_shared_satisfies extra before owner identity empty empty inputs rfl
  have ready := guard_inputs before owner identity empty name matched values captured descriptor depth inputs standard nameBinding matchedBinding
    matchedFound capturedFound lengthBound rootPath pathBound
  obtain ⟨guardRun, guardContract, _⟩ := NodeCaptureGuard.source_created_satisfies extra (emptyState before) before.objects.length emptyLiteralObject
    name matched values captured descriptor (depth + 1) ready classified
  rw [guard_written_eq] at guardRun guardContract
  have writable := captured_child_writable before child identity old name captured childWritable
  have runWrite := NodePrivateWrite.run_parameter (childActivation (capturedState before name captured) child) child identity old
    (.object before.objects.length) ⟨writable.scope, writable.allocated, writable.data⟩ ⟨rfl, by simp [childActivation, capturedState, List.lookup]⟩
  have readyAgain := stored_copy_inputs before owner identity empty child old name captured inputs childWritable
  have copied := source_copy_satisfies extra _ child identity before.objects.length empty (capturedObject name captured) readyAgain
  refine ⟨initialRun, initialContract, guardRun, guardContract, ?_, copied⟩
  rw [NodePrivateWrite.parses_parameter, Option.map_some, runWrite]
  rfl

theorem enumerableData_newData (object : OrdinaryObject) (key : JSString) (value : Value)
    (eligible : EnumerableData object) : EnumerableData (newDataObject object key value) := by
  refine ⟨newDataObject_wellFormed object key value eligible.1, ?_⟩
  intro query descriptor found enumerable
  by_cases same : query = key
  · subst query
    rw [newDataObject, putOwn_self] at found
    exact ⟨value, true, true, (Option.some.inj found).symm⟩
  · rw [newDataObject, spread_putOwn_other key query _ _ same] at found
    exact eligible.2 query descriptor found enumerable

/-- Data-only readiness is preserved by every modeled successful guard path:
own-property skip, legacy setter no-op, and own data creation. Unsupported
callbacks/rejections do not masquerade as successful native executions. -/
theorem successful_guard_preserves_data (before after : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (eligible : EnumerableData object) (contract : NodeCaptureGuard.GuardContract before params object name (.ok (.normal after))) :
    ∃ target, after.objects[params]? = some target ∧ EnumerableData target := by
  cases contract with
  | skipped descriptor initial => exact ⟨object, initial.found, eligible⟩
  | created matched values captured descriptor depth initial classified changed result =>
    refine ⟨newDataObject object name (.string captured), ?_, enumerableData_newData object name (.string captured) eligible⟩
    rw [result.heap]
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp initial.found).1
  | ignored matched values captured descriptor depth initial classified => exact ⟨object, initial.found, eligible⟩

def mapState (before : State) (object : OrdinaryObject) : State :=
  {before with
    environment := ("params", .object before.objects.length) :: before.environment
    objects := before.objects ++ [object]}
def storedMapState (before : State) (child identity : Nat) (object : OrdinaryObject) : State :=
  writePrivateDataState (mapState before object) child identity (.object before.objects.length)

theorem empty_eligible : EnumerableData emptyLiteralObject := by
  refine ⟨by simp [WellFormedObject, emptyLiteralObject], ?_⟩
  intro key descriptor found _
  cases found

theorem copied_object_eligible (object : OrdinaryObject) : EnumerableData (copiedObject object) := by
  have ready := spreadFold_ready object (ownStringKeys object) emptyLiteralObject emptyLiteral_spreadReady
  refine ⟨spreadFold_wellFormed object (ownStringKeys object) emptyLiteralObject empty_eligible.1, ?_⟩
  intro key descriptor found _
  obtain ⟨value, same⟩ := ready.ownData key descriptor found
  exact ⟨value, true, true, same⟩

theorem map_child_writable (before : State) (child identity : Nat) (old : Value) (object : OrdinaryObject)
    (writable : NodePrivateWrite.Writable before child identity old) :
    NodePrivateWrite.Writable (mapState before object) child identity old := by
  obtain ⟨owner, found⟩ := writable.allocated
  exact ⟨writable.scope, ⟨owner, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩, writable.data⟩

/-- A proof helper for a produced map. Headline protocols derive its object and
eligibility from actual initializer/guard execution, never supply future clones. -/
theorem stored_map_inputs (before : State) (owner identity source empty child : Nat) (old : Value) (object : OrdinaryObject)
    (inputs : HeaderInputs before owner identity source empty) (childWritable : NodePrivateWrite.Writable before child identity old)
    (eligible : EnumerableData object) :
    CopyInputs (nodeActivation (storedMapState before child identity object) child) child identity before.objects.length empty object := by
  have writable := writable_written (mapState before object) child identity old (.object before.objects.length)
    (map_child_writable before child identity old object childWritable)
  obtain ⟨shared, sharedFound⟩ := inputs.emptyFound
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  have sharedBound := (List.getElem?_eq_some_iff.mp sharedFound).1
  have rootBound := (List.getElem?_eq_some_iff.mp rootFound).1
  refine ⟨⟨rfl, ?_, ⟨shared, ?_⟩, ⟨writable.scope, writable.allocated, writable.data⟩, ⟨root, ?_⟩⟩, by omega, ?_, eligible⟩
  · simpa [nodeActivation, storedMapState, writePrivateDataState, mapState, List.lookup] using inputs.emptyBinding
  · exact (List.getElem?_append_left sharedBound).trans sharedFound
  · exact (List.getElem?_append_left rootBound).trans rootFound
  · simp [nodeActivation, storedMapState, writePrivateDataState, mapState]

theorem store_map_then_reinit (extra : Nat) (before : State) (owner identity source empty child : Nat) (old : Value) (object : OrdinaryObject)
    (inputs : HeaderInputs before owner identity source empty) (childWritable : NodePrivateWrite.Writable before child identity old)
    (eligible : EnumerableData object) :
    let produced := mapState before object
    let stored := storedMapState before child identity object
    let active := nodeActivation stored child
    (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
      (fun source => executeAssignment 32 defaultSplitLimit source (childActivation produced child)) =
      some (.ok (.object before.objects.length, childActivation stored child)) ∧
    sourceInit (extra + (ownStringKeys object).length + 16) active = some (.ok (copiedState active object)) ∧
    InitContract active (copiedState active object) child identity before.objects.length empty := by
  dsimp only
  have writable := map_child_writable before child identity old object childWritable
  have written := NodePrivateWrite.run_parameter (childActivation (mapState before object) child) child identity old (.object before.objects.length)
    ⟨writable.scope, writable.allocated, writable.data⟩ ⟨rfl, by simp [childActivation, mapState, List.lookup]⟩
  have copied := source_copy_satisfies extra _ child identity before.objects.length empty object
    (stored_map_inputs before owner identity source empty child old object inputs childWritable eligible)
  refine ⟨?_, copied⟩
  rw [NodePrivateWrite.parses_parameter, Option.map_some, written]
  rfl

/-- The legacy string setter path creates no own capture. Nevertheless actual
202 stores this fresh empty map, so child re-entry takes the NONshared arm and
clones an empty object. The branch is derived from identity, not empty keys. -/
theorem init_ignore_store_reinit_satisfies (extra : Nat) (before : State) (owner identity empty child : Nat) (old : Value)
    (name : JSString) (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before owner identity empty empty) (childWritable : NodePrivateWrite.Writable before child identity old)
    (standard : StandardObjectBinding before) (nameBinding : before.environment.lookup "name" = some (.string name))
    (matchedBinding : before.environment.lookup "m" = some (.array matched)) (matchedFound : before.heap[matched]? = some values)
    (capturedFound : values[0]? = some (.string captured)) (lengthBound : values.length ≤ maximumArrayLength)
    (rootPath : NodeCaptureGuard.DescriptorPath before.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel)
    (classified : NodeCaptureGuard.action descriptor true = .ignore) :
    let first := emptyState before
    let stored := storedMapState before child identity emptyLiteralObject
    let active := nodeActivation stored child
    sourceInit (extra + 16) before = some (.ok first) ∧ InitContract before first owner identity empty empty ∧
    NodeCaptureGuard.sourceGuard (extra + 27) first = some (.ok (.normal first)) ∧
    NodeCaptureGuard.GuardContract first before.objects.length emptyLiteralObject name (.ok (.normal first)) ∧
    (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
      (fun source => executeAssignment 32 defaultSplitLimit source (childActivation first child)) =
      some (.ok (.object before.objects.length, childActivation stored child)) ∧
    sourceInit (extra + (ownStringKeys emptyLiteralObject).length + 16) active = some (.ok (copiedState active emptyLiteralObject)) ∧
    InitContract active (copiedState active emptyLiteralObject) child identity before.objects.length empty := by
  dsimp only
  have initial := source_shared_satisfies extra before owner identity empty empty inputs rfl
  have ready := guard_inputs before owner identity empty name matched values captured descriptor depth inputs standard nameBinding matchedBinding
    matchedFound capturedFound lengthBound rootPath pathBound
  have ignored := NodeCaptureGuard.source_ignored_satisfies extra _ before.objects.length emptyLiteralObject name matched values captured descriptor (depth + 1) ready classified
  have rest := store_map_then_reinit extra before owner identity empty empty child old emptyLiteralObject inputs childWritable empty_eligible
  exact ⟨initial.1, initial.2, ignored.1, ignored.2, rest⟩

/-- A before-state own enumerable field is copied by actual123, then suppresses
the entire guard assignment. There is deliberately NO m/captured-string input;
202 stores that produced map and child re-entry derives another real clone. -/
theorem init_owned_store_reinit_satisfies (extra : Nat) (before : State) (owner identity source empty child : Nat) (old : Value)
    (object : OrdinaryObject) (name : JSString) (value : Value) (writable configurable : Bool)
    (inputs : CopyInputs before owner identity source empty object) (childWritable : NodePrivateWrite.Writable before child identity old)
    (standard : StandardObjectBinding before) (nameBinding : before.environment.lookup "name" = some (.string name))
    (field : object.own.lookup name = some (.data value writable true configurable)) :
    let first := copiedState before object
    let stored := storedMapState before child identity (copiedObject object)
    let active := nodeActivation stored child
    sourceInit (extra + (ownStringKeys object).length + 16) before = some (.ok first) ∧ InitContract before first owner identity source empty ∧
    NodeCaptureGuard.sourceGuard (extra + 32) first = some (.ok (.normal first)) ∧
    NodeCaptureGuard.GuardContract first before.objects.length (copiedObject object) name (.ok (.normal first)) ∧
    (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
      (fun source => executeAssignment 32 defaultSplitLimit source (childActivation first child)) =
      some (.ok (.object before.objects.length, childActivation stored child)) ∧
    sourceInit (extra + (ownStringKeys (copiedObject object)).length + 16) active = some (.ok (copiedState active (copiedObject object))) ∧
    InitContract active (copiedState active (copiedObject object)) child identity before.objects.length empty := by
  dsimp only
  have initial := source_copy_satisfies extra before owner identity source empty object inputs
  have copiedField : (copiedObject object).own.lookup name = some (.data value true true true) := by
    unfold copiedObject
    rw [spreadFold_all_keys object _ (ownStringKeys_order object inputs.eligible.1)]
    simp [copiedDescriptor, spreadValue, field]
  have ownedInputs : NodeCaptureGuard.OwnInputs (copiedState before object) before.objects.length (copiedObject object) name (.data value true true true) := by
    refine ⟨⟨?_, rfl, ?_, by simp [copiedState], (copied_object_eligible object).1⟩, copiedField⟩
    · simpa [StandardObjectBinding, copiedState, List.lookup] using standard
    · simpa [copiedState, List.lookup] using nameBinding
  have owned := NodeCaptureGuard.source_owned_satisfies extra _ before.objects.length (copiedObject object) name _ ownedInputs
  have rest := store_map_then_reinit extra before owner identity source empty child old (copiedObject object) inputs.toHeaderInputs childWritable (copied_object_eligible object)
  exact ⟨initial.1, initial.2, owned.1, owned.2, rest⟩

/-- info: 'HonoLean.Upstream.NodeParamsInit.startup_then_shared_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms startup_then_shared_satisfies
/-- info: 'HonoLean.Upstream.NodeParamsInit.init_capture_store_reinit_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms init_capture_store_reinit_satisfies
/-- info: 'HonoLean.Upstream.NodeParamsInit.init_ignore_store_reinit_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms init_ignore_store_reinit_satisfies
/-- info: 'HonoLean.Upstream.NodeParamsInit.init_owned_store_reinit_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms init_owned_store_reinit_satisfies
/-- info: 'HonoLean.Upstream.NodeParamsInit.successful_guard_preserves_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful_guard_preserves_data

end HonoLean.Upstream.NodeParamsInit
