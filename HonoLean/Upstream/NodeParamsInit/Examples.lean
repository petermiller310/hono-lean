import HonoLean.Upstream.NodeParamsInit.Composition
import HonoLean.Upstream.NodeClass.History

set_option autoImplicit false
namespace HonoLean.Upstream.NodeParamsInit.Examples
open SourceSubset ECMA2025

private def idKey : JSString := [105, 100]
private def hiddenKey : JSString := [104]
private def getterKey : JSString := [103]
private def selfKey : JSString := [115]
private def arrayKey : JSString := [97]
private def inheritedKey : JSString := [112]
private def payload : OrdinaryObject :=
  ⟨[(idKey, .data (.string [945]) false true false),
    (protoKey, .data (.object 4) false true false),
    (hiddenKey, .data (.number 7) true false true),
    (getterKey, .accessor .unsupported .unsupported false true),
    (selfKey, .data (.object 3) true true true),
    (arrayKey, .data (.array 0) true true true)], some 4, false⟩
private def sharedGetter : OrdinaryObject :=
  ⟨[(getterKey, .accessor .unsupported .unsupported true true)], none, true⟩

/-- Allocated ordinary/private fixtures are supplied initial inputs, not a
claim of whole Node.insert or source123 reachability. All alias refs are old. -/
private def fixture (source : Nat) (shared object : OrdinaryObject) : State :=
  {environment := [("node", .object 2), ("emptyParams", .object 1), ("params", .object 4), ("frame", .number 91)]
   objects := [objectPrototypeProjection [], shared, emptyLiteralObject, object,
     ⟨[(inheritedKey, .data (.string [118]) true true true)], some 0, true⟩]
   heap := [[.array 0, .object 3]]
   privates := PrivateStore.ofData [("params", 5), ("other", 8)] [(2, [(5, .object source), (8, .array 0)])]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   sets := [[idKey]]
   thisValue := .object 2}

private theorem fixture_header (source : Nat) (shared object : OrdinaryObject) :
    HeaderInputs (fixture source shared object) 2 5 source 1 := by
  exact ⟨rfl, rfl, ⟨shared, rfl⟩,
    ⟨rfl, ⟨emptyLiteralObject, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩, ⟨objectPrototypeProjection [], rfl⟩⟩

private theorem payload_eligible : EnumerableData payload := by
  refine enumerableData_of_ready payload ?_ ?_
  · change ([idKey, protoKey, hiddenKey, getterKey, selfKey, arrayKey] : List JSString).Nodup
    decide
  · intro key getter setter configurable found
    simp only [payload, List.lookup_cons] at found
    repeat' (split at found <;> simp_all)

private theorem fixture_copy (object : OrdinaryObject) (eligible : EnumerableData object) :
    CopyInputs (fixture 3 emptyNullObject object) 2 5 3 1 object :=
  ⟨fixture_header 3 emptyNullObject object, by decide, rfl, eligible⟩

private def targetObject (after : State) : Except EvalError OrdinaryObject := do
  let reference ← match ← lookupVariable after "params" with | .object reference => pure reference | _ => throw .unsupported
  match after.objects[reference]? with | some object => pure object | none => throw .invalidReference

private def observation (before : State) : Option (Except EvalError (List (Option PropertyDescriptor) × Option Nat × Bool × Value × Bool)) := do
  let result ← sourceInit 200 before
  pure do
    let after ← result
    let target ← targetObject after
    let fields := [idKey, protoKey, hiddenKey, getterKey, selfKey, arrayKey, inheritedKey].map (fun key => target.own.lookup key)
    let original ← privateGet (.object 2) "params" after
    pure (fields, target.prototype, target.extensible, original,
      decide (after.objects.take before.objects.length = before.objects ∧ after.objects.length = before.objects.length + 1 ∧
        after.heap = before.heap ∧ after.privates = before.privates ∧ after.functions.length = before.functions.length ∧
        after.sets = before.sets ∧ after.thisValue = before.thisValue ∧ after.environment.tail = before.environment))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem shared_identity_skips_even_enumerable_getters :
    observation (fixture 1 sharedGetter payload) =
      some (.ok ([none, none, none, none, none, none, none], some 0, true, .object 1, true)) := by
  have run := (source_shared_satisfies 184 _ 2 5 1 1 (fixture_header 1 sharedGetter payload) rfl).1
  simp only [observation, run]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem copy_is_own_enumerable_data_with_shallow_aliases :
    observation (fixture 3 emptyNullObject payload) = some (.ok (
      [some (.data (.string [945]) true true true), some (.data (.object 4) true true true), none, none,
       some (.data (.object 3) true true true), some (.data (.array 0) true true true), none],
      some 0, true, .object 3, true)) := by
  have run := (source_copy_satisfies 178 _ 2 5 3 1 payload (fixture_copy payload payload_eligible)).1
  change sourceInit 200 _ = _ at run
  simp only [observation, run]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem nonshared_empty_object_still_takes_copy_arm :
    observation (fixture 3 emptyNullObject emptyNullObject) =
      some (.ok ([none, none, none, none, none, none, none], some 0, true, .object 3, true)) := by
  have eligible : EnumerableData emptyNullObject := by simp [EnumerableData, WellFormedObject, emptyNullObject]
  have run := (source_copy_satisfies 184 _ 2 5 3 1 emptyNullObject (fixture_copy emptyNullObject eligible)).1
  change sourceInit 200 _ = _ at run
  simp only [observation, run]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem enumerable_getter_in_copy_arm_is_model_unsupported :
    sourceInit 200 (fixture 3 emptyNullObject sharedGetter) = some (.error .unsupported) := by
  simp only [sourceInit, parses_source]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem node_can_also_be_the_source_object :
    let before := fixture 2 emptyNullObject payload
    let before := {before with objects := before.objects.set 2 (newDataObject emptyLiteralObject selfKey (.object 2))}
    observation before = some (.ok ([none, none, none, none, some (.data (.object 2) true true true), none, none], some 0, true, .object 2, true)) := by
  let object := newDataObject emptyLiteralObject selfKey (.object 2)
  let initial := fixture 2 emptyNullObject payload
  let before := {initial with objects := initial.objects.set 2 object}
  have inputs : CopyInputs before 2 5 2 1 object := by
    refine ⟨⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, ⟨rfl, ⟨object, rfl⟩, ?_⟩, ⟨objectPrototypeProjection [], rfl⟩⟩,
      by decide, rfl, enumerableData_newData emptyLiteralObject selfKey (.object 2) empty_eligible⟩
    refine ⟨_, rfl, ?_⟩
    rfl
  have run := (source_copy_satisfies 183 before 2 5 2 1 object inputs).1
  change sourceInit 200 before = _ at run
  change observation before = _
  simp only [observation, run]
  cbv

/-- The shared source's descriptors are never an eligibility premise. -/
theorem shared_domain_has_universal_contract :
    let before := fixture 1 sharedGetter payload
    sourceInit 16 before = some (.ok (emptyState before)) ∧ InitContract before (emptyState before) 2 5 1 1 := by
  exact source_shared_satisfies 0 _ 2 5 1 1 (fixture_header 1 sharedGetter payload) rfl

set_option maxRecDepth 65536 in
theorem copy_domain_has_universal_contract :
    let before := fixture 3 emptyNullObject payload
    sourceInit ((ownStringKeys payload).length + 16) before = some (.ok (copiedState before payload)) ∧
      InitContract before (copiedState before payload) 2 5 3 1 := by
  exact source_copy_satisfies 0 _ 2 5 3 1 payload (fixture_copy payload payload_eligible)

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

private def classBefore : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection []]
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def moduleState : State := NodeInitialization.preambleState classBefore
private def definition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def methods : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def instanceState : State := NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 1)
private def initialized : State := NodeClass.classActivation instanceState 1
private def requests : List RegistrationHistory.Request := [⟨[71, 69, 84], .number 10, []⟩]
private def registered : State := RegistrationHistory.endState initialized 2 0 0 [] requests
private def matchSource : String := "const m = [capture]\n"
private def matchProgram : List Stmt := [.declare "m" (.arrayLiteral [(false, .variable "capture")])]
private def sourceClosure : StringFunctionClosure := ⟨splitPathProgram, moduleState.environment, []⟩
private def sourceFunctions : FunctionTable := ⟨2, [sourceClosure]⟩
private def matchEntry (name captured : JSString) : State :=
  {registered with
    thisValue := .object 2
    environment := [("splitPath", .function 2), ("path", .string [120]), ("name", .string name), ("capture", .string captured)] ++ registered.environment}
private def sourcePreparedState (name captured : JSString) : State :=
  {matchEntry name captured with
    environment := ("m", .array registered.heap.length) :: (matchEntry name captured).environment
    heap := registered.heap ++ [[.string captured]]}

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod) (push : Expr)
    (matchInit : List Stmt) (split : Function) (name captured : JSString) : Except EvalError State := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry classBefore))
  let (selected, _, methodTable) ← match definePrivateClass fields [method] module (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some selected => pure selected
    | none => throw .unsupported
  let (owner, one) ← instantiatePrivateClass 64 defaultSplitLimit selected (some 0) module
  let active := {one with privates := {one.privates with names := selected.names}}
  let history ← RegistrationHistory.runSourceHistory push owner requests active
  let closure : StringFunctionClosure := ⟨split, module.environment, []⟩
  let functions : FunctionTable := ⟨methodTable.base + methodTable.entries.length, [closure]⟩
  normalState (← execute 32 defaultSplitLimit matchInit
    {history with
      thisValue := .object owner
      environment := [("splitPath", .function functions.base), ("path", .string [120]), ("name", .string name), ("capture", .string captured)] ++ history.environment})

/-- Actual Node preamble/class installation/constructor/source push and parsed
imported splitPath closure. Parsed `m=[capture]` remains an explicit fixture
boundary, not matcher.exec156; actual startup is proved separately below. -/
private def sourcePrepare (name captured : JSString) : Option (Except EvalError State) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let matchInit ← parseBlock matchSource ["capture"]
  let split ← parse SourceSubset.pinnedSource
  pure (prepareCore preamble fields method push matchInit split name captured)

private theorem parses_match : parseBlock matchSource ["capture"] = some matchProgram := by cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem source_prepared (name captured : JSString) : sourcePrepare name captured = some (.ok (sourcePreparedState name captured)) := by
  have preamble := NodeInitialization.run_preamble classBefore ⟨0, [], rfl, rfl, Or.inl rfl⟩
  have selected : definePrivateClass NodeClass.fieldsProgram [NodePrivateCall.methodProgram] moduleState
      (initialPrivateClassWorld moduleState ⟨1, []⟩) ⟨1, []⟩ = some (definition, ⟨7⟩, methods) :=
    NodeClass.define_node moduleState ⟨1⟩ ⟨1, []⟩ (by decide)
  have instanceRun : instantiatePrivateClass 64 defaultSplitLimit definition (some 0) moduleState = .ok (2, instanceState) :=
    NodeClass.instantiate_node moduleState (some 0) moduleState.environment 1 1 (.object 1) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have seed : RegistrationHistory.Seed initialized 2 1 0 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have history := RegistrationHistory.run_source_history initialized 2 1 0 0 [] requests seed
  dsimp only [moduleState] at selected instanceRun
  simp only [sourcePrepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, parses_match, SourceSubset.parses_pinned_source]
  dsimp only [bind, Option.bind, pure]
  unfold prepareCore
  rw [preamble]
  dsimp only [bind, Except.bind, pure, Except.pure, normalState]
  rw [selected]
  dsimp only
  rw [instanceRun]
  dsimp only
  change RegistrationHistory.runSourceHistory NodeMethodsPush.expression 2 requests
    {instanceState with privates := {instanceState.privates with names := definition.names}} = .ok registered at history
  rw [history]
  cbv

set_option maxRecDepth 65536 in
private theorem startup_inputs (name captured : JSString) :
    NodeSearchSetup.Inputs (sourcePreparedState name captured) methods sourceFunctions sourceClosure 2 5 2 1 (.object 1) [120] := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, by decide, by decide, rfl⟩
  · exact ⟨rfl, ⟨emptyLiteralObject, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  · change (1 : Nat) ≤ 1
    decide

private def sourceStarted (name captured : JSString) : State :=
  NodeSearchSetup.resultState (sourcePreparedState name captured) 2 5 1 (NodeSearchSetup.producedParts [120])
private def sourceActive (name captured : JSString) : State := nodeActivation (sourceStarted name captured) 2

set_option maxRecDepth 65536 in
private theorem active_inputs (name captured : JSString) : HeaderInputs (sourceActive name captured) 2 5 1 1 :=
  startup_shared_inputs (sourcePreparedState name captured) methods sourceFunctions sourceClosure 2 5 2 1 (.object 1) [120]
    (startup_inputs name captured) ⟨emptyNullObject, rfl⟩ ⟨objectPrototypeProjection [], rfl⟩

set_option maxRecDepth 65536 in
private theorem active_created_protocol (captured : JSString) :
    let before := sourceActive idKey captured
    let produced := emptyState before
    let guarded := capturedState before idKey captured
    let stored := storedState before 2 5 idKey captured
    let active := nodeActivation stored 2
    sourceInit 16 before = some (.ok produced) ∧ InitContract before produced 2 5 1 1 ∧
    NodeCaptureGuard.sourceGuard 27 produced = some (.ok (.normal guarded)) ∧
    NodeCaptureGuard.CreatedContract produced guarded before.objects.length emptyLiteralObject idKey captured ∧
    (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
      (fun source => executeAssignment 32 defaultSplitLimit source (childActivation guarded 2)) =
      some (.ok (.object before.objects.length, childActivation stored 2)) ∧
    sourceInit ((ownStringKeys (capturedObject idKey captured)).length + 16) active = some (.ok (copiedState active (capturedObject idKey captured))) ∧
    InitContract active (copiedState active (capturedObject idKey captured)) 2 5 before.objects.length 1 := by
  let before := sourceActive idKey captured
  have header := active_inputs idKey captured
  have rootPath : NodeCaptureGuard.DescriptorPath before.objects idKey 0 none 1 := .absent (object := objectPrototypeProjection []) rfl (by decide) rfl
  simpa only [Nat.zero_add] using init_capture_store_reinit_satisfies 0 before 2 5 1 2 (.object 1) idKey 3 [.string captured] captured none 1
    header header.writable (Or.inl rfl) rfl rfl rfl rfl (by change 1 ≤ 4294967295; decide) rootPath (by decide) rfl

set_option maxRecDepth 65536 in
/-- Actual source installation/registration/startup derive the shared arm.
The produced captured map is written by exact202 and cloned at child re-entry;
only m production and the omitted control-flow activations remain fixtures. -/
theorem source_prepared_created_capture_protocol (captured : JSString) :
    ∃ ready,
      sourcePrepare idKey captured = some (.ok ready) ∧
      (parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true).map
        (fun source => executeFunctionStatements 100 defaultSplitLimit methods sourceFunctions source ready) =
        some (.ok (.normal (sourceStarted idKey captured))) ∧
      let before := sourceActive idKey captured
      let stored := storedState before 2 5 idKey captured
      let active := nodeActivation stored 2
      sourceInit 16 before = some (.ok (emptyState before)) ∧
      NodeCaptureGuard.sourceGuard 27 (emptyState before) = some (.ok (.normal (capturedState before idKey captured))) ∧
      (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
        (fun source => executeAssignment 32 defaultSplitLimit source (childActivation (capturedState before idKey captured) 2)) =
        some (.ok (.object before.objects.length, childActivation stored 2)) ∧
      sourceInit ((ownStringKeys (capturedObject idKey captured)).length + 16) active = some (.ok (copiedState active (capturedObject idKey captured))) ∧
      InitContract active (copiedState active (capturedObject idKey captured)) 2 5 before.objects.length 1 := by
  have started := (NodeSearchSetup.startup_satisfies (sourcePreparedState idKey captured) methods sourceFunctions sourceClosure 2 5 2 1 (.object 1) [120] (startup_inputs idKey captured)).1
  have chain := active_created_protocol captured
  exact ⟨sourcePreparedState idKey captured, source_prepared idKey captured, started, chain.1, chain.2.2.1,
    chain.2.2.2.2.1, chain.2.2.2.2.2⟩

set_option maxRecDepth 65536 in
/-- Real source reset/init, string __proto__ no-op, actual202, then a nonshared
EMPTY clone. Identical empty own maps do not imply shared object identity. -/
theorem source_prepared_legacy_ignore_protocol (captured : JSString) :
    ∃ ready,
      sourcePrepare protoKey captured = some (.ok ready) ∧
      (parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true).map
        (fun source => executeFunctionStatements 100 defaultSplitLimit methods sourceFunctions source ready) =
        some (.ok (.normal (sourceStarted protoKey captured))) ∧
      let before := sourceActive protoKey captured
      let stored := storedMapState before 2 5 emptyLiteralObject
      let active := nodeActivation stored 2
      sourceInit 16 before = some (.ok (emptyState before)) ∧
      NodeCaptureGuard.sourceGuard 27 (emptyState before) = some (.ok (.normal (emptyState before))) ∧
      (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
        (fun source => executeAssignment 32 defaultSplitLimit source (childActivation (emptyState before) 2)) =
        some (.ok (.object before.objects.length, childActivation stored 2)) ∧
      sourceInit 16 active = some (.ok (copiedState active emptyLiteralObject)) ∧
      InitContract active (copiedState active emptyLiteralObject) 2 5 before.objects.length 1 := by
  let before := sourceActive protoKey captured
  have header := active_inputs protoKey captured
  have rootPath : NodeCaptureGuard.DescriptorPath before.objects protoKey 0
      (some (.accessor .prototype .prototype false true)) 1 := .own (object := objectPrototypeProjection []) rfl rfl
  have chain := init_ignore_store_reinit_satisfies 0 before 2 5 1 2 (.object 1) protoKey 3 [.string captured] captured _ 1
    header header.writable (Or.inl rfl) rfl rfl rfl rfl (by change 1 ≤ 4294967295; decide) rootPath (by decide) rfl
  have started := (NodeSearchSetup.startup_satisfies (sourcePreparedState protoKey captured) methods sourceFunctions sourceClosure 2 5 2 1 (.object 1) [120] (startup_inputs protoKey captured)).1
  exact ⟨sourcePreparedState protoKey captured, source_prepared protoKey captured, started, chain.1, chain.2.2.1,
    chain.2.2.2.2.1, chain.2.2.2.2.2⟩

private def withoutMatch (state : State) : State := {state with environment := withoutBindings state.environment ["m"]}

private theorem copy_inputs_without_match (before : State) (owner identity source empty : Nat) (object : OrdinaryObject)
    (inputs : CopyInputs before owner identity source empty object) : CopyInputs (withoutMatch before) owner identity source empty object := by
  refine ⟨⟨?_, ?_, inputs.emptyFound, ⟨inputs.writable.scope, inputs.writable.allocated, inputs.writable.data⟩, inputs.rootFound⟩,
    inputs.different, inputs.sourceFound, inputs.eligible⟩
  · exact (lookup_withoutBindings _ _ "node" (by decide)).trans inputs.nodeBinding
  · exact (lookup_withoutBindings _ _ "emptyParams" (by decide)).trans inputs.emptyBinding

set_option maxRecDepth 65536 in
/-- Previous actual capture/202 supply the source map. A separate caller
activation removes m; both subsequent123 and own-field guard still run, then
actual202 and another123 propagate the produced-map invariant. -/
theorem source_prepared_owned_skip_without_match (captured : JSString) :
    ∃ ready,
      sourcePrepare idKey captured = some (.ok ready) ∧
      (parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true).map
        (fun source => executeFunctionStatements 100 defaultSplitLimit methods sourceFunctions source ready) =
        some (.ok (.normal (sourceStarted idKey captured))) ∧
      let before := sourceActive idKey captured
      let stored := storedState before 2 5 idKey captured
      let active := withoutMatch (nodeActivation stored 2)
      let first := copiedState active (capturedObject idKey captured)
      let storedAgain := storedMapState active 2 5 (copiedObject (capturedObject idKey captured))
      let entered := nodeActivation storedAgain 2
      active.environment.lookup "m" = none ∧
      sourceInit 16 before = some (.ok (emptyState before)) ∧
      NodeCaptureGuard.sourceGuard 27 (emptyState before) = some (.ok (.normal (capturedState before idKey captured))) ∧
      (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
        (fun source => executeAssignment 32 defaultSplitLimit source (childActivation (capturedState before idKey captured) 2)) =
        some (.ok (.object before.objects.length, childActivation stored 2)) ∧
      sourceInit ((ownStringKeys (capturedObject idKey captured)).length + 16) active = some (.ok first) ∧
      NodeCaptureGuard.sourceGuard 32 first = some (.ok (.normal first)) ∧
      (parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames).map
        (fun source => executeAssignment 32 defaultSplitLimit source (childActivation first 2)) =
        some (.ok (.object active.objects.length, childActivation storedAgain 2)) ∧
      sourceInit ((ownStringKeys (copiedObject (capturedObject idKey captured))).length + 16) entered =
        some (.ok (copiedState entered (copiedObject (capturedObject idKey captured)))) ∧
      InitContract entered (copiedState entered (copiedObject (capturedObject idKey captured))) 2 5 active.objects.length 1 := by
  let before := sourceActive idKey captured
  let stored := storedState before 2 5 idKey captured
  let active := withoutMatch (nodeActivation stored 2)
  have header := active_inputs idKey captured
  have earlier := active_created_protocol captured
  have initial := stored_copy_inputs before 2 5 1 2 (.object 1) idKey captured header header.writable
  have ready := copy_inputs_without_match _ 2 5 before.objects.length 1 _ initial
  have writable := ready.writable
  have standard : StandardObjectBinding active := Or.inl rfl
  have named : active.environment.lookup "name" = some (.string idKey) := by rfl
  have own : (capturedObject idKey captured).own.lookup idKey = some (.data (.string captured) true true true) := by
    simp [capturedObject, newDataObject, putOwn_self]
  have later := init_owned_store_reinit_satisfies 0 active 2 5 before.objects.length 1 2 (.object before.objects.length)
    (capturedObject idKey captured) idKey (.string captured) true true ready writable standard named own
  simp only [Nat.zero_add] at later
  have started := (NodeSearchSetup.startup_satisfies (sourcePreparedState idKey captured) methods sourceFunctions sourceClosure 2 5 2 1 (.object 1) [120] (startup_inputs idKey captured)).1
  exact ⟨sourcePreparedState idKey captured, source_prepared idKey captured, started, rfl, earlier.1, earlier.2.2.1,
    earlier.2.2.2.2.1, later.1, later.2.2.1, later.2.2.2.2.1, later.2.2.2.2.2⟩

/-- info: 'HonoLean.Upstream.NodeParamsInit.Examples.source_prepared_created_capture_protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_prepared_created_capture_protocol
/-- info: 'HonoLean.Upstream.NodeParamsInit.Examples.source_prepared_legacy_ignore_protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_prepared_legacy_ignore_protocol
/-- info: 'HonoLean.Upstream.NodeParamsInit.Examples.source_prepared_owned_skip_without_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_prepared_owned_skip_without_match

end HonoLean.Upstream.NodeParamsInit.Examples
