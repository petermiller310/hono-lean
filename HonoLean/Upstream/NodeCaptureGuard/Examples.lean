import HonoLean.Upstream.NodeCaptureGuard.Composition
import HonoLean.Upstream.NodeClass.History

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureGuard.Examples
open SourceSubset ECMA2025

private def ownFixture (name : JSString) (descriptor : PropertyDescriptor) : State :=
  {environment := [("params", .object 1), ("name", .string name)]
   objects := [objectPrototypeProjection [], ⟨[(name, descriptor)], some 0, false⟩]
   thisValue := .object 1}

/-- Every actual own descriptor suppresses the assignment. The matched-array
binding is absent; even unsupported getters/setters and readonly data skip. -/
theorem any_own_descriptor_skips_without_match (name : JSString) (descriptor : PropertyDescriptor) :
    sourceGuard 32 (ownFixture name descriptor) = some (.ok (.normal (ownFixture name descriptor))) ∧
    GuardContract (ownFixture name descriptor) 1 ⟨[(name, descriptor)], some 0, false⟩ name (.ok (.normal (ownFixture name descriptor))) := by
  refine source_owned_satisfies 0 _ _ _ _ descriptor ?_
  exact ⟨⟨Or.inl rfl, rfl, rfl, rfl, by simp [WellFormedObject]⟩, by simp⟩

private def realmFixture (name captured : JSString) (parent : OrdinaryObject) (extensible : Bool := true) : State :=
  {environment := [("params", .object 1), ("name", .string name), ("m", .array 0), ("frame", .number 41)]
   objects := [parent, ⟨[], some 0, extensible⟩]
   heap := [[.string captured], [.array 0, .object 1]]
   privates := PrivateStore.ofData [("params", 77)] [(1, [(77, .object 1)])]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   sets := [[name]]
   thisValue := .object 1}

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

private def observations (before : State) (params : Nat) (name : JSString) : Option (Except EvalError (Bool × Value × Bool)) := do
  let outcome ← sourceGuard 100 before
  pure do
    let after ← normalState (← outcome)
    let owned ← (hasOwn after.objects params name).mapError .objectError
    let value ← (getProperty propertyFuel after.objects params name).mapError .objectError
    pure (owned, value, decide (after.environment = before.environment ∧ after.heap = before.heap ∧
      after.privates.names = before.privates.names ∧ after.privates.elements = before.privates.elements ∧ after.functions.length = before.functions.length ∧ after.sets = before.sets ∧ after.thisValue = before.thisValue))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem ordinary_proto_constructor_and_utf16_capture :
    observations (realmFixture protoKey [97] (objectPrototypeProjection [])) 1 protoKey = some (.ok (false, .object 0, true)) ∧
    observations (realmFixture constructorKey [55296, 56320] (objectPrototypeProjection [])) 1 constructorKey =
      some (.ok (true, .string [55296, 56320], true)) ∧
    observations (realmFixture [] [] (objectPrototypeProjection [])) 1 [] = some (.ok (true, .string [], true)) := by
  repeat' constructor
  all_goals simp only [observations, sourceGuard, parses_source]; cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem inherited_writable_flags_do_not_become_own_flags :
    observations (realmFixture idKey [120] ⟨[(idKey, .data (.number 7) true false false)], none, true⟩) 1 idKey =
      some (.ok (true, .string [120], true)) ∧
    (sourceGuard 100 (realmFixture idKey [120] ⟨[(idKey, .data (.number 7) true false false)], none, true⟩)).map
      (fun outcome => outcome.map (fun completion => match completion with
        | .normal after => (after.objects[1]?).map (fun object => object.own.lookup idKey)
        | _ => none)) = some (.ok (some (some (.data (.string [120]) true true true)))) := by
  constructor <;> simp only [observations, sourceGuard, parses_source] <;> cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem nonextensible_prototype_setter_and_irrelevant_getter :
    sourceGuard 100 (realmFixture idKey [120] ⟨[(idKey, .accessor .unsupported .prototype true true)], none, true⟩ false) =
      some (.ok (.normal (realmFixture idKey [120] ⟨[(idKey, .accessor .unsupported .prototype true true)], none, true⟩ false))) := by
  simp only [sourceGuard, parses_source]
  cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem readonly_missing_setter_and_nonextensible_rejections :
    sourceGuard 100 (realmFixture idKey [120] ⟨[(idKey, .data (.number 7) false true true)], none, true⟩) =
      some (.error (.objectError .notWritable)) ∧
    sourceGuard 100 (realmFixture idKey [120] ⟨[(idKey, .accessor .unsupported .missing false true)], none, true⟩) =
      some (.error (.objectError .notWritable)) ∧
    sourceGuard 100 (realmFixture idKey [120] emptyNullObject false) = some (.error (.objectError .notExtensible)) := by
  repeat' constructor
  all_goals simp only [sourceGuard, parses_source]; cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem match_read_errors_precede_set_rejection :
    let before := realmFixture idKey [120] ⟨[(idKey, .data (.number 7) false true true)], none, true⟩
    sourceGuard 100 {before with environment := [("params", .object 1), ("name", .string idKey)]} = some (.error .missingVariable) ∧
    sourceGuard 100 {before with environment := [("params", .object 1), ("name", .string idKey), ("m", .array 99)]} = some (.error .invalidReference) := by
  constructor <;> simp only [sourceGuard, parses_source] <;> cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem null_prototype_control_really_creates_proto_data :
    let before : State := {
      environment := [("params", .object 0), ("name", .string protoKey), ("m", .array 0)]
      objects := [emptyNullObject]
      heap := [[.string [945]]]}
    observations before 0 protoKey = some (.ok (true, .string [945], true)) := by
  simp only [observations, sourceGuard, parses_source]
  cbv

/-- A genuinely initial structural domain: m and the params object's private
owner/value aliases are already allocated. The universal source theorem, not a
closed evaluator result, establishes creation and all frame observations. -/
theorem inherited_domain_has_universal_contract :
    let before := realmFixture idKey [55296] ⟨[(idKey, .data (.number 7) true false false)], none, true⟩
    ∃ after, sourceGuard 27 before = some (.ok (.normal after)) ∧
      CreatedContract before after 1 ⟨[], some 0, true⟩ idKey [55296] ∧
      GuardContract before 1 ⟨[], some 0, true⟩ idKey (.ok (.normal after)) := by
  let before := realmFixture idKey [55296] ⟨[(idKey, .data (.number 7) true false false)], none, true⟩
  have inputs : AbsentInputs before 1 ⟨[], some 0, true⟩ idKey 0 [.string [55296]] [55296]
      (some (.data (.number 7) true false false)) 2 := by
    refine ⟨⟨Or.inl rfl, rfl, rfl, rfl, by simp [WellFormedObject]⟩, rfl, rfl, rfl, rfl, by decide,
      .parent rfl rfl rfl (.own rfl rfl), by decide⟩
  obtain ⟨run, contract, related⟩ := source_created_satisfies 0 before 1 ⟨[], some 0, true⟩ idKey 0 _ [55296] _ 2 inputs rfl
  exact ⟨_, run, contract, related⟩

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
private def matchEntry (name captured : JSString) : State :=
  {registered with environment := [("name", .string name), ("capture", .string captured)] ++ registered.environment}
private def sourcePreparedState (name captured : JSString) : State :=
  {matchEntry name captured with
    environment := ("m", .array registered.heap.length) :: (matchEntry name captured).environment
    heap := registered.heap ++ [[.string captured]]}

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod) (push : Expr)
    (matchInit : List Stmt) (name captured : JSString) : Except EvalError State := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry classBefore))
  let (selected, _, _) ← match definePrivateClass fields [method] module (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some selected => pure selected
    | none => throw .unsupported
  let (owner, one) ← instantiatePrivateClass 64 defaultSplitLimit selected (some 0) module
  let active := {one with privates := {one.privates with names := selected.names}}
  let history ← RegistrationHistory.runSourceHistory push owner requests active
  normalState (← execute 32 defaultSplitLimit matchInit
    {history with environment := [("name", .string name), ("capture", .string captured)] ++ history.environment})

/-- Actual Node preamble/class installation/constructor/source push. The final
parsed `m=[capture]` is an explicit fixture boundary, not matcher.exec156. -/
private def sourcePrepare (name captured : JSString) : Option (Except EvalError State) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let matchInit ← parseBlock matchSource ["capture"]
  pure (prepareCore preamble fields method push matchInit name captured)

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
    NodeMethodsPush.parses_pinned_source, parses_match]
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
/-- The universal ordinary-object theorem is inhabited by actual Node source
initialization and registration. The matched array is supplied by an explicit
parsed fixture; later params is created by execution of ordinary `{}`. -/
theorem source_prepared_input_has_universal_guard_contract (name captured : JSString) :
    ∃ ready outcome,
      sourcePrepare name captured = some (.ok ready) ∧
      (parseBlock literalParamsSource []).map (fun source => execute 16 defaultSplitLimit source ready) =
        some (.ok (.normal (literalParamsState ready))) ∧
      sourceGuard 27 (literalParamsState ready) = some outcome ∧
      GuardContract (literalParamsState ready) ready.objects.length emptyLiteralObject name outcome := by
  let ready := sourcePreparedState name captured
  let root := objectPrototypeProjection []
  have rootFound : ready.objects[0]? = some root := by rfl
  have rootPath : DescriptorPath ready.objects name 0 (root.own.lookup name) 1 := by
    cases own : root.own.lookup name with
    | none => exact .absent rootFound own rfl
    | some descriptor => exact .own rootFound own
  have result := literal_then_capture_satisfies 0 ready root name registered.heap.length [.string captured] captured (root.own.lookup name) 1
    rootFound (Or.inl rfl) rfl rfl (by simp [ready, sourcePreparedState]) rfl (by change 1 ≤ 4294967295; decide) rootPath (by decide)
  exact ⟨ready, _, source_prepared name captured, result.1, result.2.choose_spec.1, result.2.choose_spec.2⟩

/-- info: 'HonoLean.Upstream.NodeCaptureGuard.Examples.source_prepared_input_has_universal_guard_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_prepared_input_has_universal_guard_contract

end HonoLean.Upstream.NodeCaptureGuard.Examples
