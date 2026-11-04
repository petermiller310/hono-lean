import HonoLean.Upstream.NodeExecCall.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.NodeExecCall.Examples
open SourceSubset ECMA2025
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def nameKey : JSString := [105, 100]
private def methods : PrivateMethodTable := ⟨1, []⟩
private def functions : FunctionTable := ⟨2, []⟩
private def bodySource : BodyShape → String
  | .argument => "exec(input) { return input }"
  | .nullResult => "exec(input) { return null }"
  | .receiverResult => "exec(input) { return this }"
  | .singleton => "exec(input) { return [input] }"
  | .emptyArray => "exec(input) { return [] }"
  | .fallthrough => "exec(input) {}"
private def bodyProgram (shape : BodyShape) : MemberMethod := ⟨"exec", "input", shapeBody shape "input"⟩
private def captures : List (String × Value) := [("input", .number 999), ("privateCapture", .boolean true)]
private def closure (shape : BodyShape) : MemberClosure := ⟨bodyProgram shape, captures, []⟩
private def members (shape : BodyShape) : MemberTable := ⟨3, [closure shape]⟩
private def matcherObject : OrdinaryObject := newDataObject emptyLiteralObject execKey (.function 3)
private def seed (input : JSString) : State :=
  {environment := [("callee", .function 3), ("restPathString", .string input), ("params", .object 1),
      ("name", .string nameKey), ("node", .object 2), ("emptyParams", .object 1), ("m", .string [111, 108, 100])]
   objects := [objectPrototypeProjection [], emptyNullObject, emptyLiteralObject]
   heap := [[.number 91]]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   sets := [[nameKey]]
   thisValue := .object 2
   privates := PrivateStore.ofData [("params", 5)] [(2, [(5, .object 1)])]}
private def before (input : JSString) : State :=
  {seed input with
    environment := ("matcher", .object 3) :: (seed input).environment
    objects := (seed input).objects ++ [matcherObject]}
private def installSource : String := "const matcher = { exec: callee }\n"
private def installProgram : List Stmt :=
  [.declare "matcher" (.objectLiteral [(.string execKey, .variable "callee")])]

private theorem parses_body (shape : BodyShape) : parseMemberMethod (bodySource shape) ["input", "privateCapture"] [] = some (bodyProgram shape) := by
  cases shape <;> cbv
private theorem parses_install : parseBlock installSource ["callee"] = some installProgram := by cbv

/-- The ordinary method body is actually parsed and its function-valued data
property is installed by a parsed ordinary-object literal. Creating a native
closure/table/realm correspondence remains a declared input boundary, as do the
supplied private owner and the initial method/function representation tables. -/
private def prepare (shape : BodyShape) (input : JSString) : Option (Except EvalError (MemberTable × State)) := do
  let method ← parseMemberMethod (bodySource shape) ["input", "privateCapture"] []
  let declarations ← parseBlock installSource ["callee"]
  pure do
    let completion ← execute 20 defaultSplitLimit declarations (seed input)
    match completion with
    | .normal after => pure (⟨3, [⟨method, captures, []⟩]⟩, after)
    | _ => throw .unsupported

private theorem prepared (shape : BodyShape) (input : JSString) : prepare shape input = some (.ok (members shape, before input)) := by
  rw [prepare, parses_body, parses_install]
  cbv

private theorem inputs (shape : BodyShape) (input : JSString) : Inputs (before input) methods functions (members shape) (closure shape) 3 3 input :=
  ⟨rfl, rfl, ⟨true, true, true, 1, .own rfl (putOwn_self _ _ _), by decide⟩, by change 1 ≤ 3; decide, by change 1 ≤ 3; decide, by change 2 ≤ 3; decide, by change 3 ≤ 3; decide, rfl⟩

/-- Every selected source-defined body is executable from the prepared current
property. In particular it is the BODY, rather than the spelling exec, that
determines m. No desired return/array or successful body run is an input. -/
theorem parsed_method_and_property_prepare_all_six_computations (shape : BodyShape) (input : JSString) :
    ∃ table ready, prepare shape input = some (.ok (table, ready)) ∧
      sourceExec 20 methods functions table ready = some (.ok (resultState shape ready 3 input)) ∧
      Contract 20 ready (resultState shape ready 3 input) (closure shape) 3 3 input shape := by
  exact ⟨members shape, before input, prepared shape input, source_exec_satisfies 0 _ methods functions _ _ 3 3 input shape (inputs shape input) rfl⟩

/-- Ordinary primitive, null, receiver and allocated-array returns remain
distinct. Dynamic this is matcher3 while the caller's this2 is restored. -/
theorem body_returns_are_not_abstract_RegExpExec_validation (input : JSString) :
    (resultState .argument (before input) 3 input).environment.lookup "m" = some (.string input) ∧
    (resultState .nullResult (before input) 3 input).environment.lookup "m" = some .null ∧
    (resultState .receiverResult (before input) 3 input).environment.lookup "m" = some (.object 3) ∧
    (resultState .emptyArray (before input) 3 input).heap[1]? = some [] ∧
    (resultState .fallthrough (before input) 3 input).environment.lookup "m" = some .undefined ∧
    (resultState .receiverResult (before input) 3 input).thisValue = .object 2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem header_test_preserves_empty_string_null_and_array_truthiness :
    resultTruthy .argument [] = false ∧ resultTruthy .argument [120] = true ∧
    resultTruthy .nullResult [120] = false ∧ resultTruthy .emptyArray [] = true ∧
    resultTruthy .singleton [] = true ∧ resultTruthy .fallthrough [] = false := by decide

private def inherited (input : JSString) : State :=
  {before input with objects := (seed input).objects ++ [⟨[], some 4, true⟩, matcherObject]}
private theorem inherited_inputs (input : JSString) : Inputs (inherited input) methods functions (members .receiverResult) (closure .receiverResult) 3 3 input :=
  ⟨rfl, rfl, ⟨true, true, true, 2, .parent rfl rfl rfl (.own rfl (putOwn_self _ _ _)), by decide⟩,
    by change 1 ≤ 3; decide, by decide, by decide, by decide, rfl⟩

/-- An inherited current exec still receives original matcher3, not holder4. -/
theorem inherited_exec_uses_original_receiver (input : JSString) :
    sourceExec 20 methods functions (members .receiverResult) (inherited input) =
      some (.ok (resultState .receiverResult (inherited input) 3 input)) ∧
    Contract 20 (inherited input) (resultState .receiverResult (inherited input) 3 input) (closure .receiverResult) 3 3 input .receiverResult :=
  source_exec_satisfies 0 _ methods functions _ _ 3 3 input .receiverResult (inherited_inputs input) rfl

private theorem guard_target (input : JSString) : GuardTarget (before input) 1 emptyNullObject nameKey none 1 :=
  ⟨⟨Or.inl rfl, rfl, rfl, rfl, by simp [WellFormedObject, emptyNullObject]⟩,
    rfl, .absent rfl rfl rfl, by decide⟩

/-- The fresh array and own0 string are derived from the parsed singleton
body, even for empty strings and raw lone-surrogate UTF16. Earlier exec and
surrounding-if reachability are not supplied as desired match facts. -/
theorem singleton_computation_supplies_the_actual_capture_guard (input : JSString) :
    let computed := resultState .singleton (before input) 3 input
    sourceExec 20 methods functions (members .singleton) (before input) = some (.ok computed) ∧
    Contract 20 (before input) computed (closure .singleton) 3 3 input .singleton ∧
    evalExpression 1 defaultSplitLimit guardCondition computed = .ok (.array 1, computed) ∧
    truthy (.array 1) = true ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard 27 computed = some outcome ∧ NodeCaptureGuard.GuardContract computed 1 emptyNullObject nameKey outcome :=
  source_singleton_then_guard_satisfies 0 _ methods functions _ _ 3 3 input 1 emptyNullObject nameKey none 1 (inputs .singleton input) rfl (guard_target input)

/-- Correct123→156→158 ordering. The private owner/shared pointer are supplied
allocated fixture inputs; no Hono class installation or source123 reachability
is inferred from them. Both123 arms are handled by the universal protocol. -/
theorem shared_initializer_then_computed_match_then_guard (input : JSString) :
    let initialized := NodeParamsInit.mapState (before input) emptyLiteralObject
    let computed := resultState .singleton initialized 3 input
    NodeParamsInit.sourceInit 16 (before input) = some (.ok initialized) ∧ NodeParamsInit.InitContract (before input) initialized 2 5 1 1 ∧
    sourceExec 20 methods functions (members .singleton) initialized = some (.ok computed) ∧
    Contract 20 initialized computed (closure .singleton) 3 3 input .singleton ∧
    evalExpression 1 defaultSplitLimit guardCondition computed = .ok (.array 1, computed) ∧ truthy (.array 1) = true ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard 27 computed = some outcome ∧ NodeCaptureGuard.GuardContract computed 4 emptyLiteralObject nameKey outcome := by
  have header : NodeParamsInit.HeaderInputs (before input) 2 5 1 1 :=
    ⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, ⟨rfl, ⟨emptyLiteralObject, rfl⟩, _, rfl, rfl⟩, ⟨objectPrototypeProjection [], rfl⟩⟩
  exact source_init_exec_guard_satisfies 0 _ methods functions _ _ 3 3 2 5 1 1 16 input nameKey emptyLiteralObject none 1
    (inputs .singleton input) rfl (.shared header rfl) (Or.inl rfl) rfl rfl (.absent rfl rfl rfl) (by decide)

private def both : MemberTable := ⟨3, [closure .argument, closure .singleton]⟩
private def replacementSource : String := "matcher.exec = replacement"
private def replacement : Assignment := ⟨.property (.variable "matcher") execKey, .variable "replacement"⟩
private theorem parses_replacement : parseAssignment replacementSource ["matcher", "replacement"] [] = some replacement := by cbv
private def repeatCalls (input : JSString) : Option (Except EvalError (Option Value × Option (List Value) × Value × Bool)) := do
  let first ← sourceExec 20 methods functions both (before input)
  let write ← parseAssignment replacementSource ["matcher", "replacement"] []
  pure do
    let first ← first
    let (_, changed) ← executeAssignment 20 defaultSplitLimit write {first with environment := ("replacement", .function 4) :: first.environment}
    let after ← executeMemberDeclaration 20 defaultSplitLimit methods functions both program changed
    pure (after.environment.lookup "m", after.heap[1]?, after.thisValue,
      decide (after.privates = (before input).privates ∧ after.sets = (before input).sets))

/-- Replacement occurs in a real property assignment BETWEEN activations.
The second source156 reads the new exec; no cache immutability is assumed.
Its const m belongs to a fresh selected entry, not a same-block redeclaration. -/
theorem between_call_replacement_changes_the_computed_result (input : JSString) :
    repeatCalls input = some (.ok (some (.array 1), some [.string input], .object 2, true)) := by
  simp only [repeatCalls, sourceExec, parses_source, Option.map_some, parses_replacement]
  cbv

theorem computed_guard_captures_lone_surrogate_and_empty :
    NodeCaptureGuard.sourceGuard 27 (resultState .singleton (before [0xd800, 47, 0xdc00]) 3 [0xd800, 47, 0xdc00]) =
      some (.ok (.normal (NodeCaptureGuard.writtenState (resultState .singleton (before [0xd800, 47, 0xdc00]) 3 [0xd800, 47, 0xdc00]) 1 emptyNullObject nameKey [0xd800, 47, 0xdc00]))) ∧
    NodeCaptureGuard.sourceGuard 27 (resultState .singleton (before []) 3 []) =
      some (.ok (.normal (NodeCaptureGuard.writtenState (resultState .singleton (before []) 3 []) 1 emptyNullObject nameKey []))) := by
  constructor <;> simp only [NodeCaptureGuard.sourceGuard, NodeCaptureGuard.parses_source, Option.map_some] <;> cbv

private def copiedInputObject : OrdinaryObject := newDataObject emptyLiteralObject [112] (.string [111, 108, 100])
/-- Separate initial graph: an allocated nonshared parent map and its private
pointer are supplied fixture facts, not a claim of Node history reachability. -/
private def copyBefore (input : JSString) : State :=
  {before input with
    objects := (before input).objects ++ [copiedInputObject]
    privates := PrivateStore.ofData [("params", 5)] [(2, [(5, .object 4)])]}
private theorem copy_exec_inputs (input : JSString) : Inputs (copyBefore input) methods functions (members .singleton) (closure .singleton) 3 3 input :=
  ⟨rfl, rfl, ⟨true, true, true, 1, .own rfl (putOwn_self _ _ _), by decide⟩,
    by change 1 ≤ 3; decide, by decide, by decide, by decide, rfl⟩

/-- The nonshared123 arm is also inhabited in the correctly ordered protocol.
Its old own field is copied before exec computes the fresh m array. -/
theorem copied_initializer_then_computed_match_then_guard (input : JSString) :
    let initialized := NodeParamsInit.mapState (copyBefore input) (NodeParamsInit.copiedObject copiedInputObject)
    let computed := resultState .singleton initialized 3 input
    NodeParamsInit.sourceInit 17 (copyBefore input) = some (.ok initialized) ∧
    NodeParamsInit.InitContract (copyBefore input) initialized 2 5 4 1 ∧
    sourceExec 20 methods functions (members .singleton) initialized = some (.ok computed) ∧
    Contract 20 initialized computed (closure .singleton) 3 3 input .singleton ∧
    evalExpression 1 defaultSplitLimit guardCondition computed = .ok (.array 1, computed) ∧ truthy (.array 1) = true ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard 27 computed = some outcome ∧
      NodeCaptureGuard.GuardContract computed 5 (NodeParamsInit.copiedObject copiedInputObject) nameKey outcome := by
  have header : NodeParamsInit.HeaderInputs (copyBefore input) 2 5 4 1 :=
    ⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, ⟨rfl, ⟨emptyLiteralObject, rfl⟩, _, rfl, rfl⟩, ⟨objectPrototypeProjection [], rfl⟩⟩
  have copy : NodeParamsInit.CopyInputs (copyBefore input) 2 5 4 1 copiedInputObject :=
    ⟨header, by decide, rfl, NodeParamsInit.enumerableData_newData emptyLiteralObject [112] (.string [111, 108, 100]) NodeParamsInit.empty_eligible⟩
  exact source_init_exec_guard_satisfies 0 _ methods functions _ _ 3 3 2 5 4 1 17 input nameKey (NodeParamsInit.copiedObject copiedInputObject) none 1
    (copy_exec_inputs input) rfl (.copied copiedInputObject copy) (Or.inl rfl) rfl rfl (.absent rfl rfl rfl) (by decide)

end HonoLean.Upstream.NodeExecCall.Examples
