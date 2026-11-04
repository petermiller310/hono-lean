import HonoLean.Upstream.SourceSubset.HasOwn
import HonoLean.Upstream.SourceSubset.Parser

namespace HonoLean.Upstream.SourceSubset.HasOwnChecks

open ECMA2025
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def source := "if (!Object.hasOwn(params, name)) {\n  params[name] = m[0]\n}"
private def program : List Stmt :=
  [.branch (.logicalNot (.call (.variable "Object") "hasOwn" [.variable "params", .variable "name"]))
    [.assign ⟨.index (.variable "params") (.variable "name"), .index (.variable "m") (.number 0)⟩]]
private def key : JSString := [55296, 233]
private def getterKey : JSString := [103]
private def inheritedKey : JSString := [105]
private def hasOwnKey : JSString := [104, 97, 115, 79, 119, 110]
private def object : OrdinaryObject :=
  {own := [(key, .data .undefined false false false),
           (getterKey, .accessor .unsupported .unsupported false false),
           ([110], .data .null false true false), ([102], .data (.boolean false) true true true),
           ([114], .data (.number 0) false false false), ([], .data (.string []) false false false)]
   prototype := some 1}
private def before : State :=
  {environment := [("params", .object 0), ("name", .string key)]
   objects := [object, {own := [(inheritedKey, .data (.number 7) true true true)]}]
   heap := [[.number 3]]
   functions := [⟨⟨"opaque", .number 5⟩, [("capture", .array 0)]⟩]
   sets := [[[55296]]]
   thisValue := .object 1
   privates := PrivateStore.ofData [("keep", 7)] [(0, [(7, .array 0)])]}

theorem parses_original_guard_and_index_assignment : parseBlock source ["params", "name", "m"] = some program := by cbv

theorem exact_two_argument_admission_is_conservative :
    (["Object.hasOwn()", "Object.hasOwn(params)", "Object.hasOwn(params, name, m)",
      "Object.hasOwn(params, unknown)", "Object.other(params, name)"] : List String).all
      (fun text => (parseExpression text ["params", "name", "m"]).isNone) = true := by cbv

/-- Undefined/falsy/nonenumerable/readonly values and unsupported getters all
count as own presence. The getter is never invoked by this operation. -/
theorem descriptor_presence_ignores_flags_and_values :
    ([key, getterKey, [110], [102], [114], []] : List JSString).all
      (fun name => match intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.object 0, .string name] before with
        | .ok (.boolean true, _) => true
        | _ => false) = true := by cbv

theorem inherited_descriptor_is_not_an_own_descriptor :
    intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.object 0, .string inheritedKey] before =
      .ok (.boolean false, before) := by cbv

/-- The standard global fallback and an explicit standard constructor binding
both dispatch the same intrinsic and preserve the complete input State. -/
theorem standard_binding_and_explicit_constructor :
    (parseExpression "Object.hasOwn(params, name)" ["params", "name"]).map
      (fun value => evalExpression 32 defaultSplitLimit value before) = some (.ok (.boolean true, before)) ∧
    evalExpression 32 defaultSplitLimit (.call (.variable "Object") "hasOwn" [.variable "params", .variable "name"])
      {before with environment := ("Object", .objectConstructor) :: before.environment} =
      .ok (.boolean true, {before with environment := ("Object", .objectConstructor) :: before.environment}) := by cbv

/-- Ownership makes the guard false; m is intentionally not bound. Inherited
prototype data and the own unsupported getter remain completely unobserved. -/
theorem own_getter_guard_skips_assignment_and_missing_m :
    execute 32 defaultSplitLimit program {before with environment := [("params", .object 0), ("name", .string getterKey)]} =
      .ok (.normal {before with environment := [("params", .object 0), ("name", .string getterKey)]}) := by cbv

theorem arguments_evaluate_left_to_right_and_keep_heap_effects :
    evalExpression 32 defaultSplitLimit
      (.call (.variable "Object") "hasOwn" [.call (.variable "args") "shift" [], .call (.variable "args") "shift" []])
      {before with environment := [("args", .array 0)], heap := [[.object 0, .string getterKey]]} =
      .ok (.boolean true, {before with environment := [("args", .array 0)], heap := [[]]}) := by cbv

/-- Receiver/method lookup precedes argument effects. These shadows are outside
StandardObjectBinding; the shared dispatcher never falls back to the builtin. -/
theorem object_shadow_and_method_get_precede_arguments :
    evalExpression 32 defaultSplitLimit (.call (.variable "Object") "hasOwn" [.call (.variable "bad") "shift" [], .string key])
      {environment := [("Object", .null), ("bad", .array 9)]} = .error .unsupported ∧
    evalExpression 32 defaultSplitLimit (.call (.variable "Object") "hasOwn" [.call (.variable "bad") "shift" [], .string key])
      {environment := [("Object", .object 0), ("bad", .array 9)],
       objects := [{own := [(hasOwnKey, .accessor .unsupported .unsupported true true)]}]} =
      .error (.objectError .unsupported) := by cbv

/-- Get may return a noncallable value; its validation remains after all args,
so an argument's error wins rather than an early callable rejection. -/
theorem shadow_noncallable_validation_is_after_arguments :
    evalExpression 32 defaultSplitLimit (.call (.variable "Object") "hasOwn" [.call (.variable "bad") "shift" [], .string key])
      {environment := [("Object", .object 0), ("bad", .array 9)],
       objects := [{own := [(hasOwnKey, .data (.number 0) true true true)]}]} = .error .invalidReference := by cbv

/-- These are declared model boundaries, not native errors: ordinary object
allocation and primitive string keys are required; boxing/coercion stay open. -/
theorem unsupported_arguments_and_invalid_reference :
    intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.object 0, .number 0] before = .error .unsupported ∧
    intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.string [97], .string key] before = .error .unsupported ∧
    intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.null, .string key] before = .error .unsupported ∧
    intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.object 9, .string key] before = .error (.objectError .invalidReference) := by cbv

/-- Both arguments run before intrinsic receiver/key specialization. -/
theorem right_argument_error_precedes_argument_domain_rejection :
    evalExpression 32 defaultSplitLimit
      (.call (.variable "Object") "hasOwn" [.null, .call (.variable "bad") "shift" []])
      {environment := [("bad", .array 9)]} = .error .invalidReference := by cbv

theorem inherited_writable_data_creates_real_own_capture :
    execute 32 defaultSplitLimit program
      {environment := [("params", .object 0), ("name", .string inheritedKey), ("m", .array 0)]
       heap := [[.string key]], objects := [{prototype := some 1}, {own := [(inheritedKey, .data .null true true true)]}]} =
    .ok (.normal {
      environment := [("params", .object 0), ("name", .string inheritedKey), ("m", .array 0)]
      heap := [[.string key]]
      objects := [newDataObject {prototype := some 1} inheritedKey (.string key), {own := [(inheritedKey, .data .null true true true)]}]} ) := by cbv

/-- Existing ordinary [[Set]]/legacy __proto__ behavior is unchanged: the guard
finds no own key, then a primitive string goes through the inherited setter. -/
theorem inherited_legacy_proto_setter_is_not_bypassed :
    let state : State := {
      environment := [("params", .object 1), ("name", .string protoKey), ("m", .array 0)]
      heap := [[.string key]]
      objects := d1Realm []}
    execute 32 defaultSplitLimit program state = .ok (.normal state) := by cbv

theorem symbolic_descriptor_presence_and_frame (state : State) (reference : Nat) (name : JSString)
    (record : OrdinaryObject) (found : state.objects[reference]? = some record) :
    ∃ present, intrinsic defaultSplitLimit .objectConstructor "hasOwn" [.object reference, .string name] state =
      .ok (.boolean present, state) ∧ HasOwnContract state state reference name present :=
  intrinsic_hasOwn_satisfies state reference name record found defaultSplitLimit

/-- The target allocated by the first argument is read in the post-argument
object store; no pre-argument object/descriptor snapshot is used. -/
theorem first_argument_allocation_is_visible_to_hasOwn :
    evalExpression 32 defaultSplitLimit
      (.call (.variable "Object") "hasOwn" [.objectLiteral [(.string key, .boolean false)], .string key])
      {objects := [objectPrototypeProjection []]} =
    .ok (.boolean true, {objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject key (.boolean false)]}) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.intrinsic_hasOwn_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.intrinsic_hasOwn_satisfies
/-- info: 'HonoLean.Upstream.SourceSubset.eval_hasOwn_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.eval_hasOwn_standard
/-- info: 'HonoLean.Upstream.SourceSubset.eval_hasOwn_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.eval_hasOwn_resolved

end HonoLean.Upstream.SourceSubset.HasOwnChecks
