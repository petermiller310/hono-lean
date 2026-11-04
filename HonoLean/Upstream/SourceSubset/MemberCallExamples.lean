import HonoLean.Upstream.SourceSubset.MemberCall

set_option autoImplicit false

namespace HonoLean.Upstream.SourceSubset.MemberCallChecks

open ECMA2025
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def execKey : JSString := [101, 120, 101, 99]
private def valuesKey : JSString := [118, 97, 108, 117, 101, 115]
private def echo : MemberMethod := ⟨"exec", "input", [.ret (.variable "input")]⟩
private def other : MemberMethod := ⟨"other", "input", [.ret (.number 100)]⟩
private def dynamicThis : MemberMethod := ⟨"exec", "input", [.ret .this]⟩
private def effectSource : String := "exec(input) {\nthis.values.push(input)\nthis.#secret = captured\nreturn [this, input, this.#secret]\n}"
private def effect : MemberMethod := ⟨"exec", "input",
  [.evaluate (.call (.property .this valuesKey) "push" [.variable "input"]),
   .assign ⟨.privateProperty .this "secret", .variable "captured"⟩,
   .ret (.arrayLiteral [(false, .this), (false, .variable "input"), (false, .privateProperty .this "secret")])]⟩
private def normal : MemberMethod := ⟨"exec", "input", [.evaluate (.call (.property .this valuesKey) "push" [.variable "input"])]⟩
private def captures : List (String × Value) := [("input", .number 99), ("captured", .number 13), ("this", .object 1)]
private def names : List (String × Nat) := [("secret", 77)]
private def close (method : MemberMethod) : MemberClosure := ⟨method, captures, names⟩
private def methods : PrivateMethodTable := ⟨1, [⟨⟨"noop", [], .named "void", []⟩, [], []⟩]⟩
private def functions : FunctionTable := ⟨2, [⟨⟨"echo", "input", [.ret (.variable "input")]⟩, [], []⟩]⟩
private def members : MemberTable := ⟨3, [close echo, close other, close dynamicThis, close effect, close normal]⟩
private def receiver (handle : Nat) : OrdinaryObject :=
  {own := [(execKey, .data (.function handle) true true true), (valuesKey, .data (.array 0) true true true)]}
private def before : State :=
  {environment := [("matcher", .object 0), ("restPathString", .string [55296, 233]),
      ("receivers", .array 1), ("values", .array 0), ("counter", .number 4),
      ("replacement", .function 4), ("captured", .number 999), ("this", .object 1)]
   objects := [receiver 3, receiver 4, emptyNullObject]
   heap := [[.number 7, .number 9], [.object 0, .object 1], [.number 5, .number 6]]
   functions := [⟨⟨"oldNoArg", .number 0⟩, []⟩]
   sets := [[[105, 100]]]
   thisValue := .object 2
   privates := ⟨[("secret", 5), ("caller", 6)], [(0, [(77, .data (.number 11)), (5, .data (.number 88)), (6, .method (.function 1))])]⟩}
private def atHandle (handle : Nat) : State := {before with objects := before.objects.set 0 (receiver handle)}
private def observation (result : Value × State) :=
  (result.1, result.2.heap, decide (result.2.environment = before.environment),
    decide (result.2.thisValue = before.thisValue), decide (result.2.privates.names = before.privates.names))

/-- The new admission keeps the actual call AST, while the old entry still
rejects it. A genuine ordinary method body is parsed independently. -/
theorem actual_declaration_and_ordinary_method_are_parsed :
    parseMemberDeclaration "const m = matcher.exec(restPathString)" ["matcher", "restPathString"] [] =
      some (.declare "m" (.call (.variable "matcher") "exec" [.variable "restPathString"])) ∧
    (parseBlock "const m = matcher.exec(restPathString)" ["matcher", "restPathString"]).isNone = true ∧
    parseMemberMethod "exec(input) { return input }" [] [] = some echo ∧
    parseMemberMethod effectSource ["captured"] ["secret"] = some effect := by cbv

theorem parser_rejects_rewrites_callbacks_tdz_and_wrong_arity :
    (["#exec(input) { return input }", "exec = (input) => { return input }", "exec() { return this }",
      "exec(input, extra) { return input }", "exec(input: string) { return input }",
      "exec(input) { return ++captured }", "exec(input) { captured = input }",
      "exec(input) { return f() }", "exec(input) { return this.#unknown }",
      "exec(input) { if (input) { const local = input } }", "exec(input) { return super.exec(input) }",
      "exec(input) { return arguments }", "exec(input) { return input } trailing"] : List String).all
      (fun source => (parseMemberMethod source ["captured", "f"] ["secret"]).isNone) = true ∧
    (["const m = matcher.exec()", "const m = matcher.exec(value, value)", "const m = matcher.exec(f())",
      "const m = matcher.exec(++value)", "const m = matcher.exec(m)", "const m = matcher.exec(value)\n[0]",
      "const m = matcher.exec(value); const extra = value"] : List String).all
      (fun source => (parseMemberDeclaration source ["matcher", "value", "f"] []).isNone) = true := by cbv

/-- This is an ordinary custom source method, not a regex result oracle. Its
primitive/null/fresh-array results must not be constrained to object/null. -/
theorem primitive_null_and_array_results_keep_actual_values :
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 0] before).map Prod.fst = .ok (.number 0) ∧
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.null] before).map Prod.fst = .ok .null ∧
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.arrayLiteral [(false, .number 8)]] before).map
      (fun result => (result.1, result.2.heap[3]?)) = .ok (.array 3, some [.number 8]) := by cbv

/-- Receiver expression and argument consume the same array in order. The
saved receiver0/exec3 runs, not receiver1/exec4 (which would return100).
Same-object exec mutation DURING an argument requires an unmodeled callback/
assignment-expression domain and is tested only in native boundary controls. -/
theorem saved_receiver_and_callee_precede_argument_array_mutation :
    (runMemberCall 64 defaultSplitLimit methods functions members (.call (.variable "receivers") "shift" []) "exec"
      [.call (.variable "receivers") "shift" []] before).map observation =
      .ok (.object 1, [[.number 7, .number 9], [], [.number 5, .number 6]], true, true, true) := by cbv

theorem dynamic_receiver_is_distinct_from_caller_and_lexical_this :
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.this] before).map Prod.fst = .ok (.object 2) ∧
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 9] (atHandle 5)).map
      (fun result => (result.1, result.2.thisValue, result.2.environment.lookup "this")) =
      .ok (.object 0, .object 2, some (.object 1)) := by cbv

/-- Resolve after arguments, but do not reread exec. A plain caller increment
is retained because restoration uses the post-argument caller environment. -/
theorem missing_extra_arguments_and_caller_effects :
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [] before).map Prod.fst = .ok .undefined ∧
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec"
      [.call (.variable "values") "shift" [], .call (.variable "values") "shift" []] before).map observation =
      .ok (.number 7, [[], [.object 0, .object 1], [.number 5, .number 6]], true, true, true) ∧
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.preIncrement "counter"] before).map
      (fun result => (result.1, result.2.environment.lookup "counter", result.2.thisValue)) =
      .ok (.number 5, some (.number 5), .object 2) := by cbv

theorem argument_error_precedes_noncallability_but_null_base_precedes_arguments :
    let bad := {before with objects := before.objects.set 0 (newDataObject (receiver 3) execKey (.number 0))}
    runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.variable "missing"] bad = .error .missingVariable ∧
    runMemberCall 64 defaultSplitLimit methods functions members .null "exec" [.variable "missing"] before = .error .unsupported ∧
    runMemberCall 64 defaultSplitLimit methods functions ⟨1, [close echo]⟩ (.variable "matcher") "exec" [.variable "missing"] before = .error .missingVariable := by cbv

/-- Partition and unsupported IDs describe the represented closure domain;
they do not classify native callable builtins/proxies/other function kinds. -/
theorem all_existing_function_ranges_are_excluded :
    memberTableSeparated methods functions members before = true ∧
    memberTableSeparated methods functions ⟨0, [close echo]⟩ before = false ∧
    memberTableSeparated methods functions ⟨1, [close echo]⟩ before = false ∧
    memberTableSeparated methods functions ⟨2, [close echo]⟩ before = false ∧
    runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 1] (atHandle 0) = .error .unsupported ∧
    runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 1] (atHandle 1) = .error .unsupported ∧
    runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 1] (atHandle 2) = .error .unsupported := by cbv

theorem actual_parsed_body_keeps_heap_private_effects_and_scope :
    (parseMemberMethod effectSource ["captured"] ["secret"]).map (fun program =>
      (runMemberCall 64 defaultSplitLimit methods functions ⟨3, [⟨program, captures, names⟩]⟩
        (.variable "matcher") "exec" [.number 42] before).map (fun result =>
          (result.1, result.2.heap, (result.2.privates.elements.lookup 0).bind (fun fields => fields.lookup 77),
           (result.2.privates.elements.lookup 0).bind (fun fields => fields.lookup 5),
           decide (result.2.environment = before.environment), decide (result.2.thisValue = before.thisValue),
           decide (result.2.privates.names = before.privates.names)))) =
      some (.ok (.array 3, [[.number 7, .number 9, .number 42], [.object 0, .object 1], [.number 5, .number 6],
        [.object 0, .number 42, .number 13]], some (.data (.number 13)), some (.data (.number 88)), true, true, true)) := by cbv

theorem normal_completion_is_undefined_with_effects :
    (runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 42] (atHandle 7)).map
      (fun result => (result.1, result.2.heap[0]?, result.2.environment, result.2.thisValue)) =
      .ok (.undefined, some [.number 7, .number 9, .number 42], before.environment, before.thisValue) := by cbv

/-- A real assignment BETWEEN calls replaces the callee on the same object.
The second current Get sees the new function even though its source name is
other. There is no builtin exec spelling rule and no RegExpExec fallback. -/
theorem current_exec_replacement_between_calls_changes_actual_callee :
    let outcome : Except EvalError (Value × Value) := do
      let (first, state) ← runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 7] before
      let assignment ← match parseAssignment "matcher.exec = replacement" ["matcher", "replacement"] with
        | some assignment => pure assignment | none => throw .unsupported
      let (_, changed) ← executeAssignment 32 defaultSplitLimit assignment state
      let (second, _) ← runMemberCall 64 defaultSplitLimit methods functions members (.variable "matcher") "exec" [.number 7] changed
      pure (first, second)
    outcome = .ok (.number 7, .number 100) := by cbv

theorem declaration_binds_actual_primitive_result :
    (parseMemberDeclaration "const m = matcher.exec(restPathString)" ["matcher", "restPathString"] []).map
      (fun declaration => (executeMemberDeclaration 64 defaultSplitLimit methods functions members declaration before).map
        (fun after => (after.environment.lookup "m", after.heap, after.thisValue))) =
      some (.ok (some (.string [55296, 233]), before.heap, before.thisValue)) := by cbv

theorem echo_body_has_operational_contract_for_arbitrary_values (value receiverValue : Value) (state : State) :
    MemberBodyExecution 32 defaultSplitLimit (close echo) receiverValue [value] state value state := by
  apply (invokeMemberClosure_iff 32 defaultSplitLimit (close echo) receiverValue [value] state state value).mp
  have safe : memberBodyAdmitted (close echo) = true := rfl
  unfold invokeMemberClosure
  rw [safe]
  simp [close, echo, runBlock, declaredNames,
    memberActivation, execute, evalExpression, lookupVariable, restoreCompletion, restoreMemberCaller, withoutBindings,
    bind, Except.bind, pure, Except.pure]

/-- info: 'HonoLean.Upstream.SourceSubset.invokeMemberClosure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invokeMemberClosure_iff
/-- info: 'HonoLean.Upstream.SourceSubset.runMemberCall_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runMemberCall_resolved
/-- info: 'HonoLean.Upstream.SourceSubset.invokeMemberClosure_caller_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms invokeMemberClosure_caller_frames

end HonoLean.Upstream.SourceSubset.MemberCallChecks
