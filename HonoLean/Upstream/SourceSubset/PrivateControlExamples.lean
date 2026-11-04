import HonoLean.Upstream.SourceSubset.PrivateControl

namespace HonoLean.Upstream.SourceSubset.PrivateControlChecks

open ECMA2025
set_option maxRecDepth 65536

private def record : PrivateMethod :=
  ⟨"record", [⟨"items", false, .array (.named "unknown")⟩,
      ⟨"value", false, .named "unknown"⟩], .named "void",
    [.evaluate (.call (.variable "items") "push" [.variable "value"])]⟩

private def table : PrivateMethodTable := ⟨0, [⟨record, [], [("record", 7)]⟩]⟩

private def before : State :=
  {environment := [("items", .array 0), ("receivers", .array 1),
      ("flag", .boolean true), ("foreign", .object 1), ("this", .object 1)]
   thisValue := .object 0
   objects := [emptyNullObject, emptyNullObject]
   heap := [[], [.number 1, .number 2]]
   privates := ⟨[("record", 7)], [(0, [(7, .method (.function 0))])]⟩}

private def bindings : List String := ["items", "receivers", "flag", "foreign"]

private def observation (completion : Completion) :=
  match completion with
  | .normal state => (none, state.heap, state.environment, state.thisValue)
  | .returned value state => (some value, state.heap, state.environment, state.thisValue)

private def run (text : String) (state : State := before) :
    Option (Except EvalError (Option Value × List (List Value) × List (String × Value) × Value)) :=
  (parsePrivateControl text bindings ["record"]).map fun program =>
    (runPrivateControl 96 defaultSplitLimit table program state).map observation

theorem parses_generic_nested_control :
    (parsePrivateControl
      "const saved = receivers.shift()\nif (saved) { if (flag) { this.#record(items, saved) } else { items.push(null) } } else { items.push(false) }"
      bindings ["record"]).isSome = true := by cbv

theorem nested_control_executes_both_inner_outcomes :
    let source := "const saved = receivers.shift()\nif (saved) { if (flag) { this.#record(items, saved) } else { items.push(null) } } else { items.push(false) }"
    let unflagged := {before with environment := ("flag", .boolean false) :: withoutBindings before.environment ["flag"]}
    run source = some (.ok (none, [[.number 1], [.number 2]], before.environment, before.thisValue)) ∧
    run source unflagged = some (.ok (none, [[.null], [.number 2]], unflagged.environment, unflagged.thisValue)) := by cbv

/-- The lower entry keeps fresh declarations for subsequent statements of the
enclosing block; the standalone projection restores exactly the caller scope. -/
theorem root_declaration_retention_and_projection :
    let source := "const saved = receivers.shift()\nif (saved) { this.#record(items, saved) }"
    let retained := (parsePrivateControl source bindings ["record"]).map fun program =>
      (executePrivateControl 96 defaultSplitLimit table program before).map observation
    retained = some (.ok (none, [[.number 1], [.number 2]],
      ("saved", .number 1) :: before.environment, before.thisValue)) ∧
    run source = some (.ok (none, [[.number 1], [.number 2]], before.environment, before.thisValue)) := by cbv

/-- The condition shifts once, a false string is handled with ordinary JS
truthiness, and the unchosen arm's unbranded private call is never evaluated. -/
theorem condition_once_and_only_selected_arm :
    run "if (receivers.shift()) { items.push(1) } else { foreign.#record(items, 2) }" =
      some (.ok (none, [[.number 1], [.number 2]], before.environment, before.thisValue)) ∧
    run "if ('') { foreign.#record(items, 1) } else { items.push(2) }" =
      some (.ok (none, [[.number 2], [.number 1, .number 2]], before.environment, before.thisValue)) := by
  cbv
  exact ⟨rfl, rfl⟩

/-- Distinct source leaves read arguments after the first call has completed.
Dynamic this comes from State, despite a conflicting ordinary environment key. -/
theorem repeated_calls_observe_current_state :
    run "this.#record(items, receivers.shift())\nthis.#record(items, receivers.shift())" =
      some (.ok (none, [[.number 1, .number 2], []], before.environment, before.thisValue)) := by cbv

theorem return_and_error_stop_the_continuation :
    run "if (flag) { return receivers.shift() } else { items.push(null) }\nitems.push(9)" =
      some (.ok (some (.number 1), [[], [.number 2]], before.environment, before.thisValue)) ∧
    run "foreign.#record(items, receivers.shift())\nitems.push(9)" =
      some (.error .privateBrand) := by cbv

/-- Comments may contain quote/operator-looking text; quoted URLs and block
comment-looking strings must remain literal contents. CR/LF ASI is retained. -/
theorem line_comments_preserve_quotes_and_boundaries :
    run "const url = 'http://host/*literal*/' // 'ignored\r\nitems.push(url)" =
      some (.ok (none,
        [[.string [104,116,116,112,58,47,47,104,111,115,116,47,42,108,105,116,101,114,97,108,42,47]],
          [.number 1, .number 2]], before.environment, before.thisValue)) ∧
    (parsePrivateControl "items.push(1) // keep newline\n(items).push(2)" bindings ["record"]).isNone = true ∧
    (parsePrivateControl "return // no return expression\n1" bindings ["record"]).isNone = true := by
  cbv
  exact ⟨rfl, trivial⟩

/-- Native line comments end at LS/PS as well. The specialized ASCII entry
rejects these separators instead of deleting any code after them. -/
theorem unicode_comment_separators_reject :
    ([0x2028, 0x2029].all fun code =>
      (parsePrivateControl ("// comment" ++ String.singleton (Char.ofNat code) ++ "items.push(1)")
        bindings ["record"]).isNone) = true := by cbv

theorem unsupported_control_forms_reject :
    (["if (flag) { const nested = 1 }", "if (flag) { let nested = 1 }",
      "const flag = 1", "flag = 1", "++flag", "if (++flag) { items.push(1) }",
      "this.#record(items, ++flag)", "this.#record(items, this)",
      "items.push(this.#record(items, 1))", "if (flag) items.push(1)",
      "(this.#record as unknown)()", "(flag ? this.#record : this.#record)()",
      "if (flag) {} else if (flag) {}", "while (flag) {}", "for (;;) {}",
      "/* block comment */ items.push(1)", "items.push(`template`)",
      "items.push('escaped\\'quote//still-string')", "items.push(1) items.push(2)"].all
      (fun source => (parsePrivateControl source bindings ["record"]).isNone)) = true := by cbv

/-- The extension does not teach older statement/expression entries to invoke
the private block method with arguments. -/
theorem old_entries_keep_private_call_rejection :
    (parseBlock "this.#record(items, 1)" bindings ["record"] true).isNone = true ∧
    (parseExpression "this.#record(items, 1)" bindings ["record"] true).isNone = true := by cbv

example : executePrivateControl 0 defaultSplitLimit table [] before = .error .exhausted := rfl
example : executePrivateControlStmt 0 defaultSplitLimit table (.privateCall ⟨.this, "record", []⟩) before =
    .error .exhausted := rfl

end HonoLean.Upstream.SourceSubset.PrivateControlChecks
