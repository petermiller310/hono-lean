import HonoLean.Upstream.SourceSubset.Arithmetic
import HonoLean.Upstream.SourceSubset.PrivateControlParser

namespace HonoLean.Upstream.SourceSubset.ArithmeticChecks

set_option maxRecDepth 65536

theorem parses_source_last_index :
    parseExpression "i === len - 1" ["i", "len"] =
      some (.strictEqual (.variable "i") (.subtract (.variable "len") (.number 1))) := by cbv

/-- Actual source97 retains a nullable array annotation. Admitting the null
type name adds metadata only; the initializer remains the existing null value. -/
theorem parses_nullable_array_declaration :
    parseBlock "let partOffsets: number[] | null = null" [] =
      some [.mutableDeclare "partOffsets" (some (.union (.array (.named "number")) (.named "null"))) .null] := by cbv

theorem subtraction_is_left_associative :
    parseExpression "a - b - c" ["a", "b", "c"] =
      some (.subtract (.subtract (.variable "a") (.variable "b")) (.variable "c")) ∧
    parseExpression "a - (b - c)" ["a", "b", "c"] =
      some (.subtract (.variable "a") (.subtract (.variable "b") (.variable "c"))) := by cbv

theorem subtraction_precedes_relational_and_equality :
    parseExpression "a - b < c - d" ["a", "b", "c", "d"] =
      some (.compare .less (.subtract (.variable "a") (.variable "b"))
        (.subtract (.variable "c") (.variable "d"))) ∧
    parseExpression "a - b === c - d" ["a", "b", "c", "d"] =
      some (.strictEqual (.subtract (.variable "a") (.variable "b"))
        (.subtract (.variable "c") (.variable "d"))) := by cbv

/-- Shapes checked against the local TypeScript6.0.3 parser. Unparenthesized
assertion operands that require resuming arithmetic remain outside this
restricted assertion grammar and reject instead of acquiring a different AST. -/
theorem assertion_precedence_and_restricted_mixes :
    parseExpression "a - b as number" ["a", "b"] =
      some (.typeAssertion (.subtract (.variable "a") (.variable "b")) (.named "number")) ∧
    parseExpression "(a as number) - b" ["a", "b"] =
      some (.subtract (.typeAssertion (.variable "a") (.named "number")) (.variable "b")) ∧
    parseExpression "i === len - 1 as number" ["i", "len"] =
      some (.strictEqual (.variable "i")
        (.typeAssertion (.subtract (.variable "len") (.number 1)) (.named "number"))) ∧
    (parseExpression "a as number - b" ["a", "b"]).isNone = true ∧
    (parseExpression "a - b as number - c" ["a", "b", "c"]).isNone = true := by
  cbv
  exact ⟨rfl, trivial⟩

theorem lexical_minus_and_decrement_are_distinct :
    parseExpression "a - -1" ["a"] = some (.subtract (.variable "a") (.number (-1))) ∧
    parseExpression "-2 - -1" [] = some (.subtract (.number (-2)) (.number (-1))) ∧
    parseExpression "'a--1'" [] = some (.string [97, 45, 45, 49]) ∧
    (["a--1", "a--", "--a", "a---1", "a - -0", "a + 1", "a * 1", "a / 1"].all
      (fun source => (parseExpression source ["a"]).isNone)) = true := by
  cbv
  exact ⟨rfl, rfl, rfl, trivial⟩

theorem newline_continuation_and_return_asi :
    parseExpression "a\n-\r\n1" ["a"] = some (.subtract (.variable "a") (.number 1)) ∧
    parseBlock "const result = a\n-1" ["a"] =
      some [.declare "result" (.subtract (.variable "a") (.number 1))] ∧
    (parseBlock "return\n-1" []).isNone = true ∧
    (parseBlock "a - 1 b" ["a", "b"]).isNone = true := by
  cbv
  exact ⟨rfl, rfl, trivial⟩

private def before : State :=
  {environment := [("values", .array 0)], heap := [[.number 9, .number 4]]}

theorem operands_run_left_to_right_once :
    (parseExpression "values.shift() - values.shift()" ["values"]).map
      (fun expression => (evalExpression 32 defaultSplitLimit expression before).map
        (fun (value, after) => (value, after.heap))) =
      some (.ok (.number 5, [[]])) := by cbv

theorem rhs_failure_precedes_numeric_specialization :
    evalExpression 32 defaultSplitLimit (.subtract (.string [120]) (.variable "missing")) {} =
      .error .missingVariable ∧
    evalExpression 32 defaultSplitLimit (.subtract (.string [120]) (.number 1)) {} =
      .error .unsupported := by cbv

theorem zero_length_is_negative_one :
    (evalExpression 32 defaultSplitLimit (.subtract (.number 0) (.number 1)) {}).map Prod.fst =
      .ok (.number (-1)) ∧ Arithmetic.ExactSubtractionDomain 0 1 := by
  constructor
  · cbv <;> rfl
  · exact Arithmetic.denseLength_subtract_one 0 (by decide)

/-- Safe input operands alone do not license the exact-integer native boundary.
The model still returns the mathematical result beyond that declared domain. -/
theorem safe_operands_can_have_unsafe_difference :
    (evalExpression 32 defaultSplitLimit (.subtract (.number 9007199254740991) (.number (-2))) {}).map Prod.fst =
      .ok (.number 9007199254740993) ∧
    Arithmetic.SafeInteger 9007199254740991 ∧ Arithmetic.SafeInteger (-2) ∧
    ¬ Arithmetic.ExactSubtractionDomain 9007199254740991 (-2) := by
  constructor
  · cbv <;> rfl
  · unfold Arithmetic.ExactSubtractionDomain Arithmetic.SafeInteger Arithmetic.maximumSafeInteger
    omega

theorem subtraction_walkers_keep_binding_and_private_guards :
    (parsePrivateMethod "#run(x: number): number { return x - 1 }" [] ["run"]).isSome = true ∧
    (parsePrivateMethod "#run(): number { return ++captured - 1 }" ["captured"] ["run"]).isNone = true ∧
    (parsePrivateFields "#field: number = seed - 1" ["seed"]).isSome = true ∧
    (parsePrivateFields "#field: number = ++seed - 1" ["seed"]).isNone = true ∧
    (parsePrivateControl "if (n - 1) { values.push(n) }" ["n", "values"] []).isSome = true ∧
    (parsePrivateControl "if (++n - 1) { values.push(n) }" ["n", "values"] []).isNone = true ∧
    (parsePrivateControl "(this.#run - 1)()" [] ["run"]).isNone = true ∧
    (parsePrivateMethodCall "this.#run(n - 1)" ["n"] ["run"]).isSome = true ∧
    (parsePrivateMethodCall "this.#run(this - 1)" [] ["run"]).isNone = true ∧
    (parseExpression "node.#unknown - 1" ["node"] ["params"]).isNone = true := by cbv

end HonoLean.Upstream.SourceSubset.ArithmeticChecks
