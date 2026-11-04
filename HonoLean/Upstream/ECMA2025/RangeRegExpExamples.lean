import HonoLean.Upstream.ECMA2025.RangeRegExp

set_option autoImplicit false

namespace HonoLean.Upstream.ECMA2025.RangeRegExp.Checks

open SourceSubset
private def text (value : String) : JSString := value.toList.map (UInt16.ofNat ∘ Char.toNat)

theorem syntax_and_instructions_retain_each_source_operator :
    parse (text "^[0-9]+$") = some (.sequence .start (.sequence (.plus (.range 48 57)) .finish)) ∧
    compile (anchoredPlus 48 57) = some [.assertStart, .consumeRange 48 57, .repeatRange 48 57, .assertEnd, .accept] := by decide

/-- Arbitrary literal endpoints in the declared grammar, not a special parser
case for the exact digit string, have checked parse/compile/execute bridges. -/
theorem every_safe_ordered_range_has_parser_and_machine_contract (lower upper : UInt16)
    (safeLower : SafeEndpoint lower) (safeUpper : SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat)
    (input : JSString) :
    parse [94, 91, lower, 45, upper, 93, 43, 36] = some (anchoredPlus lower upper) ∧
    compile (anchoredPlus lower upper) = some (code lower upper) ∧
    execute (code lower upper) input =
      (if Accepted lower upper input then .matched ⟨0, input.length, []⟩ else .noMatch) :=
  ⟨parse_complete _ _ (.anchored lower upper safeLower safeUpper ordered), compile_anchoredPlus lower upper,
    execute_anchoredPlus lower upper input⟩

theorem digits_consume_whole_nonempty_input_with_no_captures :
    execute (code 48 57) [48, 49, 57] = .matched ⟨0, 3, []⟩ ∧
    execute (code 48 57) [53] = .matched ⟨0, 1, []⟩ ∧
    execute (code 48 57) [] = .noMatch := by decide

/-- Original code units are inspected. There is no Unicode decoding, digit
category shortcut, line-terminator exception or implicit trimming. -/
theorem nonascii_surrogates_and_line_terminators_are_not_ascii_digits :
    ([[49, 50, 10], [49, 50, 13, 10], [49, 10, 50], [65297, 65298], [55296],
      [56320], [55296, 56320], [49, 8232], [32, 49], [49, 32]] : List JSString).all
      (fun input => execute (code 48 57) input == .noMatch) = true := by decide

theorem letters_and_singleton_ranges_execute_the_same_machine :
    parse (text "^[a-f]+$") = some (anchoredPlus 97 102) ∧
    execute (code 97 102) [97, 99, 102] = .matched ⟨0, 3, []⟩ ∧
    execute (code 97 102) [103] = .noMatch ∧
    parse (text "^[x-x]+$") = some (anchoredPlus 120 120) ∧
    execute (code 120 120) [120, 120] = .matched ⟨0, 2, []⟩ := by decide

/-- Endpoint safety does not silently restrict intervening characters to the
endpoint categories: [9-A] includes ':' and '@' in code-unit order. -/
theorem cross_category_literal_range_includes_intermediate_punctuation :
    parse (text "^[9-A]+$") = some (anchoredPlus 57 65) ∧
    execute (code 57 65) [57, 58, 64, 65] = .matched ⟨0, 4, []⟩ ∧
    execute (code 57 65) [66] = .noMatch := by decide

theorem reversed_unsafe_and_unsupported_source_grammar_rejects :
    (["^[9-0]+$", "^[a-0]+$", "^[.-9]+$", "^[0-~]+$", "[0-9]+$", "^[0-9]+", "^[0-9]*$",
      "^[0-9]$", "^[0-9]+$g", "^[0-9]{1,}$", "^([0-9])+$", "^[0-9]+$extra", "^[0-9]+$\n"] : List String).all
      (fun source => (parse (text source)).isNone) = true ∧
    parse [94, 91, 55296, 45, 56320, 93, 43, 36] = none := by decide

/-- An exhausted budget is not silently a negative regex result. The default
linear budget is proved sufficient for every finite canonical input. -/
theorem resource_exhaustion_is_distinct_and_nullable_plus_is_not_compiled :
    run 0 (code 48 57) 0 [49] = .exhausted ∧
    run 3 (code 48 57) 0 [49, 50] = .exhausted ∧
    execute (code 48 57) [49, 50] = .matched ⟨0, 2, []⟩ ∧
    compile (.plus .start) = none ∧ compile (.plus (.sequence .start .finish)) = none := by decide

theorem assertions_are_real_instruction_checks :
    run 16 (code 48 57) 1 [49, 50] = .noMatch ∧
    run 16 [.assertEnd, .accept] 0 [49] = .noMatch ∧
    run 16 [.consumeRange 48 57, .accept] 0 [] = .noMatch := by decide

theorem every_success_has_exact_span_and_empty_captures (lower upper : UInt16) (input : JSString) (result : Match)
    (matched : execute (code lower upper) input = .matched result) :
    result.start = 0 ∧ result.stop = input.length ∧ result.captures = [] ∧ input ≠ [] := by
  obtain ⟨accepted, rfl⟩ := (execute_matched_iff lower upper input result).mp matched
  exact ⟨rfl, rfl, rfl, accepted.1⟩

/-- info: 'HonoLean.Upstream.ECMA2025.RangeRegExp.parse_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parse_iff
/-- info: 'HonoLean.Upstream.ECMA2025.RangeRegExp.parsed_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parsed_execution
/-- info: 'HonoLean.Upstream.ECMA2025.RangeRegExp.execute_anchoredPlus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms execute_anchoredPlus
/-- info: 'HonoLean.Upstream.ECMA2025.RangeRegExp.execute_ne_exhausted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms execute_ne_exhausted

end HonoLean.Upstream.ECMA2025.RangeRegExp.Checks
