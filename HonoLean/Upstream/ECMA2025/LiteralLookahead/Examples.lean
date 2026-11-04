import HonoLean.Upstream.ECMA2025.LiteralLookahead.Correctness

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

private def text (value : String) : JSString := value.toList.map (fun unit => UInt16.ofNat unit.toNat)

/-- Every admitted endpoint/next combination has a concrete one-unit consumed
match. This uses the general proof, without replaying a whole closed VM. -/
theorem every_admitted_pattern_is_inhabited (lower upper : UInt16) (next : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : SafeNext next) :
    parse (rawSource lower upper next) = some (pattern lower upper next) ∧
    compile (pattern lower upper next) = some (code lower upper next) ∧
    execute (code lower upper next) (lower :: 47 :: next) = .matched ⟨0, 1, []⟩ := by
  refine ⟨parse_complete _ _ (.lookahead lower upper next safeLower safeUpper ordered safeNext),
    compile_pattern lower upper next, ?_⟩
  apply (execute_matched_iff lower upper next _ _ safeLower).mpr
  refine ⟨[lower], [], by simp, by simp, ?_, rfl⟩
  intro unit member
  have equal : unit = lower := by simpa using member
  subst unit
  exact ⟨Nat.le_refl _, ordered⟩

/-- The complete next literal is asserted, but any following suffix remains
admitted—including line terminators and unpaired UTF16 surrogate units. -/
theorem arbitrary_suffix_is_not_consumed (lower upper : UInt16) (next taken suffix : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (nonempty : taken ≠ [])
    (inside : ∀ unit ∈ taken, RangeRegExp.InRange lower upper unit) :
    execute (code lower upper next) (taken ++ (47 :: next ++ suffix)) = .matched ⟨0, taken.length, []⟩ := by
  exact (execute_matched_iff lower upper next _ _ safeLower).mpr ⟨taken, suffix, rfl, nonempty, inside, rfl⟩

theorem literal_assertion_child_and_parent_have_different_spans :
    runLiteral (0 + (text "/tailX").length + 1) (literalCode (text "/tail") ++ [.accept]) 3 (text "/tailX") =
      .matched ⟨0, 8, []⟩ ∧
    run (0 + (text "/tailX").length + 2) [.positive (literalCode (text "/tail") ++ [.accept]), .accept] 3 (text "/tailX") =
      .matched ⟨0, 3, []⟩ := by
  exact positive_literal_nonconsuming 0 3 (text "/tail") (text "X")

theorem next_does_not_require_an_ending_boundary :
    execute (code 97 122 (text "tail")) (text "abc/tailX") = .matched ⟨0, 3, []⟩ := by
  apply arbitrary_suffix_is_not_consumed 97 122 (text "tail") (text "abc") (text "X") (by decide) (by decide) (by decide)

theorem suffix_may_contain_line_terminators_and_surrogates :
    execute (code 97 122 (text "tail")) (text "a/tail" ++ [10, 13, 8232, 8233, 55296, 65535]) =
      .matched ⟨0, 1, []⟩ := by
  exact arbitrary_suffix_is_not_consumed 97 122 (text "tail") [97] [10,13,8232,8233,55296,65535]
    (by decide) (by decide) (by decide)

/-- Endpoint safety restricts the endpoints, not every intermediate unit.
The valid 9-A range includes ':' and '@'; slash still lies below the range. -/
theorem cross_gap_range_consumes_punctuation :
    execute (code 57 65 [120]) [58,64,47,120,65535] = .matched ⟨0, 2, []⟩ := by
  exact arbitrary_suffix_is_not_consumed 57 65 [120] [58,64] [65535] (by decide) (by decide) (by decide)

theorem incomplete_assertion_does_not_match :
    execute (code 97 122 (text "tail")) (text "abc/tai") = .noMatch := by
  rw [execute_scanned]
  decide

theorem quantifier_still_requires_a_nonempty_range_prefix :
    execute (code 97 122 (text "tail")) (text "/tail") = .noMatch := by
  rw [execute_scanned]
  decide

theorem wrong_unit_before_slash_does_not_match :
    execute (code 97 122 (text "tail")) (text "abcX/tail") = .noMatch := by
  rw [execute_scanned]
  decide

theorem constructor_input_and_display_are_distinct :
    rawSource 97 122 (text "tail") = text "^[a-z]+(?=/tail)" ∧
    displaySource 97 122 (text "tail") = text "^[a-z]+(?=\\/tail)" ∧
    rawSource 97 122 (text "tail") ≠ displaySource 97 122 (text "tail") := by decide

theorem unsupported_next_shapes_are_rejected :
    parse (rawSource 97 122 []) = none ∧
    parse (rawSource 97 122 [46]) = none ∧
    parse (rawSource 97 122 [47]) = none ∧
    parse (rawSource 97 122 [10]) = none := by decide

theorem unsupported_regex_forms_are_rejected :
    parse (text "^[a-z]+(?:/tail)") = none ∧
    parse (text "^[a-z]+(?=/tail)$") = none ∧
    parse (text "^[z-a]+(?=/tail)") = none ∧
    parse (text "^[a-z]+(?=/tail)g") = none := by decide

#guard (parse (text "^[a-z]+(?=/tail)")).isSome
#guard (parse (text "^[0-9]+(?=/A1)")).isSome
#guard (parse (text "^[9-A]+(?=/X)")).isSome
#guard (parse (text "^[a-z]+(?=/)")).isNone
#guard (parse (text "^[a-z]+(?=/a.b)")).isNone
#guard (parse (text "^[a-z]+(?:/tail)")).isNone

end HonoLean.Upstream.ECMA2025.LiteralLookahead
