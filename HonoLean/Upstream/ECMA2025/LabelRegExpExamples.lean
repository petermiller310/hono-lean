import HonoLean.Upstream.ECMA2025.LabelRegExpRules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.ECMA2025.LabelRegExpChecks
open SourceSubset LabelRegExp

private def text (value : String) : JSString := value.toList.map (fun unit => UInt16.ofNat unit.toNat)
private def captures (input : JSString) : Outcome × List (Option JSString) :=
  let result := execute labelCode input
  (result, match result with | .matched matched => matched.captures.map (extractCapture input) | _ => [])
private def runLiteral (literal input : String) : Option Outcome :=
  (parseLiteral (text literal)).map (fun ast => execute (compile ast) (text input))

/-- The actual29B literal has two captures and is structurally parsed/compiled. -/
theorem actual_literal_parser_and_capture_slots :
    parseLiteral labelLiteral = some labelSyntax ∧ captureSlots labelCode = 2 := by
  constructor
  · exact parse_actual
  · cbv

/-- Absent optional capture stays None; its downstream array cell is a
separate source materialization obligation, not a hole/null introduced here. -/
theorem absent_capture_and_basic_misses :
    captures [58, 105, 100] = (.matched ⟨0, 3, [some (1, 3), none]⟩, [some [105, 100], none]) ∧
    execute labelCode [58, 105, 100, 123, 125] = .noMatch ∧
    execute labelCode [58, 123, 97, 125] = .noMatch ∧
    execute labelCode [58] = .noMatch ∧ execute labelCode [] = .noMatch := by cbv

/-- Greedy body includes inner braces; the final outer brace is not captured. -/
theorem greedy_inner_braces_and_backtracking :
    captures [58, 105, 100, 123, 97, 125, 123, 98, 125] =
      (.matched ⟨0, 9, [some (1, 3), some (4, 8)]⟩, [some [105, 100], some [97, 125, 123, 98]]) := by cbv

/-- Names accept the complete UTF16 domain except braces, including NUL, lone
surrogate and all four line terminators; this never sanitizes a label. -/
theorem raw_utf16_name_with_line_terminators :
    captures [58, 0, 55296, 10, 13, 8232, 8233, 233] =
      (.matched ⟨0, 8, [some (1, 8), none]⟩, [some [0, 55296, 10, 13, 8232, 8233, 233], none]) := by cbv

/-- Dot excludes exactly LF/CR/LS/PS; VT, FF, NEL and lone surrogates survive. -/
theorem body_line_terminators_and_other_units :
    ([10, 13, 8232, 8233] : JSString).all (fun unit => execute labelCode [58, 105, 123, unit, 125] == .noMatch) = true ∧
    captures [58, 105, 123, 11, 12, 133, 55296, 125] =
      (.matched ⟨0, 8, [some (1, 2), some (3, 7)]⟩, [some [105], some [11, 12, 133, 55296]]) := by cbv

/-- Label matching is prior to later RegExp construction. Raw invalid future
patterns '[' and '(' remain perfectly valid captured body strings. -/
theorem raw_invalid_future_regexp_bodies_still_match :
    captures [58, 105, 123, 91, 125] =
      (.matched ⟨0, 5, [some (1, 2), some (3, 4)]⟩, [some [105], some [91]]) ∧
    captures [58, 105, 123, 40, 125] =
      (.matched ⟨0, 5, [some (1, 2), some (3, 4)]⟩, [some [105], some [40]]) := by cbv

/-- Genuine code alternatives snapshot capture state: an optional attempt
saves capture0 before failing its final b, then skip restores None. -/
theorem failed_optional_attempt_restores_capture_snapshot :
    execute (.sequence (.optional (.sequence (.saveBegin 0)
      (.sequence (.test (.literal 97)) (.sequence (.saveEnd 0) (.test (.literal 98))))))
      (.test (.literal 97))) [97] = .matched ⟨0, 1, [none]⟩ := by cbv

/-- Greedyplus actually generates longest-first alternatives and tries a
suffix. It consumes the final brace, backtracks one, then the suffix matches. -/
theorem actual_greedy_candidate_order_and_suffix_retry :
    (greedySplits .dot [97, 125, 98]).map (fun part => part.1.length) = [3, 2, 1] ∧
    execute (.sequence (.greedyPlus .dot) (.test (.literal 125))) [97, 125, 98, 125] =
      .matched ⟨0, 4, []⟩ := by cbv

/-- Structural parsed mutations exercise real instructions/capture numbering;
no source equality switch recognizes the canonical text. -/
theorem parsed_prefix_optional_capture_and_class_mutations :
    runLiteral "/^\\@([^\\{\\}]+)(?:\\{(.+)\\})?$/" "@id" =
      some (.matched ⟨0, 3, [some (1, 3), none]⟩) ∧
    runLiteral "/^\\:([^\\{\\}]+)(?:\\{(.+)\\})$/" ":id" = some .noMatch ∧
    runLiteral "/^\\:(?:[^\\{\\}]+)(?:\\{(.+)\\})?$/" ":id{x}" =
      some (.matched ⟨0, 6, [some (4, 5)]⟩) ∧
    runLiteral "/^\\:([^\\{\\}]+)(?:\\{([^\\{\\}]+)\\})?$/" ":id{a}{b}" = some .noMatch ∧
    runLiteral "/^\\:([^\\{\\}X]+)(?:\\{(.+)\\})?$/" ":idX" = some .noMatch := by cbv

/-- Unsupported full grammar/flags and syntactically invalid quantified raw
assertions fail closed; optional groups containing assertions remain distinct. -/
theorem parser_frontiers_and_invalid_assertion_quantifiers :
    (["/^?$/", "/$?/", "/^:a*$/", "/^:a|b$/", "/(?=a)/", "/[a-z]/", "/^:a$/g", "/\\d+/", "/^:a$"] |>.all
      (fun literal => (parseLiteral (text literal)).isNone)) = true := by cbv

/-- Symbolic arbitrary UTF16 names/bodies; primitive hypotheses concern only
input language, never execution/capture output or a precomputed result array. -/
theorem arbitrary_label_captures (name body : JSString) (validName : Name name) (validBody : Body body) :
    execute labelCode (58 :: (name ++ 123 :: (body ++ [125]))) = .matched (labelMatch name (some body)) ∧
    (labelMatch name (some body)).captures.map (extractCapture (58 :: (name ++ 123 :: (body ++ [125])))) =
      [some name, some body] := by
  have valid : Label (58 :: (name ++ 123 :: (body ++ [125]))) name (some body) := ⟨validName, validBody, rfl⟩
  exact ⟨execute_label_hit _ name _ valid, label_capture_values _ name _ valid⟩

/-- RepeatMatcher(min0) rejects a successful empty attempt, so a valid empty
capture under '?' is ABSENT rather than the empty string. This source remains
admitted; the real VM zero-progress rule supplies the result. -/
theorem nullable_optional_empty_capture_restores_original_snapshot :
    runLiteral "/^()?$/" "" = some (.matched ⟨0, 0, [none]⟩) ∧
    runLiteral "/^(a?)?$/" "" = some (.matched ⟨0, 0, [none]⟩) ∧
    runLiteral "/^(a?)?$/" "a" = some (.matched ⟨0, 1, [some (0, 1)]⟩) := by cbv

/-- Nested nullable attempts discard all their capture changes; conversely an
empty inner capture remains present if its containing optional consumes 'a'. -/
theorem nested_nullable_optional_and_consuming_parent_captures :
    runLiteral "/^(())?$/" "" = some (.matched ⟨0, 0, [none, none]⟩) ∧
    runLiteral "/^((a)?)?$/" "" = some (.matched ⟨0, 0, [none, none]⟩) ∧
    runLiteral "/^(()a)?$/" "a" = some (.matched ⟨0, 1, [some (0, 1), some (0, 0)]⟩) := by cbv

/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.parse_label_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parse_label_sound
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.greedySplits_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms greedySplits_mem
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.greedySplits_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms greedySplits_ordered
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.execute_label_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_label_iff
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.execute_label_miss_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms execute_label_miss_iff
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.label_capture_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms label_capture_values
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.match_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms match_unique
/-- info: 'HonoLean.Upstream.ECMA2025.LabelRegExp.execute_ne_exhausted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_ne_exhausted

end HonoLean.Upstream.ECMA2025.LabelRegExpChecks
