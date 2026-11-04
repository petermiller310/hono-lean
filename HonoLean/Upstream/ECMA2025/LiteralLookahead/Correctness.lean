import HonoLean.Upstream.ECMA2025.LiteralLookahead.VM

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

theorem safeEndpoint_lower_bound (unit : UInt16) (safe : RangeRegExp.SafeEndpoint unit) : 48 ≤ unit.toNat := by
  rcases safe with digits | upper | lower <;> omega

theorem slash_not_in_range (lower upper : UInt16) (safe : RangeRegExp.SafeEndpoint lower) :
    ¬ RangeRegExp.InRange lower upper 47 := by
  have bound := safeEndpoint_lower_bound lower safe
  intro inside
  have impossible := inside.1
  change lower.toNat ≤ 47 at impossible
  omega

theorem run_literal (extra cursor : Nat) (literal input : JSString) :
    runLiteral (extra + input.length + 1) (literalCode literal ++ [.accept]) cursor input =
      if literal.isPrefixOf input then .matched ⟨0, cursor + literal.length, []⟩ else .noMatch := by
  induction literal generalizing cursor input with
  | nil => simp [literalCode, runLiteral]
  | cons expected rest ih =>
    cases input with
    | nil => simp [literalCode, runLiteral]
    | cons unit tail =>
      have budget : extra + (unit :: tail).length + 1 = (extra + tail.length + 1) + 1 := by simp; omega
      rw [budget]
      by_cases same : unit = expected
      · subst unit
        simpa [literalCode, runLiteral, List.isPrefixOf, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (cursor + 1) tail
      · have different : (unit == expected) = false := beq_eq_false_iff_ne.mpr same
        have reverse : (expected == unit) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        simp [literalCode, runLiteral, different, reverse, List.isPrefixOf]

theorem run_positive_literal (extra cursor : Nat) (literal input : JSString) :
    run (extra + input.length + 2) [.positive (literalCode literal ++ [.accept]), .accept] cursor input =
      if literal.isPrefixOf input then .matched ⟨0, cursor, []⟩ else .noMatch := by
  have budget : extra + input.length + 2 = (extra + input.length + 1) + 1 := by omega
  rw [budget, run, run_literal extra cursor literal input]
  cases assertion : literal.isPrefixOf input <;>
    simp only [Bool.false_eq_true, ↓reduceIte, run]

/-- The child consumes its literal internally; a successful positive assertion
returns the parent's original cursor and leaves the suffix available. -/
theorem positive_literal_nonconsuming (extra cursor : Nat) (literal suffix : JSString) :
    runLiteral (extra + (literal ++ suffix).length + 1) (literalCode literal ++ [.accept]) cursor (literal ++ suffix) =
      .matched ⟨0, cursor + literal.length, []⟩ ∧
    run (extra + (literal ++ suffix).length + 2) [.positive (literalCode literal ++ [.accept]), .accept] cursor (literal ++ suffix) =
      .matched ⟨0, cursor, []⟩ := by
  rw [run_literal, run_positive_literal]
  simp

theorem scanRange_spec (lower upper : UInt16) (input : JSString) :
    input = (scanRange lower upper input).1 ++ (scanRange lower upper input).2 ∧
      ∀ unit ∈ (scanRange lower upper input).1, RangeRegExp.InRange lower upper unit := by
  induction input with
  | nil => simp [scanRange]
  | cons unit rest ih =>
    by_cases inside : RangeRegExp.InRange lower upper unit
    · cases scanned : scanRange lower upper rest with
      | mk taken suffix =>
        simp only [scanned] at ih
        exact ⟨by simpa [scanRange, inside, scanned] using congrArg (unit :: ·) ih.1,
          by simpa [scanRange, inside, scanned, List.mem_cons] using And.intro inside ih.2⟩
    · simp [scanRange, inside]

theorem scanRange_delimited (lower upper : UInt16) (taken next suffix : JSString)
    (outside : ¬ RangeRegExp.InRange lower upper 47)
    (all : ∀ unit ∈ taken, RangeRegExp.InRange lower upper unit) :
    scanRange lower upper (taken ++ (47 :: next ++ suffix)) = (taken, 47 :: next ++ suffix) := by
  induction taken with
  | nil => simp [scanRange, outside]
  | cons unit rest ih =>
    have inside := all unit (by simp)
    have remaining : ∀ value ∈ rest, RangeRegExp.InRange lower upper value := fun value member => all value (by simp [member])
    have tail := ih remaining
    simp only [List.cons_append] at tail
    simp only [List.cons_append, scanRange, ite_eq_left inside]
    rw [tail]

theorem run_repeat (extra cursor : Nat) (lower upper : UInt16) (next input : JSString) :
    run (extra + input.length + 4)
      [.repeatRange lower upper, .positive (literalCode (47 :: next) ++ [.accept]), .accept] cursor input =
      if (47 :: next).isPrefixOf (scanRange lower upper input).2 then
        .matched ⟨0, cursor + (scanRange lower upper input).1.length, []⟩ else .noMatch := by
  induction input generalizing cursor with
  | nil => simp [run, runLiteral, literalCode, scanRange]
  | cons unit rest ih =>
    by_cases inside : RangeRegExp.InRange lower upper unit
    · have budget : extra + (unit :: rest).length + 4 = (extra + rest.length + 4) + 1 := by simp; omega
      rw [budget, run, ite_eq_left inside]
      simpa [scanRange, inside, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (cursor + 1)
    · have budget : extra + (unit :: rest).length + 4 = ((extra + 1) + (unit :: rest).length + 2) + 1 := by omega
      rw [budget, run, ite_eq_right inside]
      simpa [scanRange, inside] using run_positive_literal (extra + 1) cursor (47 :: next) (unit :: rest)

theorem execute_scanned (lower upper : UInt16) (next input : JSString) :
    execute (code lower upper next) input =
      if (scanRange lower upper input).1.isEmpty then .noMatch else
      if (47 :: next).isPrefixOf (scanRange lower upper input).2 then
        .matched ⟨0, (scanRange lower upper input).1.length, []⟩ else .noMatch := by
  cases input with
  | nil => simp [execute, code, run, scanRange]
  | cons unit rest =>
    by_cases inside : RangeRegExp.InRange lower upper unit
    · have budget : (unit :: rest).length + 8 = (3 + rest.length + 4) + 2 := by simp; omega
      rw [execute, budget]
      simp only [code]
      rw [run, ite_eq_left rfl, run, ite_eq_left inside]
      simpa [scanRange, inside, Nat.add_comm] using run_repeat 3 1 lower upper next rest
    · simp [execute, code, run, inside, scanRange]

theorem execute_ne_exhausted (lower upper : UInt16) (next input : JSString) :
    execute (code lower upper next) input ≠ .exhausted := by
  rw [execute_scanned]
  split
  · simp
  · split <;> simp

theorem execute_matched_iff (lower upper : UInt16) (next input : JSString) (result : Match)
    (safeLower : RangeRegExp.SafeEndpoint lower) :
    execute (code lower upper next) input = .matched result ↔ Matches lower upper next input result := by
  constructor
  · intro evaluated
    rw [execute_scanned] at evaluated
    split at evaluated
    · cases evaluated
    · rename_i nonempty
      split at evaluated
      · rename_i assertion
        have shape := (scanRange_spec lower upper input).1
        have all := (scanRange_spec lower upper input).2
        obtain ⟨suffix, suffixEq⟩ := List.isPrefixOf_iff_prefix.mp assertion
        refine ⟨(scanRange lower upper input).1, suffix, ?_, ?_, all, ?_⟩
        · exact shape.trans (congrArg ((scanRange lower upper input).1 ++ ·) suffixEq.symm)
        · simpa using nonempty
        · exact (RangeRegExp.Outcome.matched.inj evaluated).symm
      · cases evaluated
  · intro relation
    obtain ⟨taken, suffix, shape, nonempty, all, rfl⟩ := relation
    rw [shape, execute_scanned, scanRange_delimited lower upper taken next suffix (slash_not_in_range lower upper safeLower) all]
    simp [nonempty]

theorem matches_accepted (lower upper : UInt16) (next input : JSString) (result : Match)
    (matched : Matches lower upper next input result) : Accepted lower upper next input := by
  obtain ⟨taken, suffix, shape, nonempty, all, _⟩ := matched
  exact ⟨taken, suffix, shape, nonempty, all⟩

theorem accepted_iff_matches (lower upper : UInt16) (next input : JSString) :
    Accepted lower upper next input ↔ ∃ result, Matches lower upper next input result := by
  constructor
  · rintro ⟨taken, suffix, shape, nonempty, all⟩
    exact ⟨⟨0, taken.length, []⟩, taken, suffix, shape, nonempty, all, rfl⟩
  · rintro ⟨result, matched⟩
    exact matches_accepted lower upper next input result matched

theorem execute_noMatch_iff (lower upper : UInt16) (next input : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) :
    execute (code lower upper next) input = .noMatch ↔ ¬ Accepted lower upper next input := by
  constructor
  · intro failed accepted
    obtain ⟨result, matched⟩ := (accepted_iff_matches lower upper next input).mp accepted
    have successful := (execute_matched_iff lower upper next input result safeLower).mpr matched
    cases failed.symm.trans successful
  · intro absent
    cases evaluated : execute (code lower upper next) input with
    | exhausted => exact False.elim (execute_ne_exhausted lower upper next input evaluated)
    | noMatch => rfl
    | matched result =>
      exact False.elim (absent (matches_accepted lower upper next input result
        ((execute_matched_iff lower upper next input result safeLower).mp evaluated)))

theorem matches_unique (lower upper : UInt16) (next input : JSString) (first second : Match)
    (safeLower : RangeRegExp.SafeEndpoint lower) (one : Matches lower upper next input first)
    (two : Matches lower upper next input second) : first = second := by
  have same := ((execute_matched_iff lower upper next input first safeLower).mpr one).symm.trans
    ((execute_matched_iff lower upper next input second safeLower).mpr two)
  exact RangeRegExp.Outcome.matched.inj same

theorem escape_safe_units (units : JSString) (safe : ∀ unit ∈ units, RangeRegExp.SafeEndpoint unit) :
    escapeSlashes units = units := by
  induction units with
  | nil => rfl
  | cons unit rest ih =>
    have bound := safeEndpoint_lower_bound unit (safe unit (by simp))
    have different : unit ≠ 47 := by intro equal; subst unit; contradiction
    have remaining : ∀ value ∈ rest, RangeRegExp.SafeEndpoint value := fun value member => safe value (by simp [member])
    have tail := ih remaining
    unfold escapeSlashes at tail ⊢
    simp only [List.flatMap_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte]
    rw [tail]
    rfl

theorem escape_append (left right : JSString) : escapeSlashes (left ++ right) = escapeSlashes left ++ escapeSlashes right := by
  simp [escapeSlashes]

theorem raw_source_display (lower upper : UInt16) (next : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper) (safeNext : SafeNext next) :
    escapeSlashes (rawSource lower upper next) = displaySource lower upper next := by
  have lowerDifferent : lower ≠ 47 := by
    intro equal; subst lower; have impossible := safeEndpoint_lower_bound 47 safeLower; contradiction
  have upperDifferent : upper ≠ 47 := by
    intro equal; subst upper; have impossible := safeEndpoint_lower_bound 47 safeUpper; contradiction
  simp only [rawSource, displaySource, escape_append]
  rw [escape_safe_units next safeNext.2]
  simp [escapeSlashes, lowerDifferent, upperDifferent]

theorem parsed_execution (source : JSString) (ast : Syntax) (parsed : parse source = some ast) :
    ∃ lower upper next, Grammar source (pattern lower upper next) ∧ ast = pattern lower upper next ∧
      compile ast = some (code lower upper next) ∧
      (∀ input result, execute (code lower upper next) input = .matched result ↔ Matches lower upper next input result) ∧
      (∀ input, execute (code lower upper next) input = .noMatch ↔ ¬ Accepted lower upper next input) ∧
      (∀ input, execute (code lower upper next) input ≠ .exhausted) := by
  cases parse_sound source ast parsed with
  | lookahead lower upper next safeLower safeUpper ordered safeNext =>
    exact ⟨lower, upper, next, .lookahead lower upper next safeLower safeUpper ordered safeNext, rfl,
      compile_pattern lower upper next, fun input result => execute_matched_iff lower upper next input result safeLower,
      fun input => execute_noMatch_iff lower upper next input safeLower, execute_ne_exhausted lower upper next⟩

end HonoLean.Upstream.ECMA2025.LiteralLookahead
