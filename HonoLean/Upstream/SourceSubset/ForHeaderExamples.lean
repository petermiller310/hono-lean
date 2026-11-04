import HonoLean.Upstream.SourceSubset.ForHeader

namespace HonoLean.Upstream.SourceSubset.ForHeaderChecks

open ECMA2025
set_option maxRecDepth 65536

private def outer : ForHeader :=
  ⟨[("i", .number 0)], .compare .less (.variable "i") (.variable "len"), "i"⟩
private def inner : ForHeader :=
  ⟨[("j", .number 0), ("len2", .property (.variable "curNodes") [108, 101, 110, 103, 116, 104])],
    .compare .less (.variable "j") (.variable "len2"), "j"⟩
private def before : State :=
  {environment := [("i", .number 77), ("len", .number 2), ("keep", .number 9)]
   heap := [[.number 8], []]
   objects := [emptyNullObject, emptyNullObject]
   functions := [⟨⟨"old", .number 5⟩, []⟩]
   sets := [[[97]]]
   privates := ⟨[("held", 1)], [(0, [(1, .data (.number 3))])]⟩}

theorem parses_actual_header_shapes_only :
    parseForHeader "for (let i = 0; i < len; i++) {" ["len"] = some outer ∧
    parseForHeader "for (let j = 0, len2 = curNodes.length; j < len2; j++) {" ["curNodes"] = some inner ∧
    (parseForHeader "for (let i = 0; i < len; i++) {}" ["len"]).isNone = true ∧
    (parseForHeader "for (let i = 0; i < len; i++) { body() }" ["len", "body"]).isNone = true := by
  cbv
  exact ⟨rfl, rfl, trivial⟩

theorem postfix_line_terminators_and_maximal_munch :
    (parseForHeader "for (let i = 0; i < len; i\n++) {" ["len"]).isNone = true ∧
    parseForHeader "for (let i = 0; i < len; i++\r\n)\n{\n" ["len"] = some outer ∧
    (parseForHeader "for (let i = 0; i < len; i--) {" ["len"]).isNone = true ∧
    (parseForHeader "for (let i = 0; i < len; ++i) {" ["len"]).isNone = true := by
  cbv
  exact ⟨rfl, trivial⟩

theorem malformed_headers_and_lexical_writes_reject :
    (["for (; i < len; i++) {", "for (let i = 0; ; i++) {", "for (let i = 0; i < len;) {",
      "for (let i = 0 i < len; i++) {", "for (let i = 0; i < len i++) {",
      "for (let i = 0; i < len; other++) {", "for (let i of values) {", "for (let i in values) {",
      "for (let i = 0, i = 1; i < len; i++) {", "for (let i = ++other; i < len; i++) {",
      "for (let i = 0; ++i < len; i++) {", "for (let i = f(len); i < len; i++) {"].all
      (fun source => (parseForHeader source ["len", "other", "values", "f"]).isNone)) = true := by cbv

theorem all_new_names_obey_tdz_and_sequential_scope :
    (parseForHeader "for (let i = i; i < len; i++) {" ["i", "len"]).isNone = true ∧
    (parseForHeader "for (let i = later, later = 0; i < len; i++) {" ["later", "len"]).isNone = true ∧
    (parseForHeader "for (let i = 0, later = i; i < len; i++) {" ["later", "i", "len"]).isSome = true := by cbv

theorem entering_shadows_old_counter_and_frames_state :
    enterForHeader 32 defaultSplitLimit outer before =
      .ok {before with environment := [("i", .number 0), ("len", .number 2), ("keep", .number 9)]} ∧
    testForHeader 32 defaultSplitLimit outer {before with environment := [("i", .number 0), ("len", .number 0)]} =
      .ok (false, {before with environment := [("i", .number 0), ("len", .number 0)]}) := by cbv

theorem second_initializer_reads_earlier_new_binding :
    enterForHeader 32 defaultSplitLimit
      ⟨[("i", .number 0), ("later", .variable "i")], .compare .less (.variable "i") (.variable "later"), "i"⟩
      {before with environment := [("i", .number 77), ("later", .number 99), ("keep", .number 9)]} =
      .ok {before with environment := [("later", .number 0), ("i", .number 0), ("keep", .number 9)]} := by cbv

/-- No scope-leaving restore occurs: an outer binding changed since entry is
retained. The first matching counter changes, a later shadowed entry does not. -/
theorem advance_changes_one_entry_and_keeps_current_outer_binding :
    advanceForHeader outer {before with environment :=
      [("curNodes", .array 1), ("i", .number 0), ("i", .number 77), ("len", .number 2)]} =
      .ok {before with environment :=
        [("curNodes", .array 1), ("i", .number 1), ("i", .number 77), ("len", .number 2)]} := by cbv

private def step (counter bound : Int) : Except EvalError (Bool × Value × Bool) := do
  let state := {before with environment := [("i", .number counter), ("len", .number bound)]}
  let (first, state) ← testForHeader 32 defaultSplitLimit outer state
  let next ← advanceForHeader outer state
  let counter ← lookupVariable next "i"
  let (last, _) ← testForHeader 32 defaultSplitLimit outer next
  pure (first, counter, last)

theorem signed_and_uint32_last_increment :
    step (-2) (-1) = .ok (true, .number (-1), false) ∧
    step 4294967294 4294967295 = .ok (true, .number 4294967295, false) ∧
    HeaderIncrementDomain (4294967294 : Int) := by
  refine ⟨?_, ?_, uint32_guard_increment_safe 4294967294 4294967295 (by decide) (by decide)⟩ <;> cbv

theorem max_safe_input_alone_is_not_increment_domain :
    ¬ HeaderIncrementDomain 9007199254740991 ∧
    (advanceForHeader outer {before with environment := [("i", .number 9007199254740991)]}).map
      (fun state => state.environment.lookup "i") = .ok (some (.number 9007199254740992)) := by
  constructor
  · unfold HeaderIncrementDomain Arithmetic.SafeInteger Arithmetic.maximumSafeInteger
    omega
  · cbv

private def changedArrayProbe (initial current : List Value) : Except EvalError (Bool × Value × Value) := do
  let state ← enterForHeader 32 defaultSplitLimit inner
    {before with environment := [("curNodes", .array 0)], heap := [initial]}
  let changed := {state with heap := [current]}
  let (guard, after) ← testForHeader 32 defaultSplitLimit inner changed
  let value ← readProperty (.array 0) (.number 0) after
  let saved ← lookupVariable after "len2"
  pure (guard, value, saved)

/-- Header truth reads the SAVED len2. It is neither a current-array bounds
check nor a claim that an arbitrary intervening body preserved that array. -/
theorem saved_length_survives_array_shrink_and_growth :
    changedArrayProbe [.object 0, .object 1] [] = .ok (true, .undefined, .number 2) ∧
    changedArrayProbe [] [.object 0] = .ok (false, .object 0, .number 0) := by
  cbv
  exact ⟨rfl, rfl⟩

/-- General testForHeader keeps actual condition effects, unlike the pure
numeric compare specialization's stronger state-equality contract. -/
theorem condition_effect_is_evaluated_once :
    (testForHeader 32 defaultSplitLimit
      ⟨[("i", .number 0)], .call (.variable "values") "shift" [], "i"⟩
      {before with environment := [("values", .array 0)], heap := [[.number 7, .number 9]]}).map
        (fun result => (result.1, result.2.heap)) = .ok (true, [[.number 9]]) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.advanceForHeader_numeric_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.advanceForHeader_numeric_satisfies

end HonoLean.Upstream.SourceSubset.ForHeaderChecks
