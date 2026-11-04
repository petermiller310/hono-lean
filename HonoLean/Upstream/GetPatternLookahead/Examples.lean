import HonoLean.Upstream.GetPatternLookahead.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternLookahead.Checks
open SourceSubset hiding pinnedSource State
open ECMA2025

private def context : PatternCacheContext := ⟨labelStandardContext⟩
private def prototypeObject : OrdinaryObject := ⟨standardLabelRegExpOwn 9 5, some 0, true⟩
private def seed (input next : JSString) : LookaheadRegExp.State :=
  ⟨cacheWithAmbient (labelStandardState input) {(labelStandardState input).base.regexp.ambient with
    environment := ("next", .string next) :: ("RegExp", .function 6) :: (labelStandardState input).base.regexp.ambient.environment}, []⟩

private theorem seed_coherent (input next : JSString) : LookaheadRegExp.Coherent (seed input next) := by
  constructor
  case allocated =>
    intro entry member
    change entry ∈ [(6, LookaheadRegExp.TaggedRecord.range digitsRecord)] at member
    simp only [List.mem_singleton] at member
    subst entry
    change 6 < 7
    decide
  case unique =>
    change ([6] : List Nat).Nodup
    decide

private theorem seed_realm (input next : JSString) : LabelRealm (seed input next).base labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [seed, cacheWithAmbient, labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < 7
  decide

theorem every_selected_source_domain_is_inhabited (name : JSString) (lower upper : UInt16) (next : JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    Inputs (seed (LabelMatch.safeRangeLabel name lower upper) next) context name lower upper next 6 ⟨2⟩ prototypeObject :=
  ⟨⟨seed_realm _ next, rfl⟩, seed_coherent _ next, validName, safeLower, safeUpper, ordered, safeNext, rfl, rfl, by decide, rfl, rfl⟩

theorem every_constructor_query_domain_has_a_verified_execution (lower upper : UInt16) (next query : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    let before := seed [] next
    let constructed := LookaheadRegExp.constructedState before 2 (LookaheadRegExp.compiledRecord lower upper next)
    ∃ returned after,
      LookaheadRegExp.invokeConstructor labelStandardOldContext (.function 6) (.string (LiteralLookahead.rawSource lower upper next)) before = .ok (.object 7, constructed) ∧
      LookaheadRegExp.invokeExec (.object 7) [.string query] constructed = .ok (returned, after) ∧
      ConstructionContract before constructed (.object 7) 2 lower upper next ∧ ExecContract constructed after returned lower upper next query := by
  apply constructor_then_exec_satisfies (seed [] next) labelStandardOldContext 6 ⟨2⟩ prototypeObject lower upper next query
  exact ⟨seed_coherent [] next, by change 1 ≤ 6; decide, by change 2 ≤ 6; decide,
    by change 3 ≤ 6; decide, by change 5 ≤ 6; decide, by change 6 ≤ 6; decide,
    by decide, rfl, rfl, safeLower, safeUpper, ordered, safeNext⟩

/-- These source-level witnesses begin before the actual label declaration;
no successful capture, key, tuple or matcher is supplied as a premise. -/
theorem every_selected_source_query_has_a_verified_execution (name : JSString) (lower upper : UInt16) (next query : JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    let before := seed (LabelMatch.safeRangeLabel name lower upper) next
    ∃ returned after,
      sourceSelectedExec 256 context before query = some (.ok (returned, after)) ∧
      ExecContract (selectedState before context name lower upper next 2) after returned lower upper next query := by
  obtain ⟨returned, after, _, executed, _, result⟩ := source_selected_exec_satisfies 0 _ context name lower upper next query 6 ⟨2⟩ prototypeObject
    (every_selected_source_domain_is_inhabited name lower upper next validName safeLower safeUpper ordered safeNext)
  exact ⟨returned, after, executed, result⟩

theorem source_query_returns_only_the_range_prefix (name : JSString) (lower upper : UInt16) (next taken suffix : JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next)
    (nonempty : taken ≠ []) (inside : ∀ unit ∈ taken, RangeRegExp.InRange lower upper unit) :
    let before := seed (LabelMatch.safeRangeLabel name lower upper) next
    let produced := selectedState before context name lower upper next 2
    sourceSelectedExec 256 context before (taken ++ (47 :: next ++ suffix)) =
      some (.ok (.array produced.base.base.regexp.ambient.heap.length,
        prefixState produced (taken ++ (47 :: next ++ suffix)) taken)) := by
  obtain ⟨returned, after, executed, result⟩ := every_selected_source_query_has_a_verified_execution name lower upper next
    (taken ++ (47 :: next ++ suffix)) validName safeLower safeUpper ordered safeNext
  obtain ⟨value, state⟩ := exec_contract_exact_prefix _ _ returned lower upper next taken suffix safeLower nonempty inside result
  rw [value, state] at executed
  exact executed

theorem source_query_rejection_preserves_constructed_state (name : JSString) (lower upper : UInt16) (next query : JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next)
    (absent : ¬ LiteralLookahead.Accepted lower upper next query) :
    let before := seed (LabelMatch.safeRangeLabel name lower upper) next
    sourceSelectedExec 256 context before query =
      some (.ok (.null, selectedState before context name lower upper next 2)) := by
  obtain ⟨returned, after, executed, result⟩ := every_selected_source_query_has_a_verified_execution name lower upper next query
    validName safeLower safeUpper ordered safeNext
  obtain ⟨value, state⟩ := exec_contract_rejects _ _ returned lower upper next query absent result
  rw [value, state] at executed
  exact executed

private def text (value : String) : JSString := value.toList.map (fun unit => UInt16.ofNat unit.toNat)

theorem actual_source_abc_tails_returns_abc :
    let before := seed (LabelMatch.safeRangeLabel (text "id") 97 122) (text "tail")
    let produced := selectedState before context (text "id") 97 122 (text "tail") 2
    sourceSelectedExec 256 context before (text "abc/tails") =
      some (.ok (.array produced.base.base.regexp.ambient.heap.length,
        prefixState produced (text "abc/tails") (text "abc"))) := by
  exact source_query_returns_only_the_range_prefix (text "id") 97 122 (text "tail") (text "abc") (text "s")
    (by simp [LabelRegExp.Name, text]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem actual_source_incomplete_assertion_returns_null :
    let before := seed (LabelMatch.safeRangeLabel (text "id") 97 122) (text "tail")
    sourceSelectedExec 256 context before (text "abc/tai") =
      some (.ok (.null, selectedState before context (text "id") 97 122 (text "tail") 2)) := by
  apply source_query_rejection_preserves_constructed_state (text "id") 97 122 (text "tail") (text "abc/tai")
    (by simp [LabelRegExp.Name, text]) (by decide) (by decide) (by decide) (by decide)
  exact (LiteralLookahead.execute_noMatch_iff 97 122 (text "tail") (text "abc/tai") (by decide)).mp (by
    rw [LiteralLookahead.execute_scanned]
    decide)

theorem actual_source_empty_range_prefix_returns_null :
    let before := seed (LabelMatch.safeRangeLabel (text "id") 97 122) (text "tail")
    sourceSelectedExec 256 context before (text "/tail") =
      some (.ok (.null, selectedState before context (text "id") 97 122 (text "tail") 2)) := by
  apply source_query_rejection_preserves_constructed_state (text "id") 97 122 (text "tail") (text "/tail")
    (by simp [LabelRegExp.Name, text]) (by decide) (by decide) (by decide) (by decide)
  exact (LiteralLookahead.execute_noMatch_iff 97 122 (text "tail") (text "/tail") (by decide)).mp (by
    rw [LiteralLookahead.execute_scanned]
    decide)

/-- info: 'HonoLean.Upstream.GetPatternLookahead.parses_source_body_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.parses_source_body_nodes

/-- info: 'HonoLean.Upstream.GetPatternLookahead.constructor_then_exec_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.constructor_then_exec_satisfies

/-- info: 'HonoLean.Upstream.GetPatternLookahead.source_selected_tuple_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.source_selected_tuple_satisfies

/-- info: 'HonoLean.Upstream.GetPatternLookahead.source_selected_exec_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.source_selected_exec_satisfies

/-- info: 'HonoLean.Upstream.GetPatternLookahead.Checks.actual_source_abc_tails_returns_abc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.Checks.actual_source_abc_tails_returns_abc

/-- info: 'HonoLean.Upstream.GetPatternLookahead.Checks.actual_source_incomplete_assertion_returns_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HonoLean.Upstream.GetPatternLookahead.Checks.actual_source_incomplete_assertion_returns_null

end HonoLean.Upstream.GetPatternLookahead.Checks
