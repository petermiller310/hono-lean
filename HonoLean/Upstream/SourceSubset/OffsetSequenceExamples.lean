import HonoLean.Upstream.SourceSubset.OffsetRules

namespace HonoLean.Upstream.SourceSubset.OffsetSequenceChecks

open ECMA2025
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def source := "if (!partOffsets) {\n  partOffsets = []\n  let offset = path[0] === '/' ? 1 : 0\n  for (let p = 0; p < len; p++) {\n    partOffsets[p] = offset\n    offset += parts[p].length + 1\n  }\n}\nconst restPathString = path.slice(partOffsets[i])"
private def bindings := ["partOffsets", "path", "parts", "len", "i"]
private def v (name : String) : OffsetExpr := .ordinary (.variable name)
private def n (value : Nat) : OffsetExpr := .ordinary (.number value)
private def lengthKey : JSString := [108, 101, 110, 103, 116, 104]
private def header : ForHeader := ⟨[("p", .number 0)], .compare .less (.variable "p") (.variable "len"), "p"⟩
private def loopBody : List OffsetStmt :=
  [.assign (.index (v "partOffsets") (v "p")) (v "offset"),
   .addAssign "offset" (.add (.property (.index (v "parts") (v "p")) lengthKey) (n 1))]
private def program : List OffsetStmt :=
  [.branch (.logicalNot (v "partOffsets"))
    [.assign (v "partOffsets") (.ordinary (.arrayLiteral [])),
     .declare true "offset" (.conditional (.strictEqual (.index (v "path") (n 0)) (.ordinary (.string [47]))) (n 1) (n 0)),
     .countedFor header loopBody],
   .declare false "restPathString" (.call (v "path") "slice" [.index (v "partOffsets") (v "i")])]

theorem parses_actual_guard_loop_add_and_compound_assignment :
    parseOffsetSequence source bindings ["partOffsets"] = some program := by cbv

theorem genuine_numeric_precedence_parentheses_and_left_associativity :
    (parseOffsetSequence "const result = 1 + (2 + 3) + 7 === 13 ? 0 : 9" [] []).map
      (fun code => (executeOffsetSequence 64 defaultSplitLimit [] code {}).map (fun state => state.environment.lookup "result")) =
      some (.ok (some (.number 0))) ∧
    (parseOffsetSequence "const result = 1\n+ 2 + 3 < 7 === true ? 4 : 5" [] []).map
      (fun code => (executeOffsetSequence 64 defaultSplitLimit [] code {}).map (fun state => state.environment.lookup "result")) =
      some (.ok (some (.number 4))) := by
  cbv
  exact ⟨rfl, rfl⟩

theorem rejects_const_tdz_callbacks_and_bad_operator_boundaries :
    (["const x = x", "const x = 0\nx += 1", "let x = 0\nx + = 1", "let x = 0\nx++=1",
      "const x = f()", "const x = ++i", "const x = 1 * 2", "const x = 1 + +2", "const x = -0",
      "for (let p = p; p < len; p++) {}", "for (let p = f(); p < len; p++) {}",
      "for (let p = 0; p < len; p\n++) {}", "if (true) { const x = 1", "const x = 1\n(2)"] : List String).all
      (fun text => (parseOffsetSequence text ["i", "p", "len", "f"] ["x"]).isNone) = true := by cbv

private def path : JSString := [47, 55296, 233, 47, 56320, 47]
private def parts : List JSString := [[55296, 233], [56320], []]
private def before : State :=
  {environment := [("partOffsets", .null), ("path", .string path), ("parts", .array 0), ("len", .number 3), ("i", .number 1),
      ("offset", .number 77), ("p", .number 88), ("partOffsets", .array 1)]
   heap := [parts.map Value.string, [.number 99]]
   objects := [emptyNullObject]
   thisValue := .object 0
   functions := [⟨⟨"opaque", .number 7⟩, [("capture", .array 1)]⟩]
   sets := [[[55296]]]
   privates := PrivateStore.ofData [("keep", 7)] [(0, [(7, .array 1)])]}

theorem fresh_loop_uses_utf16_lengths_and_retains_exact_first_cache_binding :
    (parseOffsetSequence source bindings ["partOffsets"]).map
      (fun code => executeOffsetSequence 120 defaultSplitLimit ["partOffsets"] code before) =
    some (.ok {before with
      environment := ("restPathString", .string [56320, 47]) :: before.environment.set 0 ("partOffsets", .array 2)
      heap := [parts.map Value.string, [.number 99], [.number 1, .number 4, .number 6]]}) := by cbv

private def cached : State :=
  {environment := [("partOffsets", .array 0), ("path", .string path), ("i", .number 7), ("p", .number 41), ("offset", .number 42)]
   heap := [[]]}

/-- Truthy [] skips parts/len and every fresh allocation. Its missing cached
index reads undefined, which the actual slice argument maps to start zero. -/
theorem empty_cached_array_skips_all_construction_inputs :
    (parseOffsetSequence source bindings ["partOffsets"]).map
      (fun code => executeOffsetSequence 120 defaultSplitLimit ["partOffsets"] code cached) =
      some (.ok {cached with environment := ("restPathString", .string path) :: cached.environment}) := by cbv

theorem actual_cached_value_controls_slice_without_recomputation :
    (executeOffsetSequence 120 defaultSplitLimit ["partOffsets"] program
      {environment := [("partOffsets", .array 0), ("path", .string path), ("i", .number 0)], heap := [[.number 3]]}).map
      (fun state => (state.environment.lookup "restPathString", state.heap)) =
      .ok (some (.string [47, 56320, 47]), [[.number 3]]) := by cbv

theorem fresh_len_zero_is_a_real_zero_iteration_loop :
    (executeOffsetSequence 120 defaultSplitLimit ["partOffsets"] program
      {environment := [("partOffsets", .null), ("path", .string path), ("len", .number 0), ("i", .number 0),
        ("offset", .number 42), ("p", .number 41)]}).map
      (fun state => (state.environment, state.heap)) =
      .ok ([("restPathString", .string path), ("partOffsets", .array 0), ("path", .string path), ("len", .number 0),
        ("i", .number 0), ("offset", .number 42), ("p", .number 41)], [[]]) := by cbv

theorem compound_assignment_reads_old_first_slot_then_retains_rhs_heap_effects :
    (parseOffsetSequence "offset += values.shift()" ["offset", "values"] ["offset"]).map
      (fun code => executeOffsetSequence 64 defaultSplitLimit ["offset"] code
        {environment := [("offset", .number 5), ("values", .array 0), ("offset", .number 999)], heap := [[.number 3, .number 4]]}) =
    some (.ok {environment := [("offset", .number 8), ("values", .array 0), ("offset", .number 999)], heap := [[.number 4]]}) := by cbv

theorem compound_missing_read_precedes_rhs_but_addition_checks_after_rhs :
    executeOffsetAddAssign 32 defaultSplitLimit ["missing"] "missing" (.call (v "bad") "shift" [])
      {environment := [("bad", .array 9)]} = .error .missingVariable ∧
    evalOffsetExpression 32 defaultSplitLimit (.add (.ordinary (.string [])) (.call (v "bad") "shift" []))
      {environment := [("bad", .array 9)]} = .error .invalidReference := by cbv

/-- Numeric domain guards are interpretation bounds, not ToPrimitive/string
concatenation adequacy. The old source entries remain unchanged. -/
theorem numeric_specialization_and_old_entries_remain_explicit :
    evalOffsetExpression 32 defaultSplitLimit (.add (.ordinary (.string [97])) (n 1)) {} = .error .unsupported ∧
    parseBlock "offset += 1" ["offset"] = none ∧ parseExpression "1 + 2" [] = none ∧
    tokenizeOffsetSequence "offset+=1" = some [.name "offset", .punctuation "+=", .number 1] := by cbv

theorem dense_writes_reject_gaps_but_preserve_existing_other_cells :
    putOffsetReference (.property ⟨.array 0, .number 2⟩) (.number 8) {heap := [[]]} = .error .unsupported ∧
    putOffsetReference (.property ⟨.array 0, .number 0⟩) (.number 8) {heap := [[], [.number 9]]} =
      .ok {heap := [[.number 8], [.number 9]]} := by cbv

theorem safe_bound_is_derived_for_bounded_addends (left right : Nat) (bound : left + right ≤ 4294967295) :
    OffsetArithmetic.ExactAdditionDomain (left : Int) (right : Int) := OffsetArithmetic.uint32_addition_safe left right bound

/-- A true guard executes repeatedly until the explicit model budget runs out.
This is a model fuel control, not a claim that native JS throws this error. -/
theorem constant_loop_guard_is_not_replaced_by_single_execution :
    (parseOffsetSequence "for (let p = 0; true; p++) { partOffsets[0] = 1 }" ["partOffsets"] ["partOffsets"]).map
      (fun code => executeOffsetSequence 16 defaultSplitLimit ["partOffsets"] code
        {environment := [("partOffsets", .array 0)], heap := [[]]}) = some (.error .exhausted) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.executeOffsetAddAssign_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.executeOffsetAddAssign_first
/-- info: 'HonoLean.Upstream.SourceSubset.weaveScoped_rebind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.weaveScoped_rebind
/-- info: 'HonoLean.Upstream.SourceSubset.evalOffset_slice_undefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalOffset_slice_undefined
/-- info: 'HonoLean.Upstream.SourceSubset.OffsetArithmetic.uint32_addition_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.OffsetArithmetic.uint32_addition_safe

end HonoLean.Upstream.SourceSubset.OffsetSequenceChecks
