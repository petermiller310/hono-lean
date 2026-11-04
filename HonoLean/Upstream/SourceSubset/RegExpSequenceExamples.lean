import HonoLean.Upstream.SourceSubset.RegExpSequence

namespace HonoLean.Upstream.SourceSubset.RegExpSequenceChecks

open ECMA2025
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def countSource := "const componentCount = m[0].match(/\\//g)?.length ?? 0"
private def scheduleSource := "\nconst targetCurNodes = (curNodesQueue[componentCount] ||= [])\ntargetCurNodes.push(child)"
private def countProgram : List RegExpStmt :=
  [.declare "componentCount" (.nullish (.optionalLength
    (.stringMatch (.index (.variable "m") (.number 0)) (.literal 47))) (.number 0))]
private def tailProgram : List SparseStmt :=
  [.declare "targetCurNodes" (.logicalOrAssign (.variable "curNodesQueue") (.variable "componentCount") (.arrayLiteral [])),
   .evaluate (.call (.variable "targetCurNodes") "push" [.variable "child"])]

theorem parses_original_literal_optional_nullish_ast :
    parseRegExpSequence countSource ["m"] = some countProgram := by cbv

theorem parses_full_count_and_schedule :
    parseRegExpSequence (countSource ++ scheduleSource) ["m", "curNodesQueue", "child"] =
      some (countProgram ++ tailProgram.map RegExpStmt.sparse) := by cbv

theorem old_entries_and_unsupported_regex_syntax_reject :
    parseBlock countSource ["m"] = none ∧ parseSparseSequence countSource ["m"] = none ∧
    (["const n = m[0].match(/a+/g)?.length ?? 0", "const n = m[0].match(/./g)?.length ?? 0",
      "const n = m[0].match(/(a)/g)?.length ?? 0", "const n = m[0].match(/a/gg)?.length ?? 0",
      "const n = m[0].match(/a/i)?.length ?? 0", "const n = m[0].match(/a/gu)?.length ?? 0",
      "const n = m[0].match(/a/)?.length ?? 0", "const n = m[0].match(//g)?.length ?? 0",
      "const n = m[0] / a / g", "const n = unknown[0].match(/a/g)?.length ?? 0",
      "const n = m[0].match(/a/g)?.length ?? ++m", "const n = m[0].match(/a/g)?.length ?? n"] : List String).all
      (fun source => (parseRegExpSequence source ["m"]).isNone) = true := by cbv

theorem utf16_positions_and_global_lastIndex_trace :
    executeUnitGlobal [55296, 47, 233, 47, 56320] ⟨47, 99⟩ =
      ⟨[1, 3], ⟨47, 0⟩, [0, 2, 4, 0]⟩ ∧
    executeUnitGlobal [55296, 233, 56320] ⟨47, 99⟩ = ⟨[], ⟨47, 0⟩, [0, 0]⟩ := by cbv

private def input : JSString := [55296, 47, 233, 47, 56320]
private def before : RegExpState :=
  {arrays := {environment := [("m", .array 0), ("curNodesQueue", .array 1), ("child", .object 0)]
              heap := [ofList [.string input], ofList []]}
   regexps := [⟨120, 17⟩]}
private def view (state : RegExpState) :=
  (state.arrays.environment.lookup "componentCount", state.regexps, state.executions,
    state.arrays.heap.map (fun array => (array.length, observe array)))

theorem actual_count_uses_fresh_regex_and_dense_match_accumulator :
    (parseRegExpSequence countSource ["m"]).map (fun code => (executeRegExpSequence 100 code before).map view) =
    some (.ok (some (.number 2), [⟨120, 17⟩, ⟨47, 0⟩], [⟨[1, 3], ⟨47, 0⟩, [0, 2, 4, 0]⟩],
      [(1, [.string input]), (0, []), (2, [.string [47], .string [47]])])) := by cbv

/-- This A cell is tracked by the model even though the null result makes it
unreachable from source. It is not an observed native empty-array identity. -/
theorem no_hits_return_null_but_still_allocate_tracked_A :
    (evalRegExpExpression 32 (.stringMatch (.variable "text") (.literal 47))
      {arrays := {environment := [("text", .string [55296, 233, 56320])], heap := [ofList []]}}).map
      (fun (value, state) => (value, state.arrays.heap.map observe, state.regexps, state.executions)) =
    .ok (.ordinary .null, [[], []], [⟨47, 0⟩], [⟨[], ⟨47, 0⟩, [0, 0]⟩]) := by cbv

theorem optional_nullish_follows_actual_fallback :
    (parseRegExpSequence "const n = m[0].match(/a/g)?.length ?? 7" ["m"]).map
      (fun code => (executeRegExpSequence 100 code {arrays := {environment := [("m", .array 0)], heap := [ofList [.string [98]]]}}).map
        (fun state => state.arrays.environment.lookup "n")) = some (.ok (some (.number 7))) := by cbv

theorem ascii_atom_literal_is_not_hardcoded_to_slash :
    (parseRegExpSequence "const n = m[0].match(/x/g)?.length ?? 0" ["m"]).map
      (fun code => (executeRegExpSequence 100 code {arrays := {environment := [("m", .array 0)], heap := [ofList [.string [55296, 120, 233, 120, 56320]]]}}).map
        (fun state => (state.arrays.environment.lookup "n", state.executions))) =
      some (.ok (some (.number 2), [⟨[1, 3], ⟨120, 0⟩, [0, 2, 4, 0]⟩])) := by cbv

theorem receiver_effects_precede_literal_and_match :
    (parseRegExpSequence "const n = receivers.shift().match(/\\//g)?.length ?? 0" ["receivers"]).map
      (fun code => (executeRegExpSequence 100 code {arrays := {environment := [("receivers", .array 0)], heap := [ofList [.string [47], .string []]]}}).map
        (fun state => (state.arrays.environment.lookup "n", state.arrays.heap.map observe, state.regexps))) =
    some (.ok (some (.number 1), [[.string []], [.string [47]]], [⟨47, 0⟩])) := by cbv

theorem quoted_slashes_remain_ordinary_string_syntax :
    (parseRegExpSequence "const url = 'http://x'" []).map
      (fun code => (executeRegExpSequence 100 code {}).map (fun state => (state.regexps, state.arrays.environment.lookup "url"))) =
    some (.ok ([], some (.string [104, 116, 116, 112, 58, 47, 47, 120]))) := by cbv

theorem full_original_count_creates_sparse_queue_gaps :
    (parseRegExpSequence (countSource ++ scheduleSource) ["m", "curNodesQueue", "child"]).map
      (fun code => (executeRegExpSequence 100 code before).map (fun state =>
        (state.arrays.environment.lookup "componentCount", state.arrays.environment.lookup "targetCurNodes",
         state.arrays.heap.length, (state.arrays.heap[1]?).map (fun array => (array.length, array.own 0, array.own 1, array.own 2)),
         (state.arrays.heap[3]?).map observe))) =
    some (.ok (some (.number 2), some (.array 3), 4, some (3, none, none, some (.array 3)), some [.object 0])) := by cbv

/-- The symbolic theorem works for every UTF16 string, not only examples. -/
theorem arbitrary_utf16_count_contract (text : JSString) (state : RegExpState) :
    UnitCountContract state (unitLiteralMatchState state 47 text) 47 text
      (.number (matchingPositions 47 text).length) := unitLiteralMatchState_satisfies state 47 text

theorem count_bound_is_derived_from_input (text : JSString) (legal : text.length < maximumArrayLength) :
    LegalArrayIndex (matchingPositions 47 text).length := unitCount_index_legal text 47 legal

/-- info: 'HonoLean.Upstream.ECMA2025.executeUnitGlobal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.executeUnitGlobal_satisfies
/-- info: 'HonoLean.Upstream.SourceSubset.evalRegExp_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalRegExp_count
/-- info: 'HonoLean.Upstream.SourceSubset.unitLiteralMatchState_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.unitLiteralMatchState_satisfies

end HonoLean.Upstream.SourceSubset.RegExpSequenceChecks
