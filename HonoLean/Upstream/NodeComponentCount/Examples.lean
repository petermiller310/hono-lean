import HonoLean.Upstream.NodeComponentCount.Composition

namespace HonoLean.Upstream.NodeComponentCount.Examples

open SourceSubset ECMA2025

private def cells (entries : List (Option Value)) : IndexedArray :=
  ⟨entries.length, fun index => entries[index]?.getD none⟩
private def tempCells : List (Option Value) := [none, some .undefined, some (.array 0)]
private def slots (array : IndexedArray) : List (Option Value) := (List.range array.length).map array.own
private def heapSlots (state : IndexedState) : List (List (Option Value)) := state.heap.map slots

private def initial (input : JSString) (queue : Nat := 1) (temp : Nat := 2) : RegExpState :=
  {arrays :=
    {environment := [("m", .array 0), ("curNodesQueue", .array queue), ("child", .array 0), ("tempNodes", .array temp),
        ("curNodes", .number 7), ("curNodes", .array 2), ("componentCount", .number 999)]
     heap := [ofList [.string input], ofList [], cells tempCells]}
   regexps := [⟨120, 37⟩]}

private abbrev Observation := Option Value × Option Value × List (List (Option Value)) ×
  List UnitRegExpCell × List (List Nat) × List (List Nat)
private def observe (state : RegExpState) : Observation :=
  (state.arrays.environment.lookup "componentCount", state.arrays.environment.lookup "targetCurNodes",
    heapSlots state.arrays, state.regexps, state.executions.map UnitExecution.positions,
    state.executions.map UnitExecution.lastIndexWrites)
private def countObserved (input : JSString) : Option (Except EvalError Observation) :=
  (sourceCount 100 (initial input)).map (fun result => result.map observe)
private def fullObserved (input : JSString) (queue : Nat := 1) : Option (Except EvalError Observation) :=
  (sourceSchedule 100 (initial input queue)).map (fun result => result.map observe)

/-- Both outcomes allocate the tracked global accumulator. Null makes that
cell unreachable through the match return value; it does not remove it. -/
theorem match_null_and_array_both_track_accumulator :
    (evalRegExpExpression 97 (.stringMatch (.index (.variable "m") (.number 0)) (.literal 47)) (initial [])).map
      (fun result => (result.1, result.2.arrays.heap.length, result.2.arrays.heap[3]?.map IndexedArray.length)) =
        .ok (.ordinary .null, 4, some 0) ∧
    (evalRegExpExpression 97 (.stringMatch (.index (.variable "m") (.number 0)) (.literal 47)) (initial [47, 47])).map
      (fun result => (result.1, result.2.arrays.heap.length, result.2.arrays.heap[3]?.map IndexedArray.length)) =
        .ok (.ordinary (.array 3), 4, some 2) := by cbv

theorem slash_positions_cover_empty_consecutive_and_trailing_cases :
    ([([], 0, []), ([97], 0, []), ([47], 1, [0]), ([47, 47], 2, [0, 1]),
      ([97, 47, 47], 2, [1, 2]), ([47, 97, 47], 2, [0, 2])] : List (JSString × Nat × List Nat)).all
      (fun (input, count, positions) => match sourceCount 100 (initial input) with
        | some (.ok after) =>
          after.arrays.environment.lookup "componentCount" == some (.number count) &&
          after.arrays.heap.length == 4 && after.executions.map UnitExecution.positions == [positions] &&
          after.regexps[0]?.map (fun cell => (cell.unit, cell.lastIndex)) == some (120, 37) &&
          after.regexps[1]?.map (fun cell => (cell.unit, cell.lastIndex)) == some (47, 0)
        | _ => false) = true := by
  simp only [sourceCount, parses_source]
  cbv

/-- Non-ASCII units and lone high/low surrogates are kept as raw UTF16 units.
Only the actual slash indices enter the global match result and trace. -/
theorem raw_utf16_count_and_trace_are_exact :
    countObserved [47, 945, 47, 55296, 47, 56320, 47] = some (.ok
      (some (.number 4), none,
        [[some (.string [47, 945, 47, 55296, 47, 56320, 47])], [], tempCells,
          [some (.string [47]), some (.string [47]), some (.string [47]), some (.string [47])]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0, 2, 4, 6]], [[0, 1, 3, 5, 7, 0]])) := by
  simp only [countObserved, sourceCount, parses_source]
  cbv

theorem full_source_preserves_accumulator_before_fresh_group :
    fullObserved [] = some (.ok
      (some (.number 0), some (.array 4),
        [[some (.string [])], [some (.array 4)], tempCells, [], [some (.array 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[]], [[0, 0]])) ∧
    fullObserved [97, 47, 98] = some (.ok
      (some (.number 1), some (.array 4),
        [[some (.string [97, 47, 98])], [none, some (.array 4)], tempCells, [some (.string [47])], [some (.array 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[1]], [[0, 2, 0]])) := by
  simp only [fullObserved, sourceSchedule, parses_full_source]
  cbv

private def repeatCount : Option (Except EvalError Observation) := do
  let parsed ← parseRegExpSequence pinnedSource bindings
  pure do
    let first ← executeRegExpSequence 100 parsed (initial [47, 47])
    let second ← executeRegExpSequence 100 parsed first
    pure (observe second)

theorem repeated_counts_create_fresh_literals_and_accumulators :
    repeatCount = some (.ok
      (some (.number 2), none,
        [[some (.string [47, 47])], [], tempCells,
         [some (.string [47]), some (.string [47])], [some (.string [47]), some (.string [47])]],
        [⟨120, 37⟩, ⟨47, 0⟩, ⟨47, 0⟩], [[0, 1], [0, 1]], [[0, 1, 2, 0], [0, 1, 2, 0]])) := by
  simp only [repeatCount, parses_source]
  cbv

/-- m=queue can change m[0] AFTER the count is saved. Empty input replaces
that slot; a/b writes the later slot1. Neither path rereads changed m[0]. -/
theorem m_queue_alias_uses_saved_count :
    fullObserved [] 0 = some (.ok
      (some (.number 0), some (.array 4),
        [[some (.array 4)], [], tempCells, [], [some (.array 0)]], [⟨120, 37⟩, ⟨47, 0⟩], [[]], [[0, 0]])) ∧
    fullObserved [97, 47, 98] 0 = some (.ok
      (some (.number 1), some (.array 4),
        [[some (.string [97, 47, 98]), some (.array 4)], [], tempCells, [some (.string [47])], [some (.array 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[1]], [[0, 2, 0]])) := by
  simp only [fullObserved, sourceSchedule, parses_full_source]
  cbv

theorem truthy_nonarray_queue_alias_is_outside_normal_domain :
    sourceSchedule 100 (initial [97, 98, 99] 0) = some (.error .unsupported) := by
  simp only [sourceSchedule, parses_full_source]
  cbv

private def firstConsume (temp : Nat) : Option (Except EvalError (Option Value × Option Value × List (List (Option Value)) × List UnitRegExpCell × List (List Nat))) := do
  let full ← parseRegExpSequence pinnedFullSource fullBindings
  let consume ← parseSparseSequence NodeQueueAdvance.pinnedSource NodeQueueAdvance.bindings NodeQueueAdvance.mutableBindings
  pure do
    let scheduled ← executeRegExpSequence 100 full (initial [97, 47, 98] 1 temp)
    let after ← executeSparseSequence 99 NodeQueueAdvance.mutableBindings consume scheduled.arrays
    pure (after.environment.lookup "curNodes", after.environment.lookup "shifted", heapSlots after,
      scheduled.regexps, scheduled.executions.map UnitExecution.lastIndexWrites)

theorem first_hole_consumption_keeps_regex_trace_and_array_presence :
    firstConsume 0 = some (.ok
      (some (.array 0), some .undefined,
        [[some (.string [97, 47, 98])], [some (.array 4)], tempCells, [some (.string [47])], [some (.array 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0, 2, 0]])) ∧
    firstConsume 1 = some (.ok
      (some (.array 1), some .undefined,
        [[some (.string [97, 47, 98])], [some (.array 4)], tempCells, [some (.string [47])], [some (.array 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0, 2, 0]])) := by
  simp only [firstConsume, parses_full_source, NodeQueueSchedule.parses_consumer]
  cbv

theorem invalid_m_receivers_fail_closed :
    sourceCount 100 {initial [] with arrays := {environment := [("m", .array 99)], heap := []}} = some (.error .invalidReference) ∧
    sourceCount 100 {initial [] with arrays := {environment := [("m", .array 0)], heap := [ofList [.null]]}} = some (.error .unsupported) ∧
    sourceCount 100 {initial [] with arrays := {environment := [], heap := []}} = some (.error .missingVariable) := by
  simp only [sourceCount, parses_source]
  cbv

private def path : JSString := [97, 47, 98]
private def ambient : State :=
  {objects := List.replicate 4 emptyNullObject
   functions := [⟨⟨"sample", .number 11⟩, []⟩]
   sets := [[[120]]]
   privates := PrivateStore.ofData [("saved", 9)] [(3, [(9, .array 0)])]
   thisValue := .object 3}
private def front : List (String × Value) :=
  [("m", .array 0), ("curNodesQueue", .array 1), ("child", .array 0), ("tempNodes", .array 1)]
private def back : List (String × Value) := [("curNodes", .array 2), ("componentCount", .number 999)]

/-- All operands are supplied before source176; count, A, target, gap and
consumer readiness are conclusions. temp=queue is admitted, and an arbitrary
nonempty ambient private/object/function/Set frame is retained by erasure. -/
theorem initial_empty_queue_has_universal_count_schedule_consumer_contract :
    ∃ scheduled after,
      sourceSchedule 100 (initial path 1 1) = some (.ok scheduled) ∧
      ScheduleContract (initial path 1 1) scheduled 1 (ofList []) (.array 0) path ∧
      NodeQueueSchedule.sourceConsume 99 scheduled.arrays = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance 99 defaultSplitLimit (embedIndexedState ambient scheduled.arrays) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient scheduled.arrays) 1 1
        (ECMA2025.observe (indexedSet (ofList []) 1 (.array 4))) (ECMA2025.observe (indexedSet (ofList []) 1 (.array 4)))
        (embedIndexedState ambient after) ∧
      after.environment.lookup "curNodes" = some (.array 1) ∧ after.environment.lookup "shifted" = some .undefined := by
  have countInputs : Inputs (initial path 1 1) 0 (ofList [.string path]) path :=
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 1 ≤ 4294967295; decide⟩
  have scheduleInputs : ScheduleInputs (initial path 1 1) 1 (ofList []) (.array 0) path :=
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 0 ≤ 4294967295; decide, by decide⟩
  exact source_count_schedule_then_first_hole 0 defaultSplitLimit ambient (initial path 1 1) 0 1 1
    (ofList [.string path]) (ofList []) (.array 0) path front (.number 7) back countInputs scheduleInputs rfl rfl rfl rfl (by decide)

theorem initial_m_queue_alias_has_universal_schedule_contract :
    pinnedFullSource = pinnedSource ++ NodeQueueSchedule.pinnedSource ∧
    ∃ after, sourceSchedule 100 (initial path 0) = some (.ok after) ∧
      ScheduleContract (initial path 0) after 0 (ofList [.string path]) (.array 0) path := by
  have countInputs : Inputs (initial path 0) 0 (ofList [.string path]) path :=
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 1 ≤ 4294967295; decide⟩
  have scheduleInputs : ScheduleInputs (initial path 0) 0 (ofList [.string path]) (.array 0) path :=
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 1 ≤ 4294967295; decide, by decide⟩
  exact source_schedule_satisfies 0 (initial path 0) 0 0 (ofList [.string path]) (ofList [.string path]) (.array 0) path
    countInputs scheduleInputs (Or.inl rfl)

/-- info: 'HonoLean.Upstream.NodeComponentCount.source_count_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeComponentCount.source_count_satisfies

/-- info: 'HonoLean.Upstream.NodeComponentCount.source_count_schedule_then_first_hole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeComponentCount.source_count_schedule_then_first_hole

end HonoLean.Upstream.NodeComponentCount.Examples
