import HonoLean.Upstream.NodeQueueSchedule.Bridge

namespace HonoLean.Upstream.NodeQueueSchedule.Examples

open SourceSubset ECMA2025

private def cells (entries : List (Option Value)) : IndexedArray :=
  ⟨entries.length, fun index => entries[index]?.getD none⟩
private def slots (array : IndexedArray) : List (Option Value) := (List.range array.length).map array.own
private def heapSlots (state : IndexedState) : List (List (Option Value)) := state.heap.map slots
private def tempCells : List (Option Value) := [none, some .undefined, some (.array 2)]
private def initial (index : Nat) (queued : List (Option Value)) (child : Value := .array 2) : IndexedState :=
  {environment := [("curNodesQueue", .array 0), ("componentCount", .number index), ("child", child),
      ("tempNodes", .array 1), ("curNodes", .number 7), ("curNodes", .array 2), ("targetCurNodes", .number 88)]
   heap := [cells queued, cells tempCells, ofList [.array 0]]}

private def observed (before : IndexedState) : Option (Except EvalError (List (List (Option Value)) × Option Value × Nat)) :=
  (sourceSchedule 32 before).map fun result => result.map fun after =>
    (heapSlots after, after.environment.lookup "targetCurNodes", after.heap.length)

theorem missing_slot_allocates_once_and_preserves_holes :
    observed (initial 2 []) = some (.ok
      ([[none, none, some (.array 3)], tempCells, [some (.array 0)], [some (.array 2)]], some (.array 3), 4)) := by
  simp only [observed, sourceSchedule, parses_source]
  cbv

/-- Missing own cells and own undefined/null/false/0/empty-string all select
the fallback, while every other own flag remains unchanged. -/
theorem holes_and_all_own_falsy_values_take_the_fresh_case :
    let queued : List (Option Value) := [none, some .undefined, some .null, some (.boolean false), some (.number 0), some (.string [])]
    (List.range 6).all (fun index => match sourceSchedule 32 (initial index queued) with
      | some (.ok after) => match after.heap[0]?, after.heap[3]? with
        | some queue, some target =>
          after.heap.length == 4 && queue.length == 6 && queue.own index == some (.array 3) &&
          target.length == 1 && target.own 0 == some (.array 2) &&
          (List.range 6).all (fun other => if other == index then true else queue.own other == (cells queued).own other)
        | _, _ => false
      | _ => false) = true := by
  simp only [sourceSchedule, parses_source]
  cbv

/-- The existing target aliases the queue. The source push appends at the
queue's old length, preserving both the selected slot and its old hole. -/
theorem truthy_self_target_appends_to_current_queue_without_allocation :
    observed (initial 0 [some (.array 0), none, some (.array 2)] (.array 0)) = some (.ok
      ([[some (.array 0), none, some (.array 2), some (.array 0)], tempCells, [some (.array 0)]], some (.array 0), 3)) := by
  simp only [observed, sourceSchedule, parses_source]
  cbv

/-- Creation can itself make a reference cycle: queue points at the new
target, whose child value points back at the existing queue. -/
theorem creation_is_shallow_and_can_create_cycles :
    observed (initial 1 [] (.array 0)) = some (.ok
      ([[none, some (.array 3)], tempCells, [some (.array 0)], [some (.array 0)]], some (.array 3), 4)) := by
  simp only [observed, sourceSchedule, parses_source]
  cbv

private def repeatSchedule : Option (Except EvalError IndexedState) := do
  let parsed ← parseSparseSequence pinnedSource bindings
  pure do
    let first ← executeSparseSequence 32 [] parsed (initial 2 [])
    -- A second activation reads the live slot created by the first.
    executeSparseSequence 32 [] parsed first

theorem repeated_registration_reuses_one_target :
    repeatSchedule.map (fun result => result.map fun after => (heapSlots after, after.heap.length)) =
      some (.ok ([[none, none, some (.array 3)], tempCells, [some (.array 0)],
        [some (.array 2), some (.array 2)]], 4)) := by
  simp only [repeatSchedule, parses_source]
  cbv

private def scheduleAndConsume : Option (Except EvalError (List Value × List Value × List (List (Option Value)))) := do
  let schedule ← parseSparseSequence pinnedSource bindings
  let consume ← parseSparseSequence NodeQueueAdvance.pinnedSource NodeQueueAdvance.bindings NodeQueueAdvance.mutableBindings
  pure do
    let first ← executeSparseSequence 32 [] schedule (initial 2 [])
    let queued ← executeSparseSequence 32 [] schedule first
    let one ← executeSparseSequence 32 NodeQueueAdvance.mutableBindings consume queued
    let two ← executeSparseSequence 32 NodeQueueAdvance.mutableBindings consume one
    let three ← executeSparseSequence 32 NodeQueueAdvance.mutableBindings consume two
    let nodes ← [one, two, three].mapM fun state => match state.environment.lookup "curNodes" with
      | some value => pure value | none => throw .missingVariable
    let heads ← [one, two, three].mapM fun state => match state.environment.lookup "shifted" with
      | some value => pure value | none => throw .missingVariable
    pure (nodes, heads, heapSlots three)

/-- Actual producer and consumer fragments share one authoritative sparse
heap. The first two shifts consume holes; the third sees the scheduled target.
Concat keeps a hole distinct from the following own undefined property. -/
theorem actual_schedule_then_delayed_consumption_preserves_own_presence :
    scheduleAndConsume = some (.ok
      ([.array 1, .array 1, .array 4], [.undefined, .undefined, .array 3],
       [[], tempCells, [some (.array 0)], [some (.array 2), some (.array 2)],
        [none, some .undefined, some (.array 2), some (.array 2), some (.array 2)]])) := by
  simp only [scheduleAndConsume, parses_source, parses_consumer]
  cbv

private def selfScheduleAndConsume : Option (Except EvalError (List (List (Option Value)) × Option Value)) := do
  let schedule ← parseSparseSequence pinnedSource bindings
  let consume ← parseSparseSequence NodeQueueAdvance.pinnedSource NodeQueueAdvance.bindings NodeQueueAdvance.mutableBindings
  pure do
    let queued ← executeSparseSequence 32 [] schedule (initial 0 [some (.array 0), none])
    let after ← executeSparseSequence 32 NodeQueueAdvance.mutableBindings consume queued
    pure (heapSlots after, after.environment.lookup "curNodes")

theorem self_target_consumption_reads_queue_after_shift :
    selfScheduleAndConsume = some (.ok
      ([[none, some (.array 2)], tempCells, [some (.array 0)],
        [none, some .undefined, some (.array 2), none, some (.array 2)]], some (.array 3))) := by
  simp only [selfScheduleAndConsume, parses_source, parses_consumer]
  cbv

/-- The largest array index creates a sparse length without allocating a
list of every gap. The next integer is a named property outside this runtime. -/
theorem maximum_index_and_nonindex_boundary :
    (sourceSchedule 32 (initial 4294967294 [])).map (fun result => result.map fun after =>
      (after.heap[0]?).map fun queue => (queue.length, queue.own 0, queue.own 4294967294, after.heap.length)) =
        some (.ok (some (4294967295, none, some (.array 3), 4))) ∧
    sourceSchedule 32 (initial 4294967295 []) = some (.error .unsupported) ∧
    sourceSchedule 32 {initial 0 [] with environment :=
      [("curNodesQueue", .array 0), ("componentCount", .number (-1)), ("child", .array 2)]} = some (.error .unsupported) := by
  simp only [sourceSchedule, parses_source]
  cbv

theorem truthy_nonarrays_and_dangling_targets_are_rejected :
    sourceSchedule 32 (initial 0 [some (.number 7)]) = some (.error .unsupported) ∧
    sourceSchedule 32 (initial 0 [some (.array 99)]) = some (.error .invalidReference) := by
  simp only [sourceSchedule, parses_source]
  cbv

private def ambient : State :=
  {objects := List.replicate 4 emptyNullObject
   functions := [⟨⟨"sample", .number 11⟩, []⟩]
   sets := [[[120]]]
   privates := PrivateStore.ofData [("saved", 9)] [(3, [(9, .array 0)])]
   thisValue := .object 3}

private def initialFront : List (String × Value) :=
  [("curNodesQueue", .array 0), ("componentCount", .number 2), ("child", .array 2), ("tempNodes", .array 1)]
private def initialBack : List (String × Value) := [("curNodes", .array 2), ("targetCurNodes", .number 88)]

/-- An inhabited BEFORE-producer domain applies the universal source
composition, retaining a supplied nonempty private/object/function/Set frame. -/
theorem initial_queue_has_universal_producer_consumer_contract :
    ∃ scheduled after,
      sourceSchedule 32 (initial 2 []) = some (.ok scheduled) ∧
      Contract (initial 2 []) 0 2 (ofList []) (.array 2) scheduled ∧
      sourceConsume 32 scheduled = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance 32 defaultSplitLimit (embedIndexedState ambient scheduled) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient scheduled) 0 1
        (observe (indexedSet (ofList []) 2 (.array 3))) (observe (cells tempCells)) (embedIndexedState ambient after) := by
  have inputs : Inputs (initial 2 []) 0 2 (ofList []) (.array 2) :=
    ⟨rfl, rfl, rfl, rfl, ofList_wellFormed [], by change 0 ≤ 4294967295; decide, by decide⟩
  exact schedule_then_first_hole 22 defaultSplitLimit ambient (initial 2 []) 0 1 2 (cells tempCells) (.array 2)
    initialFront (.number 7) initialBack inputs rfl rfl rfl rfl (by decide)

theorem self_target_has_universal_source_contract :
    ∃ after, sourceSchedule 32 (initial 0 [some (.array 0), none]) = some (.ok after) ∧
      Contract (initial 0 [some (.array 0), none]) 0 0 (cells [some (.array 0), none]) (.array 2) after := by
  have wellFormed : WellFormedIndexed (cells [some (.array 0), none]) := by
    intro index outside
    simp [cells, List.getElem?_eq_none outside]
  have inputs : Inputs (initial 0 [some (.array 0), none]) 0 0 (cells [some (.array 0), none]) (.array 2) :=
    ⟨rfl, rfl, rfl, rfl, wellFormed, by change 2 ≤ 4294967295; decide, by decide⟩
  exact ⟨_, reused_satisfies 22 _ 0 0 0 _ _ (.array 2) inputs rfl rfl wellFormed (by decide)⟩

/-- info: 'HonoLean.Upstream.NodeQueueSchedule.source_schedule_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeQueueSchedule.source_schedule_satisfies

/-- info: 'HonoLean.Upstream.NodeQueueSchedule.schedule_then_first_hole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeQueueSchedule.schedule_then_first_hole

end HonoLean.Upstream.NodeQueueSchedule.Examples
