import HonoLean.Upstream.NodeComponentCount.Correctness
import HonoLean.Upstream.NodeQueueSchedule.Bridge

namespace HonoLean.Upstream.NodeComponentCount

open SourceSubset ECMA2025

structure ScheduleInputs (before : RegExpState) (queue : Nat) (queued : IndexedArray) (child : Value) (input : JSString) : Prop where
  queueBinding : before.arrays.environment.lookup "curNodesQueue" = some (.array queue)
  childBinding : before.arrays.environment.lookup "child" = some child
  queueFound : before.arrays.heap[queue]? = some queued
  wellFormed : WellFormedIndexed queued
  legalLength : LegalArrayLength queued
  stringBound : input.length < maximumArrayLength

/-- A readiness condition on the INITIAL queue at the independently specified
slash count. There is no supplied componentCount binding or later heap read. -/
def AdmittedTarget (before : RegExpState) (queued : IndexedArray) (input : JSString) : Prop :=
  truthy (numericGet queued (slashCount input)) = false ∨ ∃ target initial,
    numericGet queued (slashCount input) = .array target ∧ before.arrays.heap[target]? = some initial ∧
    WellFormedIndexed initial ∧ initial.length < maximumArrayLength

structure ScheduleContract (before after : RegExpState) (queue : Nat) (queued : IndexedArray) (child : Value) (input : JSString) : Prop where
  initialQueue : ScheduleInputs before queue queued child input
  stages : ∃ counted, CountContract before counted input ∧
    NodeQueueSchedule.Contract counted.arrays queue (slashCount input) queued child after.arrays ∧
    after.regexps = counted.regexps ∧ after.executions = counted.executions
  accumulatorFound : after.arrays.heap[before.arrays.heap.length]? = some (accumulator input)

theorem counted_queue_inputs (before : RegExpState) (queue : Nat) (queued : IndexedArray) (child : Value) (input : JSString)
    (inputs : ScheduleInputs before queue queued child input) :
    NodeQueueSchedule.Inputs (countState before input).arrays queue (slashCount input) queued child := by
  have inside := (List.getElem?_eq_some_iff.mp inputs.queueFound).1
  refine ⟨?_, rfl, ?_, ?_, inputs.wellFormed, inputs.legalLength, slashCount_legal_index input inputs.stringBound⟩
  · simpa [countState, List.lookup_cons] using inputs.queueBinding
  · simpa [countState, List.lookup_cons] using inputs.childBinding
  · exact (List.getElem?_append_left inside).trans inputs.queueFound

theorem counted_target_admitted (before : RegExpState) (queued : IndexedArray) (input : JSString)
    (admitted : AdmittedTarget before queued input) :
    truthy (numericGet queued (slashCount input)) = false ∨ ∃ target initial,
      numericGet queued (slashCount input) = .array target ∧ (countState before input).arrays.heap[target]? = some initial ∧
      WellFormedIndexed initial ∧ initial.length < maximumArrayLength := by
  rcases admitted with falsy | ⟨target, initial, selected, found, wellFormed, capacity⟩
  · exact Or.inl falsy
  · have inside := (List.getElem?_eq_some_iff.mp found).1
    exact Or.inr ⟨target, initial, selected, (List.getElem?_append_left inside).trans found, wellFormed, capacity⟩

/-- The tracked match accumulator cannot alias an initial allocated target.
It is framed through scheduling even when m and the queue share a cell. -/
theorem accumulator_after_schedule (before : RegExpState) (queue : Nat) (queued : IndexedArray) (child : Value) (input : JSString)
    (initial : ScheduleInputs before queue queued child input) (admitted : AdmittedTarget before queued input)
    (after : IndexedState) (contract : NodeQueueSchedule.Contract (countState before input).arrays queue (slashCount input) queued child after) :
    after.heap[before.arrays.heap.length]? = some (accumulator input) := by
  have queueInside := (List.getElem?_eq_some_iff.mp initial.queueFound).1
  obtain ⟨selected, currentQueue, currentTarget, effect, _, _, _, _, _, _, _, others⟩ := contract.target
  have notQueue : before.arrays.heap.length ≠ queue := Nat.ne_of_gt queueInside
  have notSelected : before.arrays.heap.length ≠ selected := by
    cases effect with
    | reused target output selectedRead _ _ _ _ =>
      rcases admitted with falsy | ⟨oldTarget, oldArray, oldRead, oldFound, _, _⟩
      · have truth : truthy (numericGet queued (slashCount input)) = true := by rw [selectedRead]; rfl
        rw [falsy] at truth
        contradiction
      · have same : selected = oldTarget := Value.array.inj (selectedRead.symm.trans oldRead)
        have inside := (List.getElem?_eq_some_iff.mp oldFound).1
        omega
    | created _ _ _ fresh _ _ _ _ =>
      simp only [countState, List.length_append, List.length_singleton] at fresh
      omega
  exact (others before.arrays.heap.length (by simp [countState]) notQueue notSelected).trans (by simp [countState])

/-- The exact two sparse leaves run with the same expression budgets as the
existing sparse executor. Errors and successful states agree, without assuming
that either future leaf succeeds. -/
theorem execute_schedule_tail (fuel : Nat) (before : RegExpState) :
    executeRegExpSequence (fuel + 3) (NodeQueueSchedule.program.map RegExpStmt.sparse) before =
      (executeSparseSequence (fuel + 3) [] NodeQueueSchedule.program before.arrays).map
        (fun arrays => {before with arrays}) := by
  simp only [NodeQueueSchedule.program, List.map_cons, List.map_nil, executeRegExpSequence, executeSparseSequence]
  cases initialized : evalSparseInitializer (fuel + 2) NodeQueueSchedule.initializer before.arrays with
  | error error => simp [bind, Except.bind, Except.map]
  | ok result =>
    obtain ⟨value, arrays⟩ := result
    simp only [bind, Except.bind]
    cases pushed : evalSparseExpression (fuel + 1) (.call (.variable "targetCurNodes") "push" [.variable "child"])
        {arrays with environment := ("targetCurNodes", value) :: arrays.environment} with
    | error error => simp [Except.map]
    | ok result => obtain ⟨value, after⟩ := result; simp [Except.map]

theorem execute_full (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) (legal : input.length ≤ maximumArrayLength) :
    executeRegExpSequence (extra + 100) fullProgram before =
      (executeSparseSequence (extra + 99) [] NodeQueueSchedule.program (countState before input).arrays).map
        (fun arrays => {countState before input with arrays}) := by
  simp only [fullProgram, program, List.cons_append, List.nil_append, executeRegExpSequence]
  rw [execute_initializer extra before m matched input inputs legal]
  dsimp only [bind, pure, Except.bind, Except.pure]
  have endpoint :
      {unitLiteralMatchState before 47 input with arrays :=
        {(unitLiteralMatchState before 47 input).arrays with environment :=
          ("componentCount", .number (slashCount input)) :: (unitLiteralMatchState before 47 input).arrays.environment}} =
        countState before input := by
    simp [unitLiteralMatchState, countState, accumulator, unitMatchValues, slashRun, slashCount, slashPositions, List.map_const']
  rw [endpoint]
  exact execute_schedule_tail (extra + 96) (countState before input)

/-- Contiguous actual176–178. Count and target readiness come from the input
string and initial heap. Existing queue slots and m=queue aliases are allowed;
the original m cell is not asserted unchanged after scheduling. -/
theorem source_schedule_satisfies (extra : Nat) (before : RegExpState) (m queue : Nat) (matched queued : IndexedArray)
    (child : Value) (input : JSString) (countInputs : Inputs before m matched input)
    (scheduleInputs : ScheduleInputs before queue queued child input) (admitted : AdmittedTarget before queued input) :
    pinnedFullSource = pinnedSource ++ NodeQueueSchedule.pinnedSource ∧
    ∃ after, sourceSchedule (extra + 100) before = some (.ok after) ∧
      ScheduleContract before after queue queued child input := by
  have ready := counted_queue_inputs before queue queued child input scheduleInputs
  obtain ⟨arrays, run, contract⟩ := NodeQueueSchedule.source_schedule_satisfies (extra + 89) (countState before input).arrays
    queue (slashCount input) queued child ready (counted_target_admitted before queued input admitted)
  have sparseRun : executeSparseSequence (extra + 99) [] NodeQueueSchedule.program (countState before input).arrays = .ok arrays := by
    simpa [NodeQueueSchedule.sourceSchedule, NodeQueueSchedule.parses_source, Nat.add_assoc] using run
  have fullRun := execute_full extra before m matched input countInputs (Nat.le_of_lt scheduleInputs.stringBound)
  rw [sparseRun] at fullRun
  refine ⟨reassembles_source, {countState before input with arrays}, ?_,
    ⟨scheduleInputs, ⟨countState before input, count_contract before m matched input countInputs, contract, rfl, rfl⟩,
      accumulator_after_schedule before queue queued child input scheduleInputs admitted arrays contract⟩⟩
  simpa [sourceSchedule, parses_full_source, Except.map] using congrArg some fullRun

theorem source_empty_queue_satisfies (extra : Nat) (before : RegExpState) (m queue : Nat) (matched : IndexedArray)
    (child : Value) (input : JSString) (countInputs : Inputs before m matched input)
    (scheduleInputs : ScheduleInputs before queue (ofList []) child input) :
    pinnedFullSource = pinnedSource ++ NodeQueueSchedule.pinnedSource ∧
    ∃ after, sourceSchedule (extra + 100) before = some (.ok after) ∧
      ScheduleContract before after queue (ofList []) child input :=
  source_schedule_satisfies extra before m queue matched (ofList []) child input countInputs scheduleInputs (Or.inl rfl)

/-- For an initially empty pending queue the selected group follows the
tracked accumulator, regardless of whether match returned null or an array. -/
theorem empty_group_follows_accumulator (before after : RegExpState) (queue : Nat) (child : Value) (input : JSString)
    (contract : ScheduleContract before after queue (ofList []) child input) :
    after.arrays.environment.lookup "targetCurNodes" = some (.array (before.arrays.heap.length + 1)) ∧
    ∃ target, after.arrays.heap[before.arrays.heap.length + 1]? = some target ∧
      target.length = 1 ∧ target.own 0 = some child := by
  obtain ⟨counted, count, schedule, _, _⟩ := contract.stages
  have length : counted.arrays.heap.length = before.arrays.heap.length + 1 := by simp [count.heap]
  obtain ⟨selected, currentQueue, currentTarget, effect, _, found, _, _, _, _, _, _⟩ := schedule.target
  cases effect with
  | reused _ _ selectedRead _ _ _ _ => simp [numericGet, ofList] at selectedRead
  | created written output _ fresh _ append environment heap =>
    have selectedLength : selected = before.arrays.heap.length + 1 := fresh.trans length
    refine ⟨?_, output, ?_, ?_, ?_⟩
    · simp [environment, selectedLength]
    · rw [heap, ← length]
      simp
    · simpa [ofList] using append.length
    · simpa [ofList] using append.appended

theorem falsy_contract_bindings (before after : State) (queue temp : Nat) (queued temporary : List Value)
    (contract : NodeQueueAdvance.Contract before queue temp queued temporary after)
    (head : queued.headD .undefined = .undefined) :
    after.environment.lookup "curNodes" = some (.array temp) ∧ after.environment.lookup "shifted" = some .undefined := by
  obtain ⟨front, old, back, value, _, absent, environment, contents⟩ := contract.lexical
  have returned : value = .array temp := by
    cases contents with
    | falsy _ returned _ => exact returned
    | array _ _ _ selected _ _ _ _ _ => rw [head] at selected; contradiction
    | scalar test _ _ _ _ _ => rw [head] at test; contradiction
  rw [environment, head, returned]
  simp [List.lookup_cons, List.lookup_append, absent]

/-- Contiguous176–178 followed by separate actual209–210, from BEFORE-count
facts. Positive slash count plus initially empty queue derives a first hole;
all temp/queue aliases and the fresh accumulator offset are transported. -/
theorem source_count_schedule_then_first_hole (extra limit : Nat) (ambient : State) (before : RegExpState)
    (m queue temp : Nat) (matched temporary : IndexedArray) (child : Value) (input : JSString)
    (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (countInputs : Inputs before m matched input) (scheduleInputs : ScheduleInputs before queue (ofList []) child input)
    (tempBinding : before.arrays.environment.lookup "tempNodes" = some (.array temp))
    (tempFound : before.arrays.heap[temp]? = some temporary)
    (lexical : before.arrays.environment = front ++ ("curNodes", old) :: back) (first : front.lookup "curNodes" = none)
    (positive : 0 < slashCount input) :
    ∃ scheduled after,
      sourceSchedule (extra + 100) before = some (.ok scheduled) ∧
      ScheduleContract before scheduled queue (ofList []) child input ∧
      NodeQueueSchedule.sourceConsume (extra + 99) scheduled.arrays = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 99) limit (embedIndexedState ambient scheduled.arrays) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient scheduled.arrays) queue temp
        (observe (indexedSet (ofList []) (slashCount input) (.array (before.arrays.heap.length + 1))))
        (observe (NodeQueueSchedule.scheduledTemp (countState before input).arrays queue temp (slashCount input) temporary))
        (embedIndexedState ambient after) ∧
      after.environment.lookup "curNodes" = some (.array temp) ∧ after.environment.lookup "shifted" = some .undefined := by
  let counted := countState before input
  have ready := counted_queue_inputs before queue (ofList []) child input scheduleInputs
  have tempInside := (List.getElem?_eq_some_iff.mp tempFound).1
  have tempNow : counted.arrays.heap[temp]? = some temporary := (List.getElem?_append_left tempInside).trans tempFound
  have tempBindingNow : counted.arrays.environment.lookup "tempNodes" = some (.array temp) := by
    simpa [counted, countState, List.lookup_cons] using tempBinding
  have lexicalNow : counted.arrays.environment =
      (("componentCount", .number (slashCount input)) :: front) ++ ("curNodes", old) :: back := by
    simp [counted, countState, lexical]
  have firstNow : ((("componentCount", .number (slashCount input)) :: front) : List (String × Value)).lookup "curNodes" = none := by
    simpa using first
  obtain ⟨arrays, after, scheduleRun, scheduleContract, consumeRun, denseRun, denseContract⟩ :=
    NodeQueueSchedule.schedule_then_first_hole (extra + 89) limit ambient counted.arrays queue temp (slashCount input) temporary child
      (("componentCount", .number (slashCount input)) :: front) old back ready tempBindingNow tempNow lexicalNow firstNow positive
  have sparseRun : executeSparseSequence (extra + 99) [] NodeQueueSchedule.program counted.arrays = .ok arrays := by
    simpa [NodeQueueSchedule.sourceSchedule, NodeQueueSchedule.parses_source, Nat.add_assoc] using scheduleRun
  have run := execute_full extra before m matched input countInputs (Nat.le_of_lt scheduleInputs.stringBound)
  rw [sparseRun] at run
  have head : (observe (indexedSet (ofList []) (slashCount input) (.array counted.arrays.heap.length))).headD .undefined = .undefined := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, observe_getElem?]
    have inside : 0 < (indexedSet (ofList []) (slashCount input) (.array counted.arrays.heap.length)).length := by
      simp [indexedSet, ofList]
    have hole : (indexedSet (ofList []) (slashCount input) (.array counted.arrays.heap.length)).own 0 = none :=
      indexedSet_own_other _ _ 0 _ (by omega)
    simp [inside, numericGet, hole]
  have bindings := falsy_contract_bindings _ _ queue temp _ _ denseContract head
  refine ⟨{counted with arrays}, after, ?_,
    ⟨scheduleInputs, ⟨counted, count_contract before m matched input countInputs, scheduleContract, rfl, rfl⟩,
      accumulator_after_schedule before queue (ofList []) child input scheduleInputs (Or.inl rfl) arrays scheduleContract⟩,
    ?_, ?_, ?_, bindings.1, bindings.2⟩
  · simpa [sourceSchedule, parses_full_source, Except.map] using congrArg some run
  · simpa [Nat.add_assoc] using consumeRun
  · simpa [Nat.add_assoc] using denseRun
  · simpa [counted, countState] using denseContract

end HonoLean.Upstream.NodeComponentCount
