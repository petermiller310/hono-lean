import HonoLean.Upstream.NodePartOffsets.Contract

namespace HonoLean.Upstream.NodePartOffsets

open SourceSubset ECMA2025

theorem weights_append (left right : List JSString) : weights (left ++ right) = weights left + weights right := by
  simp [weights, List.sum_append]

theorem weights_take_le (parts : List JSString) (index : Nat) : weights (parts.take index) ≤ weights parts := by
  have decomposition : weights parts = weights (parts.take index) + weights (parts.drop index) := by
    rw [← weights_append, List.take_append_drop]
  omega

theorem offsetAt_succ (path : JSString) (parts : List JSString) (index : Nat) (inside : index < parts.length) :
    offsetAt path parts (index + 1) = offsetAt path parts index + parts[index].length + 1 := by
  simp only [offsetAt, List.take_succ_eq_append_getElem inside]
  rw [weights_append]
  simp only [weights, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem tableValues_length (path : JSString) (parts : List JSString) (count : Nat) :
    (tableValues path parts count).length = count := by simp [tableValues]

theorem tableValues_succ (path : JSString) (parts : List JSString) (count : Nat) :
    tableValues path parts (count + 1) = tableValues path parts count ++ [.number (offsetAt path parts count)] := by
  simp [tableValues, List.range_succ]

theorem tableValues_cumulative (path : JSString) (parts : List JSString) :
    CumulativeTable path parts (tableValues path parts parts.length) := by
  refine ⟨tableValues_length path parts parts.length, ?_⟩
  intro index inside
  simp [tableValues, inside]

theorem offsetAt_safe (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back) (index : Nat) :
    Arithmetic.SafeInteger (offsetAt path parts index) := by
  have bound := inputs.exactBound
  have smaller := weights_take_le parts index
  unfold offsetAt Arithmetic.SafeInteger Arithmetic.maximumSafeInteger at *
  omega

theorem prepared_contract (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back) :
    PreparedContract before (prepareState before front back path parts) path parts := by
  refine ⟨⟨partsRef, front, back, inputs⟩, ⟨front, back, inputs.reference, inputs.first, rfl⟩,
    ⟨tableValues path parts parts.length, rfl, tableValues_cumulative path parts⟩,
    by simp, ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro reference inside
  exact List.getElem?_append_left inside

private theorem sliceArgument_cases (value : Value) (start : Int) (decoded : sliceArgument value = some start) :
    value = .number start ∨ (value = .undefined ∧ start = 0) := by
  cases value <;> simp_all [sliceArgument]

theorem eval_slice (extra : Nat) (before : State) (cache : Nat) (values : List Value) (path : JSString) (index : Nat) (start : Int)
    (inputs : CachedInputs before cache values path index start) :
    evalOffsetExpression (extra + 31) defaultSplitLimit sliceExpression before = .ok (.string (stringSlice path start), before) := by
  rcases sliceArgument_cases _ start inputs.actualStart with selected | ⟨selected, zero⟩
  · simp [sliceExpression, evalOffsetExpression, evalExpression, lookupVariable, inputs.pathBinding, inputs.cacheBinding,
      inputs.indexBinding, readOffsetProperty, readProperty, inputs.cacheFound, selected, evalOffsetArguments,
      intrinsic, bind, pure, Except.bind, Except.pure]
  · subst start
    simp [sliceExpression, evalOffsetExpression, evalExpression, lookupVariable, inputs.pathBinding, inputs.cacheBinding,
      inputs.indexBinding, readOffsetProperty, readProperty, inputs.cacheFound, selected, evalOffsetArguments,
      intrinsic, stringSlice, normalizeSliceIndex, bind, pure, Except.bind, Except.pure]

theorem cached_contract (before : State) (cache : Nat) (values : List Value) (path : JSString) (index : Nat) (start : Int)
    (inputs : CachedInputs before cache values path index start) :
    CachedContract before (sliceState before (stringSlice path start)) cache values path index start := by
  refine ⟨inputs, rfl, ?_, inputs.cacheFound, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [sliceState, List.lookup_cons] using inputs.cacheBinding

/-- A truthy cache skips every preparation read/allocation. The result is its
actual cached index interpreted by slice; this does not certify/repair a table. -/
theorem source_cached_satisfies (extra : Nat) (before : State) (cache : Nat) (values : List Value)
    (path : JSString) (index : Nat) (start : Int) (inputs : CachedInputs before cache values path index start) :
    sourceOffsets (extra + 64) before = some (.ok (sliceState before (stringSlice path start))) ∧
    CachedContract before (sliceState before (stringSlice path start)) cache values path index start := by
  have guard : evalOffsetExpression (extra + 63) defaultSplitLimit (.logicalNot (.ordinary (.variable "partOffsets"))) before =
      .ok (.boolean false, before) := by
    simp [evalOffsetExpression, evalExpression, lookupVariable, inputs.cacheBinding, bind, pure, Except.bind, Except.pure]
  have sliced := eval_slice (extra + 31) before cache values path index start inputs
  simp only [Nat.add_assoc] at sliced
  have run : executeOffsetSequence (extra + 64) defaultSplitLimit mutableBindings program before =
      .ok (sliceState before (stringSlice path start)) := by
    change executeOffsetSequence (extra + 64) defaultSplitLimit mutableBindings
      (.branch (.logicalNot (.ordinary (.variable "partOffsets"))) branchBody :: sliceProgram) before = _
    rw [executeOffsetSequence_branch_false (extra + 63) defaultSplitLimit mutableBindings _ branchBody sliceProgram before before _ guard (by decide)]
    simp only [sliceProgram, executeOffsetSequence]
    rw [sliced]
    simp [sliceState, bind, Except.bind]
  exact ⟨by simpa [sourceOffsets, parses_source] using congrArg some run, cached_contract before cache values path index start inputs⟩

theorem updated_lookup_other (before : State) (front back : List (String × Value))
    (reference : before.environment = front ++ ("partOffsets", .null) :: back)
    (name : String) (different : name ≠ "partOffsets") :
    (updatedEnvironment before front back).lookup name = before.environment.lookup name := by
  simp [updatedEnvironment, reference, List.lookup_append, List.lookup_cons, beq_false_of_ne different]

theorem updated_cache (before : State) (front back : List (String × Value))
    (first : front.lookup "partOffsets" = none) :
    (updatedEnvironment before front back).lookup "partOffsets" = some (.array before.heap.length) := by
  simp [updatedEnvironment, List.lookup_append, first]

theorem loop_lookup (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString)
    (count : Nat) (name : String) (notP : name ≠ "p") (notOffset : name ≠ "offset") :
    (loopState before front back path parts count).environment.lookup name =
      (updatedEnvironment before front back).lookup name := by
  simp only [loopState, List.cons_append, List.nil_append, List.lookup_cons,
    beq_false_of_ne notP, beq_false_of_ne notOffset]
  rw [lookup_withoutBindings _ _ _ (by simpa), lookup_withoutBindings _ _ _ (by simpa)]

def stepState (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString) (count : Nat) : State :=
  {loopState before front back path parts count with
    environment := [("p", .number count), ("offset", .number (offsetAt path parts (count + 1)))] ++
      withoutBindings (withoutBindings (updatedEnvironment before front back) ["offset"]) ["p"]
    heap := before.heap ++ [tableValues path parts (count + 1)]}

theorem source_loop_step (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (count : Nat) (inside : count < parts.length) :
    executeOffsetSequence (extra + 16) defaultSplitLimit ["p", "offset", "partOffsets"] loopBody
      (loopState before front back path parts count) = .ok (stepState before front back path parts count) := by
  let current := loopState before front back path parts count
  let written := {current with heap := before.heap ++ [tableValues path parts (count + 1)]}
  have pRead : current.environment.lookup "p" = some (.number count) := by rfl
  have offsetRead : current.environment.lookup "offset" = some (.number (offsetAt path parts count)) := by rfl
  have cacheRead : current.environment.lookup "partOffsets" = some (.array before.heap.length) := by
    exact (loop_lookup before front back path parts count "partOffsets" (by decide) (by decide)).trans (updated_cache before front back inputs.first)
  have cacheFound : current.heap[before.heap.length]? = some (tableValues path parts count) := by simp [current, loopState]
  have legal : count < maximumArrayLength := Nat.lt_of_lt_of_le inside inputs.partsBound
  have write : executeOffsetAssign (extra + 15) defaultSplitLimit ["p", "offset", "partOffsets"]
      (.index (.ordinary (.variable "partOffsets")) (.ordinary (.variable "p"))) (.ordinary (.variable "offset")) current = .ok written := by
    simp only [executeOffsetAssign, captureOffsetReference]
    simp only [evalOffsetExpression, evalExpression, lookupVariable, cacheRead, pRead, offsetRead,
      bind, Except.bind, pure, Except.pure]
    have put := putOffsetReference_append current before.heap.length _ (.number (offsetAt path parts count)) cacheFound (by simpa [tableValues_length] using legal)
    simp only [tableValues_length] at put
    rw [put]
    simp [written, current, loopState, tableValues_succ, List.set_append_right]
  have partsRead : written.environment.lookup "parts" = some (.array partsRef) := by
    exact (loop_lookup before front back path parts count "parts" (by decide) (by decide)).trans
      ((updated_lookup_other before front back inputs.reference "parts" (by decide)).trans inputs.partsBinding)
  have partFound : written.heap[partsRef]? = some (parts.map Value.string) := by
    have allocated := (List.getElem?_eq_some_iff.mp inputs.partsFound).1
    simpa [written] using (List.getElem?_append_left (l₂ := [tableValues path parts (count + 1)]) allocated).trans inputs.partsFound
  have partRead := evalOffset_part_length (extra + 7) defaultSplitLimit written "parts" "p" partsRef count parts parts[count]
    partsRead pRead partFound (List.getElem?_eq_getElem inside)
  have right : evalOffsetExpression (extra + 14) defaultSplitLimit stepExpression written =
      .ok (.number (parts[count].length + 1), written) := by
    apply evalOffset_add_numbers (extra + 13)
    · exact partRead
    · simp [evalOffsetExpression, evalExpression, pure, Except.pure]
  have add := executeOffsetAddAssign_first (extra + 14) defaultSplitLimit ["p", "offset", "partOffsets"] "offset" stepExpression
    written written (offsetAt path parts count) (parts[count].length + 1) [("p", .number count)]
    (withoutBindings (withoutBindings (updatedEnvironment before front back) ["offset"]) ["p"])
    (by decide) rfl (by simp) right
  have added : executeOffsetAddAssign (extra + 14) defaultSplitLimit ["p", "offset", "partOffsets"] "offset" stepExpression written =
      .ok (stepState before front back path parts count) := by
    rw [add]
    simp [writeMutableBinding, written, current, loopState, stepState, offsetAt_succ path parts count inside, Int.natCast_add, Int.add_assoc]
  change executeOffsetSequence (extra + 16) defaultSplitLimit ["p", "offset", "partOffsets"] loopBody current = _
  simp only [loopBody, executeOffsetSequence]
  rw [write]
  simp only [bind, Except.bind]
  rw [added]

theorem step_advance (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString) (count : Nat) :
    advanceForHeader loopHeader (stepState before front back path parts count) =
      .ok (loopState before front back path parts (count + 1)) := by
  simp [advanceForHeader, loopHeader, incrementVariable, incrementEnvironment, stepState, loopState, Int.natCast_add,
    bind, Except.bind, pure, Except.pure]

theorem source_loop_complete (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (remaining count : Nat) (total : count + remaining = parts.length) :
    executeOffsetFor (extra + remaining + 32) defaultSplitLimit ["p", "offset", "partOffsets"] loopHeader loopBody
      (loopState before front back path parts count) = .ok (loopState before front back path parts parts.length) := by
  induction remaining generalizing count with
  | zero =>
    have equal : count = parts.length := by omega
    subst count
    have lenRead : (loopState before front back path parts parts.length).environment.lookup "len" = some (.number parts.length) :=
      (loop_lookup before front back path parts parts.length "len" (by decide) (by decide)).trans
        ((updated_lookup_other before front back inputs.reference "len" (by decide)).trans inputs.savedLength)
    have guard := testForHeader_numeric (extra + 27) defaultSplitLimit loopHeader (loopState before front back path parts parts.length)
      "p" "len" parts.length parts.length rfl rfl lenRead
    change executeOffsetFor ((extra + 31) + 1) defaultSplitLimit ["p", "offset", "partOffsets"] loopHeader loopBody _ = _
    rw [executeOffsetFor, guard]
    simp [bind, Except.bind, pure, Except.pure]
  | succ remaining ih =>
    have inside : count < parts.length := by omega
    have lenRead : (loopState before front back path parts count).environment.lookup "len" = some (.number parts.length) :=
      (loop_lookup before front back path parts count "len" (by decide) (by decide)).trans
        ((updated_lookup_other before front back inputs.reference "len" (by decide)).trans inputs.savedLength)
    have guard := testForHeader_numeric (extra + remaining + 28) defaultSplitLimit loopHeader (loopState before front back path parts count)
      "p" "len" count parts.length rfl rfl lenRead
    have less : (count : Int) < parts.length := by omega
    simp only [less, decide_true] at guard
    have body := source_loop_step (extra + remaining + 16) before partsRef path parts front back inputs count inside
    have next := ih (count + 1) (by omega)
    change executeOffsetFor ((extra + remaining + 32) + 1) defaultSplitLimit ["p", "offset", "partOffsets"] loopHeader loopBody _ = _
    rw [executeOffsetFor, guard]
    simp only [bind, Except.bind, ite_true, show offsetDeclaredNames loopBody = [] from rfl, withoutBindings_nil]
    change (do
      let after ← executeOffsetSequence (extra + remaining + 32) defaultSplitLimit ["p", "offset", "partOffsets"] loopBody (loopState before front back path parts count)
      let advanced ← advanceForHeader loopHeader (restoreOffsetScope (loopState before front back path parts count).environment [] after)
      executeOffsetFor (extra + remaining + 32) defaultSplitLimit ["p", "offset", "partOffsets"] loopHeader loopBody advanced) = _
    rw [body]
    simp only [bind, Except.bind, restoreOffsetScope_empty, step_advance]
    exact next

theorem eval_start (extra : Nat) (before : State) (path : JSString)
    (pathRead : before.environment.lookup "path" = some (.string path)) :
    evalOffsetExpression (extra + 16) defaultSplitLimit startExpression before = .ok (.number (initialOffset path), before) := by
  cases read : path[0]? with
  | none => simp [startExpression, initialOffset, read, evalOffsetExpression, evalExpression, lookupVariable, pathRead,
      readOffsetProperty, bind, Except.bind, pure, Except.pure]
  | some unit =>
    by_cases equal : unit = 47
    · subst unit
      simp [startExpression, initialOffset, read, evalOffsetExpression, evalExpression, lookupVariable, pathRead,
        readOffsetProperty, bind, Except.bind, pure, Except.pure]
    · simp [startExpression, initialOffset, read, equal, evalOffsetExpression, evalExpression, lookupVariable, pathRead,
        readOffsetProperty, bind, Except.bind, pure, Except.pure]

def branchState (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString) : State :=
  {before with
    environment := ("offset", .number (offsetAt path parts parts.length)) :: withoutBindings (updatedEnvironment before front back) ["offset"]
    heap := before.heap ++ [tableValues path parts parts.length]}

theorem execute_branch_body (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back) :
    executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings branchBody
      {before with environment := withoutBindings before.environment ["offset"]} = .ok (branchState before front back path parts) := by
  let cleared := {before with environment := withoutBindings before.environment ["offset"]}
  let allocated := {cleared with heap := before.heap ++ [[]]}
  let assigned := {allocated with environment := withoutBindings (updatedEnvironment before front back) ["offset"]}
  let entered := {assigned with environment := ("offset", .number (initialOffset path)) :: assigned.environment}
  have clearedEnv : cleared.environment = withoutBindings front ["offset"] ++ ("partOffsets", .null) :: withoutBindings back ["offset"] := by
    simp [cleared, inputs.reference, withoutBindings, List.filter_append]
  have clearedAbsent : (withoutBindings front ["offset"]).lookup "partOffsets" = none := by
    rw [lookup_withoutBindings _ _ _ (by decide), inputs.first]
  have allocation : evalOffsetExpression (extra + parts.length + 78) defaultSplitLimit (.ordinary (.arrayLiteral [])) cleared =
      .ok (.array before.heap.length, allocated) := by
    simp [evalOffsetExpression, evalExpression, evalLiteralElements, cleared, allocated, bind, Except.bind, pure, Except.pure]
  have assign := executeOffsetAssign_first (extra + parts.length + 78) defaultSplitLimit mutableBindings "partOffsets" (.ordinary (.arrayLiteral []))
    cleared allocated .null (.array before.heap.length) (withoutBindings front ["offset"]) (withoutBindings back ["offset"])
    (by decide) clearedEnv clearedAbsent allocation
  have assignedEq : writeMutableBinding allocated (withoutBindings front ["offset"]).length "partOffsets" (.array before.heap.length) = assigned := by
    simp [writeMutableBinding, allocated, clearedEnv, assigned, updatedEnvironment, withoutBindings, List.filter_append, List.set_append_right]
  rw [assignedEq] at assign
  have pathRead : assigned.environment.lookup "path" = some (.string path) := by
    exact (lookup_withoutBindings _ _ _ (by decide)).trans
      ((updated_lookup_other before front back inputs.reference "path" (by decide)).trans inputs.pathBinding)
  have start := eval_start (extra + parts.length + 61) assigned path pathRead
  have enter := (enterForHeader_one_numeric (extra + parts.length + 72) defaultSplitLimit loopHeader entered "p" 0 rfl).1
  have initial : {entered with environment := ("p", .number 0) :: withoutBindings entered.environment ["p"]} =
      loopState before front back path parts 0 := by
    simp [entered, assigned, allocated, cleared, loopState, offsetAt, tableValues, weights, withoutBindings]
  rw [initial] at enter
  have complete := source_loop_complete (extra + 44) before partsRef path parts front back inputs parts.length 0 (by omega)
  have restore : restoreOffsetScope entered.environment ["p"] (loopState before front back path parts parts.length) = branchState before front back path parts := by
    have weave := weaveScoped_rebind ["p"] [] assigned.environment "offset" (.number (initialOffset path))
      (.number (offsetAt path parts parts.length)) (by decide)
    simpa [restoreOffsetScope, entered, loopState, branchState, assigned, allocated, cleared,
      withoutBindings, List.filter_filter] using weave
  change executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings branchBody cleared = _
  change executeOffsetSequence ((extra + parts.length + 78) + 1) defaultSplitLimit mutableBindings
    (.assign (.ordinary (.variable "partOffsets")) (.ordinary (.arrayLiteral [])) ::
      [.declare true "offset" startExpression, .countedFor loopHeader loopBody]) cleared = _
  rw [executeOffsetSequence]
  change (do
    let state ← executeOffsetAssign (extra + parts.length + 78) defaultSplitLimit mutableBindings (.ordinary (.variable "partOffsets")) (.ordinary (.arrayLiteral [])) cleared
    executeOffsetSequence (extra + parts.length + 78) defaultSplitLimit mutableBindings
      [.declare true "offset" startExpression, .countedFor loopHeader loopBody] state) = _
  rw [assign]
  simp only [bind, Except.bind]
  rw [executeOffsetSequence, start]
  change (do
    let state ← enterForHeader (extra + parts.length + 76) defaultSplitLimit loopHeader entered
    let state ← executeOffsetFor (extra + parts.length + 76) defaultSplitLimit ["p", "offset", "partOffsets"] loopHeader loopBody state
    executeOffsetSequence (extra + parts.length + 76) defaultSplitLimit ["offset", "partOffsets"] [] (restoreOffsetScope entered.environment ["p"] state)) = _
  rw [enter]
  simp only [bind, Except.bind]
  rw [show extra + parts.length + 76 = extra + 44 + parts.length + 32 by omega, complete]
  dsimp only
  rw [restore]
  rfl

theorem source_prepare_satisfies (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back) :
    sourcePrepare (extra + parts.length + 80) before = some (.ok (prepareState before front back path parts)) ∧
      PreparedContract before (prepareState before front back path parts) path parts := by
  have cacheRead : before.environment.lookup "partOffsets" = some .null := by simp [inputs.reference, List.lookup_append, inputs.first]
  have guard : evalOffsetExpression (extra + parts.length + 79) defaultSplitLimit (.logicalNot (.ordinary (.variable "partOffsets"))) before = .ok (.boolean true, before) := by
    simp [evalOffsetExpression, evalExpression, lookupVariable, cacheRead, bind, Except.bind, pure, Except.pure]
  have body := execute_branch_body extra before partsRef path parts front back inputs
  have restored : restoreOffsetScope before.environment ["offset"] (branchState before front back path parts) = prepareState before front back path parts := by
    simp only [restoreOffsetScope, branchState, prepareState]
    have weave := weaveScoped_rebind ["offset"] front back "partOffsets" .null (.array before.heap.length) (by decide)
    simpa [inputs.reference, updatedEnvironment, withoutBindings, List.filter_filter] using weave
  have run : executeOffsetSequence (extra + parts.length + 80) defaultSplitLimit mutableBindings prepareProgram before = .ok (prepareState before front back path parts) := by
    change executeOffsetSequence ((extra + parts.length + 79) + 1) defaultSplitLimit mutableBindings
      (.branch (.logicalNot (.ordinary (.variable "partOffsets"))) branchBody :: []) before = _
    rw [executeOffsetSequence, guard]
    change (do
      let after ← executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings branchBody {before with environment := withoutBindings before.environment ["offset"]}
      executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings [] (restoreOffsetScope before.environment ["offset"] after)) = _
    rw [body]
    simp only [bind, Except.bind]
    rw [restored]
    rfl
  exact ⟨by simpa [sourcePrepare, parses_prepare] using congrArg some run, prepared_contract before partsRef path parts front back inputs⟩

theorem prepared_cached_inputs (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (index : Nat) (inside : index < parts.length) (indexRead : before.environment.lookup "i" = some (.number index)) :
    CachedInputs (prepareState before front back path parts) before.heap.length (tableValues path parts parts.length)
      path index (offsetAt path parts index) := by
  refine ⟨updated_cache before front back inputs.first, by simp [prepareState], ?_, ?_, ?_,
    Nat.lt_of_lt_of_le inside inputs.partsBound, by simpa [tableValues_length] using inputs.partsBound,
    offsetAt_safe before partsRef path parts front back inputs index⟩
  · exact (updated_lookup_other before front back inputs.reference "path" (by decide)).trans inputs.pathBinding
  · exact (updated_lookup_other before front back inputs.reference "i" (by decide)).trans indexRead
  · rw [(tableValues_cumulative path parts).index index inside]
    rfl

/-- The fresh branch builds its own complete cumulative table, then the actual
source slice reads that table. Alignment with the original path is established
separately from actual splitPath output. -/
theorem source_fresh_satisfies (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (index : Nat) (inside : index < parts.length) (indexRead : before.environment.lookup "i" = some (.number index)) :
    sourceOffsets (extra + parts.length + 80) before =
      some (.ok (sliceState (prepareState before front back path parts) (path.drop (offsetAt path parts index)))) ∧
    PreparedContract before (prepareState before front back path parts) path parts ∧
    CachedContract (prepareState before front back path parts)
      (sliceState (prepareState before front back path parts) (path.drop (offsetAt path parts index)))
      before.heap.length (tableValues path parts parts.length) path index (offsetAt path parts index) := by
  have cached := prepared_cached_inputs before partsRef path parts front back inputs index inside indexRead
  have sliced := eval_slice (extra + parts.length + 47) (prepareState before front back path parts) before.heap.length
    (tableValues path parts parts.length) path index (offsetAt path parts index) cached
  have cacheRead : before.environment.lookup "partOffsets" = some .null := by simp [inputs.reference, List.lookup_append, inputs.first]
  have guard : evalOffsetExpression (extra + parts.length + 79) defaultSplitLimit (.logicalNot (.ordinary (.variable "partOffsets"))) before = .ok (.boolean true, before) := by
    simp [evalOffsetExpression, evalExpression, lookupVariable, cacheRead, bind, Except.bind, pure, Except.pure]
  have body := execute_branch_body extra before partsRef path parts front back inputs
  have restored : restoreOffsetScope before.environment ["offset"] (branchState before front back path parts) = prepareState before front back path parts := by
    simp only [restoreOffsetScope, branchState, prepareState]
    have weave := weaveScoped_rebind ["offset"] front back "partOffsets" .null (.array before.heap.length) (by decide)
    simpa [inputs.reference, updatedEnvironment, withoutBindings, List.filter_filter] using weave
  have run : executeOffsetSequence (extra + parts.length + 80) defaultSplitLimit mutableBindings program before =
      .ok (sliceState (prepareState before front back path parts) (path.drop (offsetAt path parts index))) := by
    change executeOffsetSequence ((extra + parts.length + 79) + 1) defaultSplitLimit mutableBindings
      (.branch (.logicalNot (.ordinary (.variable "partOffsets"))) branchBody :: sliceProgram) before = _
    rw [executeOffsetSequence, guard]
    change (do
      let after ← executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings branchBody {before with environment := withoutBindings before.environment ["offset"]}
      executeOffsetSequence (extra + parts.length + 79) defaultSplitLimit mutableBindings sliceProgram (restoreOffsetScope before.environment ["offset"] after)) = _
    rw [body]
    simp only [bind, Except.bind]
    rw [restored]
    change executeOffsetSequence ((extra + parts.length + 78) + 1) defaultSplitLimit mutableBindings
      [.declare false "restPathString" sliceExpression] (prepareState before front back path parts) = _
    rw [executeOffsetSequence, sliced]
    simp [executeOffsetSequence, sliceState, stringSlice_from_nat, bind, Except.bind]
  refine ⟨by simpa [sourceOffsets, parses_source] using congrArg some run,
    prepared_contract before partsRef path parts front back inputs, ?_⟩
  simpa [stringSlice_from_nat] using cached_contract (prepareState before front back path parts) before.heap.length
    (tableValues path parts parts.length) path index (offsetAt path parts index) cached

/-- Both source additions (field length + 1, then offset += step) stay exact
under the initial cumulative bound; native exactness is not a later premise. -/
theorem source_step_exact_additions (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (count : Nat) (inside : count < parts.length) :
    OffsetArithmetic.ExactAdditionDomain (parts[count].length : Int) 1 ∧
    OffsetArithmetic.ExactAdditionDomain (offsetAt path parts count : Int) (parts[count].length + 1) := by
  have current := offsetAt_safe before partsRef path parts front back inputs count
  have following := offsetAt_safe before partsRef path parts front back inputs (count + 1)
  rw [offsetAt_succ path parts count inside] at following
  unfold OffsetArithmetic.ExactAdditionDomain Arithmetic.SafeInteger at *
  constructor
  · constructor
    · omega
    · constructor
      · unfold Arithmetic.maximumSafeInteger; omega
      · omega
  · exact ⟨current, by omega, by simpa [Int.natCast_add, Int.add_assoc] using following⟩

/-- info: 'HonoLean.Upstream.NodePartOffsets.source_fresh_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_fresh_satisfies
/-- info: 'HonoLean.Upstream.NodePartOffsets.source_cached_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cached_satisfies

end HonoLean.Upstream.NodePartOffsets
