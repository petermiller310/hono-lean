import HonoLean.Upstream.NodeQueueSchedule.Contract

namespace HonoLean.Upstream.NodeQueueSchedule

open SourceSubset ECMA2025

theorem own_write_contract (before : IndexedArray) (index : Nat) (value : Value) :
    OwnWrite before (indexedSet before index value) index value :=
  ⟨indexedSet_length before index value, indexedSet_own_same before index value,
    fun key different => indexedSet_own_other before index key value different⟩

theorem own_append_contract (before : IndexedArray) (value : Value) (wellFormed : WellFormedIndexed before) :
    OwnAppend before (pushOwn before value) value :=
  ⟨pushOwn_length before value, pushOwn_own_same before value,
    fun key inside => pushOwn_own_old before value key inside,
    pushOwn_wellFormed before value wellFormed⟩

theorem reused_contract (before : IndexedState) (queue index target : Nat) (queued initial : IndexedArray) (child : Value)
    (inputs : Inputs before queue index queued child)
    (selected : numericGet queued index = .array target)
    (found : before.heap[target]? = some initial)
    (wellFormed : WellFormedIndexed initial) (capacity : initial.length < maximumArrayLength) :
    Contract before queue index queued child (reusedState before target initial child) := by
  have targetInside := (List.getElem?_eq_some_iff.mp found).1
  have appended := own_append_contract initial child wellFormed
  have targetFound : (reusedState before target initial child).heap[target]? = some (pushOwn initial child) :=
    List.getElem?_set_self targetInside
  have targetLegal : LegalArrayLength (pushOwn initial child) := by
    change (pushOwn initial child).length ≤ maximumArrayLength
    rw [pushOwn_length]; omega
  refine ⟨inputs.queueBinding, inputs.countBinding, inputs.childBinding, inputs.queueFound, inputs.legalIndex, ?_, ?_⟩
  · by_cases self : target = queue
    · subst target
      have equal : initial = queued := Option.some.inj (found.symm.trans inputs.queueFound)
      subst initial
      have inside := numericGet_array_inside queued index queue inputs.wellFormed selected
      refine ⟨queue, pushOwn queued child, pushOwn queued child,
        .reused queued _ selected found appended rfl rfl, targetFound, targetFound,
        ?_, appended.wellFormed, targetLegal, appended.wellFormed, targetLegal, ?_⟩
      · rw [pushOwn_own_old queued child index inside]
        exact numericGet_array_own queued index queue selected
      · intro reference _ different _
        exact List.getElem?_set_ne (Ne.symm different)
    · have queueFound : (reusedState before target initial child).heap[queue]? = some queued :=
        (List.getElem?_set_ne self).trans inputs.queueFound
      refine ⟨target, queued, pushOwn initial child,
        .reused initial _ selected found appended rfl rfl, queueFound, targetFound,
        numericGet_array_own queued index target selected, inputs.wellFormed, inputs.legalLength,
        appended.wellFormed, targetLegal, ?_⟩
      intro reference _ _ different
      exact List.getElem?_set_ne (Ne.symm different)
  · simp [reusedState, selected]

theorem created_contract (before : IndexedState) (queue index : Nat) (queued : IndexedArray) (child : Value)
    (inputs : Inputs before queue index queued child)
    (falsy : truthy (numericGet queued index) = false) :
    Contract before queue index queued child (createdState before queue index queued child) := by
  have queueInside := (List.getElem?_eq_some_iff.mp inputs.queueFound).1
  have appended := own_append_contract (ofList []) child (ofList_wellFormed [])
  have writtenWF := indexedSet_wellFormed queued index (.array before.heap.length) inputs.wellFormed
  have writtenLegal : LegalArrayLength (indexedSet queued index (.array before.heap.length)) := by
    change max queued.length (index + 1) ≤ maximumArrayLength
    have old := inputs.legalLength
    change queued.length ≤ maximumArrayLength at old
    have key := inputs.legalIndex
    omega
  have targetLegal : LegalArrayLength (pushOwn (ofList []) child) := by
    change (pushOwn (ofList []) child).length ≤ maximumArrayLength
    rw [pushOwn_length]
    decide
  refine ⟨inputs.queueBinding, inputs.countBinding, inputs.childBinding, inputs.queueFound, inputs.legalIndex, ?_, ?_⟩
  · refine ⟨before.heap.length, indexedSet queued index (.array before.heap.length), pushOwn (ofList []) child,
      .created _ _ falsy rfl (own_write_contract queued index _) appended rfl rfl,
      ?_, ?_, indexedSet_own_same queued index _, writtenWF, writtenLegal,
      appended.wellFormed, targetLegal, ?_⟩
    · change (before.heap.set queue _ ++ [_])[queue]? = _
      rw [List.getElem?_append_left (by simpa using queueInside)]
      exact List.getElem?_set_self queueInside
    · change (before.heap.set queue _ ++ [_])[before.heap.length]? = _
      simp
    · intro reference inside notQueue _
      change (before.heap.set queue _ ++ [_])[reference]? = _
      rw [List.getElem?_append_left (by simpa using inside)]
      exact List.getElem?_set_ne (Ne.symm notQueue)
  · simp only [createdState, List.length_append, List.length_set, List.length_singleton, falsy, Bool.false_eq_true, ↓reduceIte]

def assignedState (before : IndexedState) (queue index : Nat) (queued : IndexedArray) : IndexedState :=
  {before with heap := before.heap.set queue (indexedSet queued index (.array before.heap.length)) ++ [ofList []]}

theorem initializer_reuses (extra : Nat) (before : IndexedState) (queue index target : Nat)
    (queued : IndexedArray) (child : Value) (inputs : Inputs before queue index queued child)
    (selected : numericGet queued index = .array target) :
    evalSparseInitializer (extra + 9) initializer before = .ok (.array target, before) := by
  simp [initializer, evalSparseInitializer, evalSparseExpression, inputs.queueBinding, inputs.countBinding,
    inputs.queueFound, inputs.legalIndex, selected, bind, pure, Except.bind, Except.pure]

theorem initializer_creates (extra : Nat) (before : IndexedState) (queue index : Nat)
    (queued : IndexedArray) (child : Value) (inputs : Inputs before queue index queued child)
    (falsy : truthy (numericGet queued index) = false) :
    evalSparseInitializer (extra + 9) initializer before =
      .ok (.array before.heap.length, assignedState before queue index queued) := by
  have inside := (List.getElem?_eq_some_iff.mp inputs.queueFound).1
  have found : (allocateFresh [] before).2.heap[queue]? = some queued :=
    (List.getElem?_append_left inside).trans inputs.queueFound
  simp only [initializer, evalSparseInitializer, evalSparseExpression, inputs.queueBinding, inputs.countBinding,
    inputs.queueFound, inputs.legalIndex, ↓reduceIte, falsy, Bool.false_eq_true,
    bind, pure, Except.bind, Except.pure]
  rw [setAt_found _ queue index _ queued found inputs.legalIndex]
  simp [allocateFresh, assignedState, List.set_append_left _ _ inside]

private theorem push_child (extra : Nat) (before : IndexedState) (target : Nat) (initial : IndexedArray) (child : Value)
    (binding : before.environment.lookup "targetCurNodes" = some (.array target))
    (childBinding : before.environment.lookup "child" = some child)
    (found : before.heap[target]? = some initial) (capacity : initial.length < maximumArrayLength) :
    evalSparseExpression (extra + 8) (.call (.variable "targetCurNodes") "push" [.variable "child"]) before =
      .ok (.number (initial.length + 1), {before with heap := before.heap.set target (pushOwn initial child)}) := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp [evalSparseExpression, binding, childBinding, found, evalSparseArguments, sparseIntrinsic,
    pushAt, capacity, List.getElem?_set_self inside, pushOwn_length, bind, pure, Except.bind, Except.pure]

theorem reused_satisfies (extra : Nat) (before : IndexedState) (queue index target : Nat)
    (queued initial : IndexedArray) (child : Value) (inputs : Inputs before queue index queued child)
    (selected : numericGet queued index = .array target) (found : before.heap[target]? = some initial)
    (wellFormed : WellFormedIndexed initial) (capacity : initial.length < maximumArrayLength) :
    sourceSchedule (extra + 10) before = some (.ok (reusedState before target initial child)) ∧
    Contract before queue index queued child (reusedState before target initial child) := by
  refine ⟨?_, reused_contract before queue index target queued initial child inputs selected found wellFormed capacity⟩
  have pushed := push_child extra
    {before with environment := ("targetCurNodes", .array target) :: before.environment} target initial child
    rfl (by simpa [List.lookup_cons] using inputs.childBinding) found capacity
  have run : executeSparseSequence (extra + 10) [] program before = .ok (reusedState before target initial child) := by
    simp only [program, executeSparseSequence]
    rw [initializer_reuses extra before queue index target queued child inputs selected]
    dsimp only [bind, pure, Except.bind, Except.pure]
    rw [pushed]
    simp [reusedState]
  simpa [sourceSchedule, parses_source] using congrArg some run

theorem created_satisfies (extra : Nat) (before : IndexedState) (queue index : Nat)
    (queued : IndexedArray) (child : Value) (inputs : Inputs before queue index queued child)
    (falsy : truthy (numericGet queued index) = false) :
    sourceSchedule (extra + 10) before = some (.ok (createdState before queue index queued child)) ∧
    Contract before queue index queued child (createdState before queue index queued child) := by
  refine ⟨?_, created_contract before queue index queued child inputs falsy⟩
  let active := {assignedState before queue index queued with
    environment := ("targetCurNodes", .array before.heap.length) :: before.environment}
  have found : active.heap[before.heap.length]? = some (ofList []) := by simp [active, assignedState]
  have pushed := push_child extra active before.heap.length (ofList []) child rfl
    (by simpa [active, List.lookup_cons] using inputs.childBinding) found (by decide)
  have run : executeSparseSequence (extra + 10) [] program before = .ok (createdState before queue index queued child) := by
    simp only [program, executeSparseSequence]
    rw [initializer_creates extra before queue index queued child inputs falsy]
    dsimp only [bind, pure, Except.bind, Except.pure]
    change (do
      let (_, state) ← evalSparseExpression (extra + 8) (.call (.variable "targetCurNodes") "push" [.variable "child"]) active
      executeSparseSequence (extra + 8) [] [] state) = _
    rw [pushed]
    simp [executeSparseSequence, active, assignedState, createdState, List.set_append_right, bind, Except.bind]
  simpa [sourceSchedule, parses_source] using congrArg some run

/-- All readiness facts concern the initial indexed heap. Holes, missing
indices and own falsy values all take the created case; an initial truthy
value must be an allocated array with room for the source push. -/
theorem source_schedule_satisfies (extra : Nat) (before : IndexedState) (queue index : Nat)
    (queued : IndexedArray) (child : Value) (inputs : Inputs before queue index queued child)
    (admitted : truthy (numericGet queued index) = false ∨ ∃ target initial,
      numericGet queued index = .array target ∧ before.heap[target]? = some initial ∧
      WellFormedIndexed initial ∧ initial.length < maximumArrayLength) :
    ∃ after, sourceSchedule (extra + 10) before = some (.ok after) ∧ Contract before queue index queued child after := by
  rcases admitted with falsy | ⟨target, initial, selected, found, wellFormed, capacity⟩
  · exact ⟨_, created_satisfies extra before queue index queued child inputs falsy⟩
  · exact ⟨_, reused_satisfies extra before queue index target queued initial child inputs selected found wellFormed capacity⟩

end HonoLean.Upstream.NodeQueueSchedule
