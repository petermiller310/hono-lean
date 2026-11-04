import HonoLean.Upstream.NodeQueueSchedule.Correctness
import HonoLean.Upstream.NodeQueueAdvance.Correctness

namespace HonoLean.Upstream.NodeQueueSchedule

open SourceSubset ECMA2025

/-- Erasure is a read-value observation, relative to an explicit ambient
nonarray frame. It does not assert that the source sparse arrays are dense. -/
theorem numeric_read_erasure (array : IndexedArray) (index : Nat) (wellFormed : WellFormedIndexed array) :
    numericGet array index = (observe array)[index]?.getD .undefined := by
  rw [observe_getElem?]
  by_cases inside : index < array.length
  · simp [inside]
  · simp [inside, numericGet, wellFormed index (Nat.le_of_not_lt inside)]

theorem shift_read_erasure (array : IndexedArray) :
    (shiftSteps array).1 = (observe array).headD .undefined ∧
    observe (shiftSteps array).2 = (observe array).tail := by
  refine ⟨?_, observe_shiftSteps array⟩
  by_cases empty : array.length = 0
  · have observed : observe array = [] := by simp [observe, empty]
    simp [shiftSteps, empty, observed]
  · have inside : 0 < array.length := Nat.pos_of_ne_zero empty
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, observe_getElem?]
    simp [shiftSteps, empty, inside]

theorem erasure_preserves_explicit_ambient_frame (ambient : State) (indexed : IndexedState) :
    (embedIndexedState ambient indexed).objects = ambient.objects ∧
    (embedIndexedState ambient indexed).privates = ambient.privates ∧
    (embedIndexedState ambient indexed).functions = ambient.functions ∧
    (embedIndexedState ambient indexed).sets = ambient.sets ∧
    (embedIndexedState ambient indexed).thisValue = ambient.thisValue := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Equal indexed Get observations do not identify own-property presence. -/
theorem erasure_does_not_identify_holes_with_own_undefined :
    let hole : IndexedArray := ⟨1, fun _ => none⟩
    observe hole = observe (ofList [.undefined]) ∧
    hole.own 0 = none ∧ (ofList [.undefined]).own 0 = some .undefined := by cbv

def consumerProgram : List SparseStmt :=
  [.declare "shifted" (.ordinary NodeQueueAdvance.shiftedExpression),
   .rebind "curNodes" NodeQueueAdvance.nextExpression]

theorem parses_consumer : parseSparseSequence NodeQueueAdvance.pinnedSource NodeQueueAdvance.bindings
    NodeQueueAdvance.mutableBindings = some consumerProgram := by
  set_option maxRecDepth 4096 in cbv

def sourceConsume (fuel : Nat) (before : IndexedState) : Option (Except EvalError IndexedState) := do
  let parsed ← parseSparseSequence NodeQueueAdvance.pinnedSource NodeQueueAdvance.bindings NodeQueueAdvance.mutableBindings
  pure (executeSparseSequence fuel NodeQueueAdvance.mutableBindings parsed before)

theorem shiftAt_embed (ambient : State) (before : IndexedState) (reference limit : Nat) :
    (shiftAt reference before).map (fun result => (result.1, embedIndexedState ambient result.2)) =
      intrinsic limit (.array reference) "shift" [] (embedIndexedState ambient before) := by
  cases found : before.heap[reference]? with
  | none => simp [shiftAt, found, intrinsic, embedIndexedState, Except.map]
  | some array =>
    simp [shiftAt, found, intrinsic, embedIndexedState, Except.map, List.map_set,
      observe_shiftSteps, (shift_read_erasure array).1]

theorem concatAt_array (before : IndexedState) (receiver argument : Nat) (left right : IndexedArray)
    (leftFound : before.heap[receiver]? = some left) (rightFound : before.heap[argument]? = some right)
    (capacity : left.length + right.length ≤ maximumArrayLength) :
    concatAt receiver (.array argument) before =
      .ok (.array before.heap.length, {before with heap := before.heap ++ [concatOwn left right]}) := by
  simp [concatAt, leftFound, rightFound, capacity, bind, pure, Except.bind, Except.pure]

theorem concatAt_scalar (before : IndexedState) (receiver : Nat) (argument : Value) (left : IndexedArray)
    (leftFound : before.heap[receiver]? = some left) (notArray : ∀ reference, argument ≠ .array reference)
    (capacity : left.length + 1 ≤ maximumArrayLength) :
    concatAt receiver argument before =
      .ok (.array before.heap.length, {before with heap := before.heap ++ [concatOwn left (ofList [argument])]}) := by
  cases argument <;> simp_all [concatAt, ofList, bind, pure, Except.bind, Except.pure]

theorem concatAt_array_embed (ambient : State) (before : IndexedState) (receiver argument limit : Nat)
    (left right : IndexedArray) (leftFound : before.heap[receiver]? = some left)
    (rightFound : before.heap[argument]? = some right) (capacity : left.length + right.length ≤ maximumArrayLength) :
    (concatAt receiver (.array argument) before).map (fun result => (result.1, embedIndexedState ambient result.2)) =
      intrinsic limit (.array receiver) "concat" [.array argument] (embedIndexedState ambient before) := by
  rw [concatAt_array before receiver argument left right leftFound rightFound capacity]
  simp [embedIndexedState, intrinsic, leftFound, rightFound, observe_concatOwn, Except.map]

theorem concatAt_scalar_embed (ambient : State) (before : IndexedState) (receiver limit : Nat)
    (argument : Value) (left : IndexedArray) (leftFound : before.heap[receiver]? = some left)
    (notArray : ∀ reference, argument ≠ .array reference) (capacity : left.length + 1 ≤ maximumArrayLength) :
    (concatAt receiver argument before).map (fun result => (result.1, embedIndexedState ambient result.2)) =
      intrinsic limit (.array receiver) "concat" [argument] (embedIndexedState ambient before) := by
  rw [concatAt_scalar before receiver argument left leftFound notArray capacity]
  have found : (embedIndexedState ambient before).heap[receiver]? = some (observe left) := by
    simp [embedIndexedState, leftFound]
  rw [intrinsic_concat_scalar _ receiver argument (observe left) found notArray limit]
  simp [embedIndexedState, observe_concatOwn, observe_ofList, Except.map]

structure ConsumerInputs (before : IndexedState) (queue temp : Nat) (queued temporary : IndexedArray)
    (front : List (String × Value)) (old : Value) (back : List (String × Value)) : Prop where
  queueBinding : before.environment.lookup "curNodesQueue" = some (.array queue)
  tempBinding : before.environment.lookup "tempNodes" = some (.array temp)
  queueFound : before.heap[queue]? = some queued
  tempFound : before.heap[temp]? = some temporary
  lexical : before.environment = front ++ ("curNodes", old) :: back
  first : front.lookup "curNodes" = none

def consumerShiftState (before : IndexedState) (queue : Nat) (queued : IndexedArray) : IndexedState :=
  {before with heap := before.heap.set queue (shiftSteps queued).2}
def consumerDeclared (before : IndexedState) (queue : Nat) (queued : IndexedArray) : IndexedState :=
  {consumerShiftState before queue queued with
    environment := ("shifted", (shiftSteps queued).1) :: before.environment}
def consumerFinish (before : IndexedState) (queue : Nat) (queued : IndexedArray)
    (front : List (String × Value)) (value : Value) (heap : List IndexedArray) : IndexedState :=
  {consumerDeclared before queue queued with
    environment := ((consumerDeclared before queue queued).environment).set (front.length + 1) ("curNodes", value)
    heap}
def consumerFalsy (before : IndexedState) (queue temp : Nat) (queued : IndexedArray)
    (front : List (String × Value)) : IndexedState :=
  consumerFinish before queue queued front (.array temp) (consumerShiftState before queue queued).heap
def consumerCopied (before : IndexedState) (queue : Nat) (queued output : IndexedArray)
    (front : List (String × Value)) : IndexedState :=
  consumerFinish before queue queued front (.array before.heap.length)
    ((consumerShiftState before queue queued).heap ++ [output])
def currentArray (queue reference : Nat) (queued initial : IndexedArray) : IndexedArray :=
  if reference = queue then (shiftSteps queued).2 else initial

theorem observe_currentArray (queue reference : Nat) (queued initial : IndexedArray) :
    observe (currentArray queue reference queued initial) =
      NodeQueueAdvance.currentValues queue reference (observe queued) (observe initial) := by
  by_cases equal : reference = queue <;> simp [currentArray, NodeQueueAdvance.currentValues, equal, observe_shiftSteps]

private theorem consumer_cell (before : IndexedState) (queue reference : Nat) (queued initial : IndexedArray)
    (queueFound : before.heap[queue]? = some queued) (found : before.heap[reference]? = some initial) :
    (consumerDeclared before queue queued).heap[reference]? = some (currentArray queue reference queued initial) := by
  have inside := (List.getElem?_eq_some_iff.mp queueFound).1
  by_cases equal : reference = queue
  · subst reference
    simp [consumerDeclared, consumerShiftState, currentArray, List.getElem?_set_self inside]
  · simpa [consumerDeclared, consumerShiftState, currentArray, equal] using
      (List.getElem?_set_ne (Ne.symm equal) (l := before.heap) (a := (shiftSteps queued).2)).trans found

private theorem consumer_dense_inputs (ambient : State) (before : IndexedState) (queue temp : Nat)
    (queued temporary : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back) :
    NodeQueueAdvance.Inputs (embedIndexedState ambient before) queue temp (observe queued) (observe temporary) front old back :=
  ⟨inputs.queueBinding, inputs.tempBinding, by simp [embedIndexedState, inputs.queueFound],
    by simp [embedIndexedState, inputs.tempFound], inputs.lexical, inputs.first⟩

private theorem consumer_shift (extra : Nat) (before : IndexedState) (queue : Nat) (queued : IndexedArray)
    (binding : before.environment.lookup "curNodesQueue" = some (.array queue))
    (found : before.heap[queue]? = some queued) :
    evalSparseExpression (extra + 9) NodeQueueAdvance.shiftedExpression before =
      .ok ((shiftSteps queued).1, consumerShiftState before queue queued) := by
  simp [NodeQueueAdvance.shiftedExpression, evalSparseExpression, binding, found, evalSparseArguments,
    sparseIntrinsic, shiftAt, consumerShiftState, bind, pure, Except.bind, Except.pure]

private theorem consumer_with_right (extra : Nat) (before : IndexedState) (queue temp : Nat) (queued temporary : IndexedArray)
    (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (value : Value) (evaluated : IndexedState)
    (right : evalSparseExpression (extra + 8) NodeQueueAdvance.nextExpression (consumerDeclared before queue queued) = .ok (value, evaluated)) :
    executeSparseSequence (extra + 10) NodeQueueAdvance.mutableBindings consumerProgram before =
      .ok {evaluated with environment := evaluated.environment.set (front.length + 1) ("curNodes", value)} := by
  have lexical : (consumerDeclared before queue queued).environment =
      (("shifted", (shiftSteps queued).1) :: front) ++ ("curNodes", old) :: back := by
    simp [consumerDeclared, inputs.lexical]
  have first : ((("shifted", (shiftSteps queued).1) :: front) : List (String × Value)).lookup "curNodes" = none := by
    simpa using inputs.first
  have slot : mutableBindingIndex "curNodes" (consumerDeclared before queue queued).environment = some (front.length + 1) := by
    rw [lexical, mutableBindingIndex_first _ back "curNodes" old first]
    rfl
  simp only [consumerProgram, executeSparseSequence, evalSparseInitializer]
  rw [consumer_shift extra before queue queued inputs.queueBinding inputs.queueFound]
  dsimp only [bind, pure, Except.bind, Except.pure]
  change (do
    let next ← executeSparseRebind (extra + 8) NodeQueueAdvance.mutableBindings "curNodes" NodeQueueAdvance.nextExpression
      (consumerDeclared before queue queued)
    executeSparseSequence (extra + 8) NodeQueueAdvance.mutableBindings [] next) = _
  simp [executeSparseRebind, NodeQueueAdvance.mutableBindings, slot, right,
    executeSparseSequence, bind, pure, Except.bind, Except.pure]

private theorem consumer_true_right (extra : Nat) (before : IndexedState) (queue temp : Nat) (queued current : IndexedArray)
    (tempBinding : before.environment.lookup "tempNodes" = some (.array temp))
    (found : (consumerDeclared before queue queued).heap[temp]? = some current)
    (test : truthy (shiftSteps queued).1 = true) :
    evalSparseExpression (extra + 8) NodeQueueAdvance.nextExpression (consumerDeclared before queue queued) =
      concatAt temp (shiftSteps queued).1 (consumerDeclared before queue queued) := by
  have binding : (consumerDeclared before queue queued).environment.lookup "tempNodes" = some (.array temp) := by
    simpa [consumerDeclared, List.lookup_cons] using tempBinding
  have shifted : (consumerDeclared before queue queued).environment.lookup "shifted" = some (shiftSteps queued).1 := by
    simp [consumerDeclared]
  simp only [NodeQueueAdvance.nextExpression, evalSparseExpression, shifted, binding, found, test,
    evalSparseArguments, bind, pure, Except.bind, Except.pure, ↓reduceIte, String.reduceBEq, Bool.or_true, sparseIntrinsic]

private theorem consumer_falsy_run (extra : Nat) (before : IndexedState) (queue temp : Nat) (queued temporary : IndexedArray)
    (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back) (test : truthy (shiftSteps queued).1 = false) :
    sourceConsume (extra + 10) before = some (.ok (consumerFalsy before queue temp queued front)) := by
  have binding : (consumerDeclared before queue queued).environment.lookup "tempNodes" = some (.array temp) := by
    simpa [consumerDeclared, List.lookup_cons] using inputs.tempBinding
  have shifted : (consumerDeclared before queue queued).environment.lookup "shifted" = some (shiftSteps queued).1 := by
    simp [consumerDeclared]
  have right : evalSparseExpression (extra + 8) NodeQueueAdvance.nextExpression (consumerDeclared before queue queued) =
      .ok (.array temp, consumerDeclared before queue queued) := by
    simp only [NodeQueueAdvance.nextExpression, evalSparseExpression, shifted, binding, test,
      bind, pure, Except.bind, Except.pure, Bool.false_eq_true, ↓reduceIte]
  simpa [sourceConsume, parses_consumer, consumerFalsy, consumerFinish, consumerDeclared, consumerShiftState] using
    congrArg some (consumer_with_right extra before queue temp queued temporary front old back inputs _ _ right)

private theorem consumer_copied_embed (ambient : State) (before : IndexedState) (queue : Nat) (queued output : IndexedArray)
    (front : List (String × Value)) :
    embedIndexedState ambient (consumerCopied before queue queued output front) =
      NodeQueueAdvance.copiedState (embedIndexedState ambient before) queue (observe queued) (observe output) front := by
  simp [consumerCopied, consumerFinish, consumerDeclared, consumerShiftState, embedIndexedState,
    NodeQueueAdvance.copiedState, NodeQueueAdvance.finish, NodeQueueAdvance.declaredState, NodeQueueAdvance.shiftState,
    writeMutableBinding, List.map_set, observe_shiftSteps, (shift_read_erasure queued).1]

/-- Actual parsed sparse209–210 and the earlier dense read-value theorem
agree on the false arm. The sparse own-property heap remains authoritative. -/
theorem consumer_falsy_erases (extra limit : Nat) (ambient : State) (before : IndexedState) (queue temp : Nat)
    (queued temporary : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back) (test : truthy (shiftSteps queued).1 = false) :
    ∃ after, sourceConsume (extra + 10) before = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 10) limit (embedIndexedState ambient before) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient before) queue temp (observe queued) (observe temporary)
        (embedIndexedState ambient after) := by
  have run := consumer_falsy_run extra before queue temp queued temporary front old back inputs test
  have denseTest : truthy ((observe queued).headD .undefined) = false := by
    rw [← (shift_read_erasure queued).1]; exact test
  obtain ⟨denseRun, contract⟩ := NodeQueueAdvance.falsy_satisfies extra limit (embedIndexedState ambient before) queue temp
    (observe queued) (observe temporary) front old back (consumer_dense_inputs ambient before queue temp queued temporary front old back inputs) denseTest
  have embedded : embedIndexedState ambient (consumerFalsy before queue temp queued front) =
      NodeQueueAdvance.falsyState (embedIndexedState ambient before) queue temp (observe queued) front := by
    simp [consumerFalsy, consumerFinish, consumerDeclared, consumerShiftState, embedIndexedState,
      NodeQueueAdvance.falsyState, NodeQueueAdvance.finish, NodeQueueAdvance.declaredState, NodeQueueAdvance.shiftState,
      writeMutableBinding, List.map_set, observe_shiftSteps, (shift_read_erasure queued).1]
  exact ⟨_, run, embedded.symm ▸ denseRun, embedded.symm ▸ contract⟩

private theorem consumer_array_run (extra : Nat) (before : IndexedState) (queue temp argument : Nat)
    (queued temporary initial : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (head : (shiftSteps queued).1 = .array argument) (argumentFound : before.heap[argument]? = some initial)
    (capacity : (currentArray queue temp queued temporary).length + (currentArray queue argument queued initial).length ≤ maximumArrayLength) :
    sourceConsume (extra + 10) before = some (.ok (consumerCopied before queue queued
      (concatOwn (currentArray queue temp queued temporary) (currentArray queue argument queued initial)) front)) := by
  have tempFound := consumer_cell before queue temp queued temporary inputs.queueFound inputs.tempFound
  have argFound := consumer_cell before queue argument queued initial inputs.queueFound argumentFound
  have right : evalSparseExpression (extra + 8) NodeQueueAdvance.nextExpression (consumerDeclared before queue queued) =
      .ok (.array before.heap.length, {consumerDeclared before queue queued with heap :=
        (consumerShiftState before queue queued).heap ++ [concatOwn (currentArray queue temp queued temporary) (currentArray queue argument queued initial)]}) := by
    rw [consumer_true_right extra before queue temp queued _ inputs.tempBinding tempFound (by rw [head]; rfl), head,
      concatAt_array _ temp argument _ _ tempFound argFound capacity]
    simp [consumerDeclared, consumerShiftState]
  simpa [sourceConsume, parses_consumer, consumerCopied, consumerFinish] using
    congrArg some (consumer_with_right extra before queue temp queued temporary front old back inputs _ _ right)

/-- Both sparse input arrays may alias the queue, each other, or themselves.
Capacity is an initial bound on their lengths after the one known shift. -/
theorem consumer_array_erases (extra limit : Nat) (ambient : State) (before : IndexedState) (queue temp argument : Nat)
    (queued temporary initial : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (head : (shiftSteps queued).1 = .array argument) (argumentFound : before.heap[argument]? = some initial)
    (capacity : (currentArray queue temp queued temporary).length + (currentArray queue argument queued initial).length ≤ maximumArrayLength) :
    ∃ after, sourceConsume (extra + 10) before = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 10) limit (embedIndexedState ambient before) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient before) queue temp (observe queued) (observe temporary)
        (embedIndexedState ambient after) := by
  have run := consumer_array_run extra before queue temp argument queued temporary initial front old back inputs head argumentFound capacity
  have denseHead : (observe queued).headD .undefined = .array argument := by
    rw [← (shift_read_erasure queued).1]; exact head
  have found : (embedIndexedState ambient before).heap[argument]? = some (observe initial) := by
    simp [embedIndexedState, argumentFound]
  obtain ⟨denseRun, contract⟩ := NodeQueueAdvance.array_satisfies extra limit (embedIndexedState ambient before) queue temp
    (observe queued) (observe temporary) front old back (consumer_dense_inputs ambient before queue temp queued temporary front old back inputs)
    argument (observe initial) denseHead found
  have embedded := consumer_copied_embed ambient before queue queued
    (concatOwn (currentArray queue temp queued temporary) (currentArray queue argument queued initial)) front
  simp only [observe_concatOwn, observe_currentArray] at embedded
  exact ⟨_, run, embedded.symm ▸ denseRun, embedded.symm ▸ contract⟩

private theorem consumer_scalar_run (extra : Nat) (before : IndexedState) (queue temp : Nat)
    (queued temporary : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (test : truthy (shiftSteps queued).1 = true) (notArray : ∀ reference, (shiftSteps queued).1 ≠ .array reference)
    (capacity : (currentArray queue temp queued temporary).length + 1 ≤ maximumArrayLength) :
    sourceConsume (extra + 10) before = some (.ok (consumerCopied before queue queued
      (concatOwn (currentArray queue temp queued temporary) (ofList [(shiftSteps queued).1])) front)) := by
  have tempFound := consumer_cell before queue temp queued temporary inputs.queueFound inputs.tempFound
  have right : evalSparseExpression (extra + 8) NodeQueueAdvance.nextExpression (consumerDeclared before queue queued) =
      .ok (.array before.heap.length, {consumerDeclared before queue queued with heap :=
        (consumerShiftState before queue queued).heap ++ [concatOwn (currentArray queue temp queued temporary) (ofList [(shiftSteps queued).1])]}) := by
    rw [consumer_true_right extra before queue temp queued _ inputs.tempBinding tempFound test,
      concatAt_scalar _ temp _ _ tempFound notArray capacity]
    simp [consumerDeclared, consumerShiftState]
  simpa [sourceConsume, parses_consumer, consumerCopied, consumerFinish] using
    congrArg some (consumer_with_right extra before queue temp queued temporary front old back inputs _ _ right)

theorem consumer_scalar_erases (extra limit : Nat) (ambient : State) (before : IndexedState) (queue temp : Nat)
    (queued temporary : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (test : truthy (shiftSteps queued).1 = true) (notArray : ∀ reference, (shiftSteps queued).1 ≠ .array reference)
    (capacity : (currentArray queue temp queued temporary).length + 1 ≤ maximumArrayLength) :
    ∃ after, sourceConsume (extra + 10) before = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 10) limit (embedIndexedState ambient before) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient before) queue temp (observe queued) (observe temporary)
        (embedIndexedState ambient after) := by
  have run := consumer_scalar_run extra before queue temp queued temporary front old back inputs test notArray capacity
  have denseTest : truthy ((observe queued).headD .undefined) = true := by
    rw [← (shift_read_erasure queued).1]; exact test
  have denseNotArray : ∀ reference, (observe queued).headD .undefined ≠ .array reference := by
    rw [← (shift_read_erasure queued).1]; exact notArray
  obtain ⟨denseRun, contract⟩ := NodeQueueAdvance.scalar_satisfies extra limit (embedIndexedState ambient before) queue temp
    (observe queued) (observe temporary) front old back (consumer_dense_inputs ambient before queue temp queued temporary front old back inputs)
    denseTest denseNotArray
  have embedded := consumer_copied_embed ambient before queue queued
    (concatOwn (currentArray queue temp queued temporary) (ofList [(shiftSteps queued).1])) front
  simp only [observe_concatOwn, observe_currentArray, observe_ofList] at embedded
  conv at embedded => rhs; rw [(shift_read_erasure queued).1]
  exact ⟨_, run, embedded.symm ▸ denseRun, embedded.symm ▸ contract⟩

/-- Actual parsed209–210 on the sparse heap, with all normal source cases.
The existing theorem is reused only for its read-value contract. No own
presence or full native traversal equivalence is inferred from erasure. -/
theorem consumer_source_erases (extra limit : Nat) (ambient : State) (before : IndexedState) (queue temp : Nat)
    (queued temporary : IndexedArray) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : ConsumerInputs before queue temp queued temporary front old back)
    (admitted : truthy (shiftSteps queued).1 = false ∨
      (∃ argument initial, (shiftSteps queued).1 = .array argument ∧ before.heap[argument]? = some initial ∧
        (currentArray queue temp queued temporary).length + (currentArray queue argument queued initial).length ≤ maximumArrayLength) ∨
      (truthy (shiftSteps queued).1 = true ∧ (∀ reference, (shiftSteps queued).1 ≠ .array reference) ∧
        (currentArray queue temp queued temporary).length + 1 ≤ maximumArrayLength)) :
    ∃ after, sourceConsume (extra + 10) before = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 10) limit (embedIndexedState ambient before) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient before) queue temp (observe queued) (observe temporary)
        (embedIndexedState ambient after) := by
  rcases admitted with falsy | ⟨argument, initial, head, found, capacity⟩ | ⟨test, notArray, capacity⟩
  · exact consumer_falsy_erases extra limit ambient before queue temp queued temporary front old back inputs falsy
  · exact consumer_array_erases extra limit ambient before queue temp argument queued temporary initial front old back inputs head found capacity
  · exact consumer_scalar_erases extra limit ambient before queue temp queued temporary front old back inputs test notArray capacity

def scheduledTemp (before : IndexedState) (queue temp index : Nat) (initial : IndexedArray) : IndexedArray :=
  if temp = queue then indexedSet (ofList []) index (.array before.heap.length) else initial

/-- A real producer-to-consumer composition from initial facts: scheduling
beyond index0 into an initially empty queue creates a hole at0, and the next
actual source209–210 consumes that hole without concat. Readiness and aliases
are derived from the producer's allocation/Set, not supplied afterward. This
is two explicit source activations, not reachability through the omitted body. -/
theorem schedule_then_first_hole (extra limit : Nat) (ambient : State) (before : IndexedState) (queue temp index : Nat)
    (temporary : IndexedArray) (child : Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue index (ofList []) child)
    (tempBinding : before.environment.lookup "tempNodes" = some (.array temp))
    (tempFound : before.heap[temp]? = some temporary)
    (lexical : before.environment = front ++ ("curNodes", old) :: back) (first : front.lookup "curNodes" = none)
    (positive : 0 < index) :
    ∃ scheduled after,
      sourceSchedule (extra + 10) before = some (.ok scheduled) ∧
      Contract before queue index (ofList []) child scheduled ∧
      sourceConsume (extra + 10) scheduled = some (.ok after) ∧
      NodeQueueAdvance.sourceAdvance (extra + 10) limit (embedIndexedState ambient scheduled) =
        some (.ok (.normal (embedIndexedState ambient after))) ∧
      NodeQueueAdvance.Contract (embedIndexedState ambient scheduled) queue temp
        (observe (indexedSet (ofList []) index (.array before.heap.length)))
        (observe (scheduledTemp before queue temp index temporary)) (embedIndexedState ambient after) := by
  let written := indexedSet (ofList []) index (.array before.heap.length)
  let scheduled := createdState before queue index (ofList []) child
  have producer := created_satisfies extra before queue index (ofList []) child inputs (by rfl)
  have queueInside := (List.getElem?_eq_some_iff.mp inputs.queueFound).1
  have tempInside := (List.getElem?_eq_some_iff.mp tempFound).1
  have queueNow : scheduled.heap[queue]? = some written := by
    change (before.heap.set queue written ++ [_])[queue]? = _
    rw [List.getElem?_append_left (by simpa using queueInside)]
    exact List.getElem?_set_self queueInside
  have tempNow : scheduled.heap[temp]? = some (scheduledTemp before queue temp index temporary) := by
    by_cases alias : temp = queue
    · subst temp; simpa [scheduledTemp, written] using queueNow
    · change (before.heap.set queue written ++ [_])[temp]? = _
      rw [List.getElem?_append_left (by simpa using tempInside), List.getElem?_set_ne (Ne.symm alias)]
      simpa [scheduledTemp, alias] using tempFound
  have consumerInputs : ConsumerInputs scheduled queue temp written (scheduledTemp before queue temp index temporary)
      (("targetCurNodes", .array before.heap.length) :: front) old back := by
    refine ⟨?_, ?_, queueNow, tempNow, ?_, ?_⟩
    · simpa [scheduled, createdState, List.lookup_cons] using inputs.queueBinding
    · simpa [scheduled, createdState, List.lookup_cons] using tempBinding
    · simp [scheduled, createdState, lexical]
    · simpa using first
  have zeroHole : written.own 0 = none := by
    rw [indexedSet_own_other (ofList []) index 0 _ (by omega)]
    rfl
  have head : (shiftSteps written).1 = .undefined := by
    rw [shiftSteps_head written (indexedSet_wellFormed _ _ _ (ofList_wellFormed []))]
    simp [numericGet, zeroHole]
  obtain ⟨after, sparseRun, denseRun, denseContract⟩ := consumer_falsy_erases extra limit ambient scheduled queue temp written
    (scheduledTemp before queue temp index temporary) (("targetCurNodes", .array before.heap.length) :: front) old back consumerInputs (by rw [head]; rfl)
  exact ⟨scheduled, after, producer.1, producer.2, sparseRun, denseRun, denseContract⟩

end HonoLean.Upstream.NodeQueueSchedule
