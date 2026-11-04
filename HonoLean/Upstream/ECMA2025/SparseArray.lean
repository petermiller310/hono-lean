import HonoLean.Upstream.ECMA2025.DenseArray

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-! Sparse own-index specialization. None is a missing own property, distinct
from Some undefined. Writable indices/length, clean numeric prototypes, frozen
intrinsics/default species/spreadability and successful resources are premises.
Indices below 2^32-1 are array indices; 2^32-1 itself is a named property outside
this model. Observation erases presence only for reads, never for dense shape. -/

def WellFormedIndexed (array : IndexedArray) : Prop :=
  ∀ index, array.length ≤ index → array.own index = none

def LegalArrayIndex (index : Nat) : Prop := index < maximumArrayLength

def indexedSet (array : IndexedArray) (index : Nat) (value : Value) : IndexedArray :=
  ⟨max array.length (index + 1), put array.own index (some value)⟩

def pushOwn (array : IndexedArray) (value : Value) : IndexedArray := indexedSet array array.length value

theorem indexedSet_length (array : IndexedArray) (index : Nat) (value : Value) :
    (indexedSet array index value).length = max array.length (index + 1) := rfl
theorem indexedSet_own_same (array : IndexedArray) (index : Nat) (value : Value) :
    (indexedSet array index value).own index = some value := by simp [indexedSet, put]
theorem indexedSet_own_other (array : IndexedArray) (index other : Nat) (value : Value) (different : other ≠ index) :
    (indexedSet array index value).own other = array.own other := by simp [indexedSet, put, different]
theorem indexedSet_wellFormed (array : IndexedArray) (index : Nat) (value : Value)
    (wellFormed : WellFormedIndexed array) : WellFormedIndexed (indexedSet array index value) := by
  intro other outside
  have old : array.length ≤ other := by change max array.length (index + 1) ≤ other at outside; omega
  have different : other ≠ index := by change max array.length (index + 1) ≤ other at outside; omega
  rw [indexedSet_own_other array index other value different]
  exact wellFormed other old
theorem pushOwn_length (array : IndexedArray) (value : Value) : (pushOwn array value).length = array.length + 1 := by
  simp [pushOwn, indexedSet]
theorem pushOwn_own_same (array : IndexedArray) (value : Value) : (pushOwn array value).own array.length = some value :=
  indexedSet_own_same array array.length value
theorem pushOwn_own_old (array : IndexedArray) (value : Value) (index : Nat) (inside : index < array.length) :
    (pushOwn array value).own index = array.own index :=
  indexedSet_own_other array array.length index value (by omega)
theorem pushOwn_wellFormed (array : IndexedArray) (value : Value) (wellFormed : WellFormedIndexed array) :
    WellFormedIndexed (pushOwn array value) := indexedSet_wellFormed array array.length value wellFormed

theorem ofList_wellFormed (values : List Value) : WellFormedIndexed (ofList values) := by
  intro index outside
  exact List.getElem?_eq_none outside

def setAt (reference index : Nat) (value : Value) (state : IndexedState) : Except EvalError IndexedState :=
  if index < maximumArrayLength then
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some array => .ok {state with heap := state.heap.set reference (indexedSet array index value)}
  else .error .unsupported

def pushAt (reference : Nat) (value : Value) (state : IndexedState) : Except EvalError IndexedState :=
  match state.heap[reference]? with
  | none => .error .invalidReference
  | some array =>
    if array.length < maximumArrayLength then
      .ok {state with heap := state.heap.set reference (pushOwn array value)}
    else .error .unsupported

theorem setAt_found (state : IndexedState) (reference index : Nat) (value : Value) (array : IndexedArray)
    (found : state.heap[reference]? = some array) (legal : LegalArrayIndex index) :
    setAt reference index value state = .ok {state with heap := state.heap.set reference (indexedSet array index value)} := by
  change index < maximumArrayLength at legal
  simp [setAt, legal, found]
theorem pushAt_found (state : IndexedState) (reference : Nat) (value : Value) (array : IndexedArray)
    (found : state.heap[reference]? = some array) (legal : array.length < maximumArrayLength) :
    pushAt reference value state = .ok {state with heap := state.heap.set reference (pushOwn array value)} := by
  simp [pushAt, found, legal]

/-- Concat preserves missing own cells. The allocation endpoint specializes
effect-free standard species; this is no general getter/species order claim. -/
def concatOwn (left right : IndexedArray) : IndexedArray :=
  ⟨left.length + right.length, fun index =>
    if index < left.length then left.own index
    else if index < left.length + right.length then right.own (index - left.length) else none⟩

theorem concatOwn_wellFormed (left right : IndexedArray) : WellFormedIndexed (concatOwn left right) := by
  intro index outside
  change left.length + right.length ≤ index at outside
  have first : ¬ index < left.length := by change left.length + right.length ≤ index at outside; omega
  exact by simp [concatOwn, first, Nat.not_lt.mpr outside]

def concatAt (receiver : Nat) (argument : Value) (state : IndexedState) : Except EvalError (Value × IndexedState) := do
  let left ← match state.heap[receiver]? with
    | none => .error .invalidReference
    | some array => .ok array
  let right ← match argument with
    | .array reference => match state.heap[reference]? with
      | none => .error .invalidReference
      | some array => .ok array
    | value => .ok (ofList [value])
  if left.length + right.length ≤ maximumArrayLength then
    return (.array state.heap.length, {state with heap := state.heap ++ [concatOwn left right]})
  else .error .unsupported

theorem shiftSteps_length (array : IndexedArray) : (shiftSteps array).2.length = array.length - 1 := by
  by_cases empty : array.length = 0 <;> simp [shiftSteps, empty]

theorem shiftSteps_own_successor (array : IndexedArray) (index : Nat) (inside : index < array.length - 1) :
    (shiftSteps array).2.own index = array.own (index + 1) := by
  have nonempty : array.length ≠ 0 := by omega
  have different : index ≠ array.length - 1 := by omega
  simp [shiftSteps, nonempty, put, different, copyForward_properties, inside]

/-- Checked direct endpoint for the reference ascending-copy/delete algorithm.
Out-of-length own cells are preserved even for malformed inputs; the equality
below is unconditional, rather than relying on the native wellformed domain. -/
def shiftDirect (array : IndexedArray) : Value × IndexedArray :=
  if array.length = 0 then (.undefined, {array with length := 0})
  else (numericGet array 0, ⟨array.length - 1, fun index =>
    if index < array.length - 1 then array.own (index + 1)
    else if index = array.length - 1 then none else array.own index⟩)

private theorem sparseArray_ext {left right : IndexedArray} (length : left.length = right.length)
    (own : ∀ index, left.own index = right.own index) : left = right := by
  cases left
  cases right
  simp only [IndexedArray.mk.injEq]
  exact ⟨length, funext own⟩

theorem shiftDirect_eq_shiftSteps (array : IndexedArray) : shiftDirect array = shiftSteps array := by
  by_cases empty : array.length = 0
  · simp [shiftDirect, shiftSteps, empty]
  · apply Prod.ext
    · simp [shiftDirect, shiftSteps, empty]
    · apply sparseArray_ext
      · simp [shiftDirect, shiftSteps, empty]
      · intro index
        by_cases inside : index < array.length - 1
        · have different : index ≠ array.length - 1 := by omega
          simp [shiftDirect, shiftSteps, empty, inside, put, different, copyForward_properties]
        · by_cases last : index = array.length - 1
          · simp [shiftDirect, shiftSteps, empty, put, last]
          · simp [shiftDirect, shiftSteps, empty, inside, put, last, copyForward_properties]

def shiftAtDirect (reference : Nat) (state : IndexedState) : Except EvalError (Value × IndexedState) :=
  match state.heap[reference]? with
  | none => .error .invalidReference
  | some array =>
    let result := shiftDirect array
    .ok (result.1, {state with heap := state.heap.set reference result.2})

@[simp] theorem shiftAtDirect_eq_shiftAt (reference : Nat) (state : IndexedState) :
    shiftAtDirect reference state = shiftAt reference state := by
  simp only [shiftAtDirect, shiftAt, shiftDirect_eq_shiftSteps]
  rfl

/-- Out-of-domain ghost cells are intentionally retained so endpoint equality
does not silently depend on WellFormedIndexed or clip malformed inputs. -/
theorem shiftDirect_malformed_empty_control :
    (shiftDirect ⟨0, fun _ => some (.number 7)⟩).2.own 123 = some (.number 7) := rfl

theorem shiftDirect_malformed_nonempty_controls :
    (shiftDirect ⟨2, fun index => if index = 7 then some (.number 9) else none⟩).2.own 0 = none ∧
    (shiftDirect ⟨2, fun index => if index = 7 then some (.number 9) else none⟩).2.own 1 = none ∧
    (shiftDirect ⟨2, fun index => if index = 7 then some (.number 9) else none⟩).2.own 7 = some (.number 9) := by decide

/-- info: 'HonoLean.Upstream.ECMA2025.shiftDirect_eq_shiftSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftDirect_eq_shiftSteps
/-- info: 'HonoLean.Upstream.ECMA2025.shiftAtDirect_eq_shiftAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftAtDirect_eq_shiftAt

theorem shiftSteps_wellFormed (array : IndexedArray) (wellFormed : WellFormedIndexed array) :
    WellFormedIndexed (shiftSteps array).2 := by
  intro index outside
  rw [shiftSteps_length] at outside
  by_cases empty : array.length = 0
  · simpa [shiftSteps, empty] using wellFormed index (by omega)
  · by_cases last : index = array.length - 1
    · simp [shiftSteps, empty, put, last]
    · have old : array.length ≤ index := by omega
      simp [shiftSteps, empty, put, last, copyForward_properties, Nat.not_lt.mpr outside, wellFormed index old]

theorem observe_getElem? (array : IndexedArray) (index : Nat) :
    (observe array)[index]? = if index < array.length then some (numericGet array index) else none := by
  simp [observe, List.getElem?_ofFn]

theorem observe_shiftSteps (array : IndexedArray) : observe (shiftSteps array).2 = (observe array).tail := by
  apply List.ext_getElem?
  intro index
  rw [observe_getElem?, List.getElem?_tail, observe_getElem?, shiftSteps_length]
  by_cases inside : index < array.length - 1
  · have next : index + 1 < array.length := by omega
    simp [inside, next, numericGet, shiftSteps_own_successor array index inside]
  · have next : ¬ index + 1 < array.length := by omega
    simp [inside, next]

theorem observe_concatOwn (left right : IndexedArray) : observe (concatOwn left right) = observe left ++ observe right := by
  apply List.ext_getElem?
  intro index
  rw [observe_getElem?]
  have leftLength : (observe left).length = left.length := by simp [observe]
  by_cases first : index < left.length
  · rw [List.getElem?_append_left (by simpa [observe] using first), observe_getElem?]
    have total : index < left.length + right.length := by omega
    simp [concatOwn, first, total, numericGet]
  · rw [List.getElem?_append_right (by simpa [observe] using Nat.le_of_not_lt first), observe_getElem?]
    by_cases total : index < left.length + right.length
    · have second : index - left.length < right.length := by omega
      simp [concatOwn, first, total, second, numericGet, leftLength]
    · have second : ¬ index - left.length < right.length := by omega
      simp [concatOwn, total, second, leftLength]

/-- Read-value erasure only. Holes become undefined in this observer;
the authoritative sparse heap is neither changed nor made dense. -/
def eraseIndexedState (state : IndexedState) : State :=
  {environment := state.environment, heap := state.heap.map observe}

/-- Preserve an explicitly supplied ambient nonarray frame. The shorter
eraseIndexedState above is only a queue/read observer with default other fields,
not a reconstruction of Node/private/object execution context. -/
def embedIndexedState (ambient : State) (state : IndexedState) : State :=
  {ambient with environment := state.environment, heap := state.heap.map observe}

theorem embedIndexedState_frames (ambient : State) (state : IndexedState) :
    (embedIndexedState ambient state).objects = ambient.objects ∧
    (embedIndexedState ambient state).functions = ambient.functions ∧
    (embedIndexedState ambient state).privates = ambient.privates ∧
    (embedIndexedState ambient state).sets = ambient.sets ∧
    (embedIndexedState ambient state).thisValue = ambient.thisValue := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem numericGet_observe (array : IndexedArray) (index : Nat) (wellFormed : WellFormedIndexed array) :
    numericGet array index = (observe array)[index]?.getD .undefined := by
  rw [observe_getElem?]
  by_cases inside : index < array.length
  · simp [inside]
  · simp [inside, numericGet, wellFormed index (Nat.le_of_not_lt inside)]

theorem shiftSteps_head (array : IndexedArray) (wellFormed : WellFormedIndexed array) :
    (shiftSteps array).1 = numericGet array 0 := by
  by_cases empty : array.length = 0
  · simp [shiftSteps, empty, numericGet, wellFormed 0 (by omega)]
  · simp [shiftSteps, empty]

theorem numericGet_array_own (array : IndexedArray) (index reference : Nat)
    (found : numericGet array index = .array reference) : array.own index = some (.array reference) := by
  cases own : array.own index with
  | none => simp [numericGet, own] at found
  | some value => simpa [numericGet, own] using congrArg some found

theorem numericGet_array_inside (array : IndexedArray) (index reference : Nat)
    (wellFormed : WellFormedIndexed array) (found : numericGet array index = .array reference) : index < array.length := by
  by_cases inside : index < array.length
  · exact inside
  · have outside := Nat.le_of_not_lt inside
    have absent := wellFormed index outside
    rw [numericGet_array_own array index reference found] at absent
    cases absent

end HonoLean.Upstream.ECMA2025
