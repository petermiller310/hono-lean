import HonoLean.Upstream.SourceSubset.ArrayIterator

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Initial ordinary prototype edges stay inside the old heap. This is a
structural input condition, not a desired future lookup/iterator execution. -/
def IteratorPrototypeClosed (heap : ObjectHeap) : Prop :=
  ∀ (reference : Nat) (object : OrdinaryObject), heap[reference]? = some object →
    ∀ (parent : Nat), object.prototype = some parent → parent < heap.length

theorem iterator_lookup_append (heap extra : ObjectHeap) (closed : IteratorPrototypeClosed heap)
    (fuel holder : Nat) (key : JSString) (old : holder < heap.length) :
    lookupProperty fuel (heap ++ extra) holder key = lookupProperty fuel heap holder key := by
  induction fuel generalizing holder with
  | zero => rfl
  | succ fuel ih =>
    have found := (List.getElem?_eq_some_iff.mpr ⟨old, rfl⟩ : heap[holder]? = some heap[holder])
    have appended : (heap ++ extra)[holder]? = some heap[holder] := (List.getElem?_append_left old).trans found
    simp only [lookupProperty, found, appended]
    cases own : heap[holder].own.lookup key with
    | some descriptor => rfl
    | none =>
      cases proto : heap[holder].prototype with
      | none => rfl
      | some parent => exact ih parent (closed holder heap[holder] found parent proto)

theorem iterator_get_append (heap extra : ObjectHeap) (closed : IteratorPrototypeClosed heap)
    (fuel holder : Nat) (key : JSString) (old : holder < heap.length) :
    getProperty fuel (heap ++ extra) holder key = getProperty fuel heap holder key := by
  rw [getProperty, iterator_lookup_append heap extra closed fuel holder key old, getProperty]
  cases resolved : lookupProperty fuel heap holder key with
  | error error => rfl
  | ok descriptor =>
    cases descriptor with
    | none => rfl
    | some descriptor =>
      cases descriptor with
      | data value writable enumerable configurable => rfl
      | accessor getter setter enumerable configurable =>
        cases getter with
        | missing | unsupported => rfl
        | prototype =>
          simp only [bind, Except.bind, callGetter, List.getElem?_append_left old]

/-- All array-owner symbol overrides refer to already allocated arrays. The
fresh tuple from the constructor therefore has no own Symbol.iterator entry. -/
def ArraySymbolsAllocated (before : ArrayBindingState) : Prop :=
  ∀ fields ∈ before.symbols, ∀ reference, fields.1 = .array reference → reference < before.regexp.ambient.heap.length

theorem symbolOwn_fresh_array (before : ArrayBindingState) (allocated : ArraySymbolsAllocated before)
    (reference : Nat) (fresh : before.regexp.ambient.heap.length ≤ reference) :
    symbolOwn before (.array reference) = none := by
  have missing : before.symbols.lookup (.array reference) = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    have unequal : ArraySymbolOwner.array reference ≠ entry.1 := by
      intro equal
      have bound := allocated entry member reference equal.symm
      omega
    simpa using unequal
  simp [symbolOwn, missing]

/-- Explicit result endpoint. Both value and done are OWN W/E/C DATA properties
on a newly allocated Object.prototype-linked ordinary cell. -/
def iteratorResultState (context : ArrayIteratorContext) (value : Value) (done : Bool) (before : ArrayBindingState) : ArrayBindingState :=
  {before with
    regexp := {before.regexp with ambient := {before.regexp.ambient with
      objects := before.regexp.ambient.objects ++ [iteratorResultObject context.resultPrototype value done]}}
    trace := before.trace ++ [.resultAllocated before.regexp.ambient.objects.length value done]}

theorem allocateIteratorResult_eq (context : ArrayIteratorContext) (value : Value) (done : Bool)
    (before : ArrayBindingState) (root : OrdinaryObject)
    (found : before.regexp.ambient.objects[context.resultPrototype]? = some root) :
    allocateIteratorResult context value done before =
      .ok (before.regexp.ambient.objects.length, iteratorResultState context value done before) := by
  simp [allocateIteratorResult, found, iteratorResultState, bind, Except.bind, pure, Except.pure]

def iteratorYieldState (context : ArrayIteratorContext) (reference array index : Nat) (values : List Value)
    (before : ArrayBindingState) : ArrayBindingState :=
  let measured := {before with trace := before.trace ++ [.lengthGet array values.length]}
  let advanced := setArrayIteratorCursor reference ⟨some array, index + 1⟩ measured
  iteratorResultState context (values[index]?.getD .undefined) false
    {advanced with trace := advanced.trace ++ [.elementGet array index (values[index]?.getD .undefined)]}

def iteratorExhaustedState (context : ArrayIteratorContext) (reference array index : Nat) (values : List Value)
    (before : ArrayBindingState) : ArrayBindingState :=
  let measured := {before with trace := before.trace ++ [.lengthGet array values.length]}
  iteratorResultState context .undefined true (setArrayIteratorCursor reference ⟨none, index⟩ measured)

theorem arrayIteratorNext_yield (context : ArrayIteratorContext) (reference array index : Nat) (values : List Value)
    (before : ArrayBindingState) (root : OrdinaryObject)
    (cursor : before.iterators.lookup reference = some ⟨some array, index⟩)
    (found : before.regexp.ambient.heap[array]? = some values)
    (rootFound : before.regexp.ambient.objects[context.resultPrototype]? = some root)
    (inBounds : index < values.length) :
    arrayIteratorNext context reference before =
      .ok (before.regexp.ambient.objects.length, iteratorYieldState context reference array index values before) := by
  simp only [arrayIteratorNext, cursor, found, bind, Except.bind, inBounds, ↓reduceIte]
  simp only [readProperty, found, Except.mapError]
  simp [allocateIteratorResult, setArrayIteratorCursor, rootFound, iteratorYieldState, iteratorResultState] <;> rfl

theorem arrayIteratorNext_exhausted (context : ArrayIteratorContext) (reference array index : Nat) (values : List Value)
    (before : ArrayBindingState) (root : OrdinaryObject)
    (cursor : before.iterators.lookup reference = some ⟨some array, index⟩)
    (found : before.regexp.ambient.heap[array]? = some values)
    (rootFound : before.regexp.ambient.objects[context.resultPrototype]? = some root)
    (outOfBounds : values.length ≤ index) :
    arrayIteratorNext context reference before =
      .ok (before.regexp.ambient.objects.length, iteratorExhaustedState context reference array index values before) := by
  simp only [arrayIteratorNext, cursor, found, bind, Except.bind, Nat.not_lt.mpr outOfBounds, ↓reduceIte]
  simp [allocateIteratorResult, setArrayIteratorCursor, rootFound, iteratorExhaustedState, iteratorResultState] <;> rfl

theorem arrayIteratorNext_completed (context : ArrayIteratorContext) (reference index : Nat) (before : ArrayBindingState)
    (root : OrdinaryObject) (cursor : before.iterators.lookup reference = some ⟨none, index⟩)
    (rootFound : before.regexp.ambient.objects[context.resultPrototype]? = some root) :
    arrayIteratorNext context reference before =
      .ok (before.regexp.ambient.objects.length, iteratorResultState context .undefined true before) := by
  simp only [arrayIteratorNext, cursor, bind, Except.bind]
  exact allocateIteratorResult_eq context .undefined true before root rootFound

/-- The saved next identity is used even if its ordinary property later changes.
The equation requires only current table/record input facts, no desired output. -/
theorem invokeArrayIteratorNext_saved (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState)
    (separated : iteratorTablesSeparated context before.regexp.ambient = true)
    (identity : iteratorBuiltinAt context.builtins record.nextMethod = some .arrayNext) :
    invokeArrayIteratorNext context record before = arrayIteratorNext context record.iterator before := by
  simp [invokeArrayIteratorNext, separated, identity]

/-- Elision consumes exactly IteratorStep, with no IteratorValue expression. -/
theorem bindArrayElements_elision (fuel : Nat) (context : ArrayIteratorContext) (tail : List ArrayBindingElement)
    (record nextRecord : ArrayIteratorRecord) (before after : ArrayBindingState) (result : Option Nat)
    (stepped : iteratorStep context record before = .ok (result, nextRecord, after)) :
    bindArrayElements (fuel + 1) context (.elision :: tail) record before =
      bindArrayElements fuel context tail nextRecord after := by
  simp only [bindArrayElements, stepped, bind, Except.bind]

theorem iteratorStep_already_done (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState)
    (done : record.done = true) : iteratorStep context record before = .ok (none, record, before) := by
  simp [iteratorStep, done, pure, Except.pure]

/-- Nullish GetMethod(return) preserves the record and cursor, and reads the
CURRENT complete ordinary property path. It never performs a fourth next. -/
theorem closeArrayIterator_nullish (record : ArrayIteratorRecord) (before : ArrayBindingState) (value : Value)
    (notDone : record.done = false)
    (read : getProperty propertyFuel before.regexp.ambient.objects record.iterator iteratorReturnKey = .ok value)
    (nullish : value = .undefined ∨ value = .null) :
    closeArrayIterator record before = .ok {before with trace := before.trace ++ [.returnGet record.iterator value]} := by
  rcases nullish with rfl | rfl <;>
    simp [closeArrayIterator, notDone, read, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem closeArrayIterator_done (record : ArrayIteratorRecord) (before : ArrayBindingState) (done : record.done = true) :
    closeArrayIterator record before = .ok before := by
  simp [closeArrayIterator, done, pure, Except.pure]

/-- Actual allocated result properties, not a trusted value/done callback. -/
theorem iteratorResult_reads (context : ArrayIteratorContext) (before : ArrayBindingState) (value : Value) (done : Bool) :
    getProperty propertyFuel (iteratorResultState context value done before).regexp.ambient.objects
      before.regexp.ambient.objects.length iteratorDoneKey = .ok (.boolean done) ∧
    getProperty propertyFuel (iteratorResultState context value done before).regexp.ambient.objects
      before.regexp.ambient.objects.length iteratorValueKey = .ok value := by
  have found : (iteratorResultState context value done before).regexp.ambient.objects[before.regexp.ambient.objects.length]? =
      some (iteratorResultObject context.resultPrototype value done) := by simp [iteratorResultState]
  constructor
  · exact getProperty_data _ _ (propertyFuel - 1) _ _ _ true true true found (by rfl)
  · exact getProperty_data _ _ (propertyFuel - 1) _ _ _ true true true found (by rfl)

/-- Pure descriptor reads, independently classified from Get. In particular
no accessor callback or receiver-sensitive prototype getter is assumed pure. -/
inductive IteratorPureRead : Option PropertyDescriptor → Value → Prop where
  | absent : IteratorPureRead none .undefined
  | data (value : Value) (writable enumerable configurable : Bool) :
      IteratorPureRead (some (.data value writable enumerable configurable)) value
  | missing (setter : Setter) (enumerable configurable : Bool) :
      IteratorPureRead (some (.accessor .missing setter enumerable configurable)) .undefined

theorem iterator_get_of_lookup (fuel : Nat) (heap : ObjectHeap) (reference : Nat) (key : JSString)
    (descriptor : Option PropertyDescriptor) (value : Value)
    (resolved : lookupProperty fuel heap reference key = .ok descriptor)
    (pureRead : IteratorPureRead descriptor value) :
    getProperty fuel heap reference key = .ok value := by
  cases pureRead <;> simp [getProperty, resolved, callGetter, bind, Except.bind, pure, Except.pure]

/-- Full inherited descriptor lookup from an actually allocated fresh iterator.
The old prototype chain is retained, not shortened to own-return absence. -/
theorem iterator_new_lookup (before : ArrayBindingState) (prototype : Nat)
    (closed : IteratorPrototypeClosed before.regexp.ambient.objects) (old : prototype < before.regexp.ambient.objects.length)
    (fuel : Nat) (key : JSString) :
    lookupProperty (fuel + 1) (before.regexp.ambient.objects ++ [arrayIteratorObject prototype])
      before.regexp.ambient.objects.length key =
    lookupProperty fuel before.regexp.ambient.objects prototype key := by
  have found : (before.regexp.ambient.objects ++ [arrayIteratorObject prototype])[before.regexp.ambient.objects.length]? =
      some (arrayIteratorObject prototype) := by simp
  rw [lookupProperty, found]
  dsimp only [arrayIteratorObject, List.lookup]
  exact iterator_lookup_append _ _ closed fuel prototype key old

def arrayIteratorAcquiredState (context : ArrayIteratorContext) (array : Nat) (method next : Value) (before : ArrayBindingState) : ArrayBindingState :=
  let measured := {before with trace := before.trace ++ [.symbolGet array method]}
  let allocated := allocateArrayIterator context array measured
  {allocated with trace := allocated.trace ++ [.nextGet before.regexp.ambient.objects.length next]}

theorem getArrayIterator_standard (context : ArrayIteratorContext) (array : Nat) (before : ArrayBindingState)
    (method next : Value) (prototypeObject : OrdinaryObject)
    (currentMethod : getArrayIteratorMethod context array before = .ok method)
    (separated : iteratorTablesSeparated context before.regexp.ambient = true)
    (identity : iteratorBuiltinAt context.builtins method = some .arrayValues)
    (prototypeFound : before.regexp.ambient.objects[context.iteratorPrototype]? = some prototypeObject)
    (closed : IteratorPrototypeClosed before.regexp.ambient.objects)
    (nextDescriptor : lookupProperty (propertyFuel - 1) before.regexp.ambient.objects context.iteratorPrototype iteratorNextKey =
      .ok (some (.data next true false true))) :
    getArrayIterator context (.array array) before =
      .ok (⟨before.regexp.ambient.objects.length, next, false⟩,
        arrayIteratorAcquiredState context array method next before) := by
  have bound := (List.getElem?_eq_some_iff.mp prototypeFound).1
  have resolved := iterator_new_lookup before context.iteratorPrototype closed bound (propertyFuel - 1) iteratorNextKey
  have budget : propertyFuel - 1 + 1 = propertyFuel := by decide
  rw [budget, nextDescriptor] at resolved
  have readNext := iterator_get_of_lookup propertyFuel _ _ _ _ next resolved (.data next true false true)
  simp only [getArrayIterator, currentMethod, bind, Except.bind]
  simp only [separated, Bool.not_true, identity, bne_self_eq_false, prototypeFound]
  simp only [allocateArrayIterator] at readNext ⊢
  rw [readNext]
  rfl

/-- Guarded binding step: one next and done Get, deliberately no value Get. -/
theorem iteratorStep_yield (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState)
    (after : ArrayBindingState) (result : Nat)
    (notDone : record.done = false)
    (next : invokeArrayIteratorNext context record before = .ok (result, after))
    (doneRead : getProperty propertyFuel after.regexp.ambient.objects result iteratorDoneKey = .ok (.boolean false)) :
    iteratorStep context record before =
      .ok (some result, record, {after with trace := after.trace ++ [.doneGet result (.boolean false)]}) := by
  simp [iteratorStep, notDone, next, doneRead, Except.mapError, truthy, bind, Except.bind, pure, Except.pure]

theorem iteratorStepValue_yield (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState)
    (after : ArrayBindingState) (result : Nat) (value : Value)
    (notDone : record.done = false)
    (next : invokeArrayIteratorNext context record before = .ok (result, after))
    (doneRead : getProperty propertyFuel after.regexp.ambient.objects result iteratorDoneKey = .ok (.boolean false))
    (valueRead : getProperty propertyFuel after.regexp.ambient.objects result iteratorValueKey = .ok value) :
    iteratorStepValue context record before =
      .ok (value, record, {after with trace := after.trace ++ [.doneGet result (.boolean false), .valueGet result value]}) := by
  rw [iteratorStepValue, iteratorStep_yield context record before after result notDone next doneRead]
  simp [iteratorValue, valueRead, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Full unchanged ordinary/source components of every concrete yield state.
Result and iterator allocations are ordinary projected cells, so object-heap
identity is deliberately NOT a frame claim. -/
theorem iteratorYield_frames (context : ArrayIteratorContext) (reference array index : Nat) (values : List Value)
    (before : ArrayBindingState) :
    (iteratorYieldState context reference array index values before).regexp.ambient.heap = before.regexp.ambient.heap ∧
    (iteratorYieldState context reference array index values before).regexp.ambient.environment = before.regexp.ambient.environment ∧
    (iteratorYieldState context reference array index values before).regexp.ambient.functions = before.regexp.ambient.functions ∧
    (iteratorYieldState context reference array index values before).regexp.ambient.privates = before.regexp.ambient.privates ∧
    (iteratorYieldState context reference array index values before).regexp.ambient.sets = before.regexp.ambient.sets ∧
    (iteratorYieldState context reference array index values before).regexp.ambient.thisValue = before.regexp.ambient.thisValue ∧
    (iteratorYieldState context reference array index values before).regexp.brands = before.regexp.brands ∧
    (iteratorYieldState context reference array index values before).regexp.results = before.regexp.results ∧
    (iteratorYieldState context reference array index values before).symbols = before.symbols := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end HonoLean.Upstream.SourceSubset
