import HonoLean.Upstream.SourceSubset.Semantics
import Init.Data.List.OfFn

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-- A finite indexed-own-property description. Named properties, descriptors,
proxies, accessors and prototype lookup are outside this representation. The
refinement below concerns ordinary dense arrays with writable/enumerable/
configurable indexed data properties, standard writable length, and no inherited
indexed properties or replaced intrinsics. -/
structure IndexedArray where
  length : Nat
  own : Nat → Option Value

def maximumArrayLength : Nat := 4294967295
def LegalArrayLength (array : IndexedArray) : Prop := array.length ≤ maximumArrayLength

def ofList (elements : List Value) : IndexedArray := ⟨elements.length, fun i => elements[i]?⟩

def Represents (array : IndexedArray) (elements : List Value) : Prop :=
  array.length = elements.length ∧ ∀ i, array.own i = elements[i]?

def numericGet (array : IndexedArray) (index : Nat) : Value :=
  (array.own index).getD .undefined

def put (properties : Nat → Option Value) (index : Nat) (value : Option Value) :
    Nat → Option Value := fun key => if key = index then value else properties key

/-- Ascending copy steps: read source k+1, then write destination k. A missing
own source deletes the destination; only the dense clean-prototype case is
claimed by the public refinement theorem. This is not a list-tail definition. -/
def copyForward (destination : Nat) : Nat → (Nat → Option Value) → (Nat → Option Value)
  | 0, properties => properties
  | count + 1, properties =>
    copyForward (destination + 1) count
      (put properties destination (properties (destination + 1)))

/-- The empty branch returns undefined. Otherwise preserve the original first
value, perform ascending copies, delete the old last property, then set length.
No generic-object, throwing descriptor, sparse-array or proxy claim is made. -/
def shiftSteps (array : IndexedArray) : Value × IndexedArray :=
  if array.length = 0 then (.undefined, {array with length := 0})
  else
    (numericGet array 0,
      ⟨array.length - 1,
       put (copyForward 0 (array.length - 1) array.own) (array.length - 1) none⟩)

theorem copyForward_properties (count destination : Nat) (properties : Nat → Option Value)
    (index : Nat) :
    copyForward destination count properties index =
      if destination ≤ index ∧ index < destination + count then properties (index + 1)
      else properties index := by
  induction count generalizing destination properties with
  | zero =>
    have impossible : ¬ (destination ≤ index ∧ index < destination + 0) := by omega
    change properties index = if destination ≤ index ∧ index < destination + 0 then
      properties (index + 1) else properties index
    rw [ite_eq_right impossible]
  | succ count ih =>
    rw [copyForward, ih]
    by_cases zone : destination + 1 ≤ index ∧ index < destination + 1 + count
    · have unequal : index + 1 ≠ destination := by omega
      have total : destination ≤ index ∧ index < destination + (count + 1) := by omega
      simp [zone, total, put, unequal]
    · by_cases same : index = destination
      · subst index
        simp [zone, put]
      · have outside : ¬ (destination ≤ index ∧ index < destination + (count + 1)) := by omega
        simp [zone, outside, put, same]

theorem represents_ofList (elements : List Value) : Represents (ofList elements) elements :=
  ⟨rfl, fun _ => rfl⟩

theorem numericGet_refinement {array : IndexedArray} {elements : List Value}
    (representation : Represents array elements) (index : Nat) :
    numericGet array index = elements[index]?.getD .undefined := by
  simp [numericGet, representation.2 index]

private theorem indexed_ext {a b : IndexedArray} (length : a.length = b.length)
    (properties : ∀ i, a.own i = b.own i) : a = b := by
  cases a; cases b
  simp_all only [IndexedArray.mk.injEq]
  exact ⟨True.intro, funext properties⟩

theorem represents_eq_ofList {array : IndexedArray} {elements : List Value}
    (representation : Represents array elements) : array = ofList elements :=
  indexed_ext representation.1 representation.2

def observe (array : IndexedArray) : List Value :=
  List.ofFn (fun index : Fin array.length => numericGet array index.val)

theorem observe_ofList (elements : List Value) : observe (ofList elements) = elements := by
  simp [observe, numericGet, ofList, List.ofFn_getElem]

theorem observe_representation {array : IndexedArray} {elements : List Value}
    (representation : Represents array elements) : observe array = elements := by
  rw [represents_eq_ofList representation, observe_ofList]

theorem shiftSteps_ofList (elements : List Value) :
    shiftSteps (ofList elements) = (elements.headD .undefined, ofList elements.tail) := by
  cases elements with
  | nil => rfl
  | cons first rest =>
    apply Prod.ext
    · simp [shiftSteps, ofList, numericGet]
    · apply indexed_ext
      · simp [shiftSteps, ofList]
      · intro index
        simp only [shiftSteps, ofList, List.length_cons, Nat.add_one_ne_zero,
          ↓reduceIte, Nat.add_sub_cancel, put, copyForward_properties,
          Nat.zero_le, Nat.zero_add, true_and]
        by_cases before : index < rest.length
        · have unequal : index ≠ rest.length := by omega
          simp [before, unequal]
        · by_cases last : index = rest.length
          · simp [last]
          · simp [before, last]
            omega

/-- Representation refinement between two declared descriptions, under the
explicit legal-length and ordinary dense-array assumptions above. It is not a
formal derivation of the full ECMA-262 abstract operations or engine behavior. -/
theorem dense_shift_refinement (elements : List Value)
    (legal : elements.length ≤ maximumArrayLength) :
    (shiftSteps (ofList elements)).1 = elements.headD .undefined ∧
    Represents (shiftSteps (ofList elements)).2 elements.tail ∧
    LegalArrayLength (shiftSteps (ofList elements)).2 := by
  rw [shiftSteps_ofList]
  exact ⟨rfl, represents_ofList _, by
    simp only [LegalArrayLength, ofList]
    simp only [List.length_tail]
    omega⟩

theorem shiftSteps_representation {array : IndexedArray} {elements : List Value}
    (representation : Represents array elements) (legal : LegalArrayLength array) :
    (shiftSteps array).1 = elements.headD .undefined ∧
    Represents (shiftSteps array).2 elements.tail ∧
    LegalArrayLength (shiftSteps array).2 := by
  have canonical := represents_eq_ofList representation
  rw [canonical] at legal ⊢
  exact dense_shift_refinement elements legal

structure IndexedState where
  environment : List (String × Value) := []
  heap : List IndexedArray := []

def liftState (state : State) : IndexedState :=
  ⟨state.environment, state.heap.map ofList⟩

/-- References are abstract heap addresses, not JavaScript Number values. -/
def allocateFresh (elements : List Value) (state : IndexedState) : Value × IndexedState :=
  (.array state.heap.length, {state with heap := state.heap ++ [ofList elements]})

theorem allocateFresh_refinement (state : State) (elements : List Value) :
    allocateFresh elements (liftState state) =
      (.array state.heap.length,
       liftState {state with heap := state.heap ++ [elements]}) := by
  simp [allocateFresh, liftState]

theorem allocateFresh_preserves_other_cells (state : IndexedState) (elements : List Value)
    (reference : Nat) (existing : reference < state.heap.length) :
    (allocateFresh elements state).2.heap[reference]? = state.heap[reference]? := by
  exact List.getElem?_append_left existing

theorem allocateFresh_new_cell (state : IndexedState) (elements : List Value) :
    (allocateFresh elements state).2.heap[state.heap.length]? = some (ofList elements) := by
  simp [allocateFresh]

theorem split_allocation_refinement (state : State) (input : JSString)
    (separator : UInt16) (limit : Nat) :
    (intrinsic limit (.string input) "split" [.string [separator]] state).map
        (fun result => (result.1, liftState result.2)) =
      .ok (allocateFresh (((input.splitOn separator).take limit).map Value.string)
        (liftState state)) := by
  simp [intrinsic, Except.map, allocateFresh, liftState]

theorem split_allocation_legal (input : JSString) (separator : UInt16) (limit : Nat)
    (legalLimit : limit ≤ maximumArrayLength) :
    LegalArrayLength (ofList (((input.splitOn separator).take limit).map Value.string)) := by
  simp only [LegalArrayLength, ofList, List.length_map, List.length_take]
  omega

def shiftAt (reference : Nat) (state : IndexedState) :
    Except EvalError (Value × IndexedState) :=
  match state.heap[reference]? with
  | none => .error .invalidReference
  | some array =>
    let shifted := shiftSteps array
    .ok (shifted.1, {state with heap := state.heap.set reference shifted.2})

theorem shiftAt_refinement (state : State) (reference limit : Nat) :
    shiftAt reference (liftState state) =
      (intrinsic limit (.array reference) "shift" [] state).map
        (fun result => (result.1, liftState result.2)) := by
  cases found : state.heap[reference]? with
  | none => simp [shiftAt, liftState, intrinsic, found, Except.map]
  | some elements =>
    simp [shiftAt, liftState, intrinsic, found, shiftSteps_ofList, Except.map, List.map_set]

theorem shiftAt_preserves_environment (state next : IndexedState) (reference : Nat)
    (value : Value) (shifted : shiftAt reference state = .ok (value, next)) :
    next.environment = state.environment := by
  cases found : state.heap[reference]? with
  | none => simp [shiftAt, found] at shifted
  | some array =>
    simp only [shiftAt, found, Except.ok.injEq, Prod.mk.injEq] at shifted
    rw [← shifted.2]

theorem shiftAt_preserves_alias (state next : IndexedState) (reference : Nat)
    (value : Value) (name : String)
    (shifted : shiftAt reference state = .ok (value, next)) :
    next.environment.lookup name = state.environment.lookup name := by
  rw [shiftAt_preserves_environment state next reference value shifted]

theorem shift_preserves_other_cells (state : State) (reference other : Nat)
    (elements : List Value) (found : state.heap[reference]? = some elements)
    (different : other ≠ reference) :
    intrinsic 0 (.array reference) "shift" [] state =
      .ok (elements.headD .undefined, {state with heap := state.heap.set reference elements.tail}) ∧
    (state.heap.set reference elements.tail)[other]? = state.heap[other]? := by
  exact ⟨by simp [intrinsic, found], List.getElem?_set_ne (Ne.symm different)⟩

theorem index_eval_refinement (state : State) (name : String)
    (reference index limit : Nat) (elements : List Value)
    (binding : state.environment.lookup name = some (.array reference))
    (found : state.heap[reference]? = some elements) :
    evalExpression 2 limit (.index (.variable name) (.number index)) state =
      .ok (numericGet (ofList elements) index, state) := by
  simp [evalExpression, lookupVariable, binding, found, numericGet, ofList,
    bind, pure, Except.bind, Except.pure]

/-- Values reachable by this fragment's array indexing before comparison with
the empty string. This domain intentionally excludes all number semantics. -/
inductive StringOrUndefined : Value → Prop where
  | string (contents : JSString) : StringOrUndefined (.string contents)
  | undefined : StringOrUndefined .undefined

theorem string_field_get_reachable (fields : List JSString) (index : Nat) :
    StringOrUndefined (numericGet (ofList (fields.map Value.string)) index) := by
  cases found : fields[index]? with
  | none => simp [numericGet, ofList, found]; exact .undefined
  | some contents => simp [numericGet, ofList, found]; exact .string contents

def equalsEmpty : Value → Except EvalError Bool
  | .string contents => .ok contents.isEmpty
  | .undefined => .ok false
  | _ => .error .unsupported

theorem equalsEmpty_refinement (value : Value) (reachable : StringOrUndefined value) :
    equalsEmpty value = .ok (decide (value = .string [])) := by
  cases reachable with
  | string contents => cases contents <;> rfl
  | undefined => rfl

/-- info: 'HonoLean.Upstream.ECMA2025.shiftSteps_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftSteps_ofList

end HonoLean.Upstream.ECMA2025
