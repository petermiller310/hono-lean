import HonoLean.Upstream.SourceSubset.Semantics

set_option autoImplicit false

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-! Ordinary own-string, frozen data-only CopyDataProperties specialization.
All own names are considered, then descriptors/enumerability; nonenumerable
accessors skip Get, enumerable accessors are an explicit unsupported frontier.
Symbols, proxies, getters/mutation, primitive boxing and native resources stay
open. Own-store order is representative only; extensional results below cover
every complete duplicate-free own-string-key order, a native-order overapprox.
-/

structure OwnStringKeyOrder (source : OrdinaryObject) (keys : List JSString) : Prop where
  unique : keys.Nodup
  complete : ∀ key, key ∈ keys ↔ ∃ descriptor, source.own.lookup key = some descriptor

def ownStringKeys (source : OrdinaryObject) : List JSString := source.own.map Prod.fst

theorem ownStringKeys_complete (source : OrdinaryObject) (key : JSString) :
    key ∈ ownStringKeys source ↔ ∃ descriptor, source.own.lookup key = some descriptor := by
  constructor
  · intro member
    cases found : source.own.lookup key with
    | some descriptor => exact ⟨descriptor, rfl⟩
    | none =>
      obtain ⟨entry, inSource, same⟩ := List.mem_map.mp member
      have absent := List.lookup_eq_none_iff.mp found entry inSource
      simp [same] at absent
  · rintro ⟨descriptor, found⟩
    obtain ⟨front, back, equation, _⟩ := List.lookup_eq_some_iff.mp found
    simp [ownStringKeys, equation]

theorem ownStringKeys_order (source : OrdinaryObject) (wellFormed : WellFormedObject source) :
    OwnStringKeyOrder source (ownStringKeys source) := ⟨wellFormed, ownStringKeys_complete source⟩

def CopyReady (source : OrdinaryObject) : Prop :=
  ∀ key getter setter configurable,
    source.own.lookup key = some (.accessor getter setter true configurable) → False

/-- Only enumerable own DATA descriptors contribute values; this independent
specification does not invoke a getter, copy loop or object-expression evaluator. -/
def spreadValue (source : OrdinaryObject) (key : JSString) : Option Value :=
  match source.own.lookup key with
  | some (.data value _ true _) => some value
  | _ => none

def copiedDescriptor (source : OrdinaryObject) (key : JSString) : Option PropertyDescriptor :=
  (spreadValue source key).map (fun value => .data value true true true)

structure SpreadTargetReady (target : OrdinaryObject) : Prop where
  extensible : target.extensible = true
  ownData : ∀ key descriptor, target.own.lookup key = some descriptor → ∃ value, descriptor = .data value true true true

theorem emptyLiteral_spreadReady : SpreadTargetReady emptyLiteralObject := by
  refine ⟨rfl, ?_⟩
  intro key descriptor found
  cases found

theorem spread_putOwn_other (key other : JSString) (descriptor : PropertyDescriptor)
    (properties : List (JSString × PropertyDescriptor)) (different : other ≠ key) :
    (putOwn key descriptor properties).lookup other = properties.lookup other := by
  have unequal := beq_false_of_ne different
  induction properties with
  | nil => simp [putOwn, List.lookup_cons, unequal]
  | cons entry rest ih =>
    obtain ⟨name, old⟩ := entry
    by_cases same : name = key
    · subst name
      simpa [putOwn, List.lookup_cons, unequal] using ih
    · have filtered : (rest.filter (fun entry => entry.1 != key)).lookup other = rest.lookup other := by
        simpa [putOwn, List.lookup_cons, unequal] using ih
      simp [putOwn, List.lookup_cons, same, filtered, unequal]

theorem newDataObject_spreadReady (target : OrdinaryObject) (key : JSString) (value : Value)
    (ready : SpreadTargetReady target) : SpreadTargetReady (newDataObject target key value) := by
  refine ⟨ready.extensible, ?_⟩
  intro other descriptor found
  by_cases same : other = key
  · subst other
    rw [newDataObject, putOwn_self] at found
    exact ⟨value, (Option.some.inj found).symm⟩
  · rw [newDataObject, spread_putOwn_other key other _ _ same] at found
    exact ready.ownData other descriptor found

def spreadFold (source : OrdinaryObject) : List JSString → OrdinaryObject → OrdinaryObject
  | [], target => target
  | key :: rest, target =>
    spreadFold source rest (match spreadValue source key with | none => target | some value => newDataObject target key value)

theorem spreadFold_ready (source : OrdinaryObject) (keys : List JSString) (target : OrdinaryObject)
    (ready : SpreadTargetReady target) : SpreadTargetReady (spreadFold source keys target) := by
  induction keys generalizing target with
  | nil => exact ready
  | cons key rest ih =>
    cases found : spreadValue source key with
    | none => simpa [spreadFold, found] using ih target ready
    | some value => simpa [spreadFold, found] using ih (newDataObject target key value) (newDataObject_spreadReady target key value ready)

theorem spreadFold_prototype (source : OrdinaryObject) (keys : List JSString) (target : OrdinaryObject) :
    (spreadFold source keys target).prototype = target.prototype := by
  induction keys generalizing target with
  | nil => rfl
  | cons key rest ih =>
    cases found : spreadValue source key <;> simp [spreadFold, found, ih, newDataObject]

theorem spreadFold_lookup (source : OrdinaryObject) (keys : List JSString) (target : OrdinaryObject) (query : JSString) :
    (spreadFold source keys target).own.lookup query =
      if query ∈ keys then (copiedDescriptor source query).or (target.own.lookup query) else target.own.lookup query := by
  induction keys generalizing target with
  | nil => simp [spreadFold]
  | cons key rest ih =>
    cases found : spreadValue source key with
    | none =>
      by_cases same : query = key
      · subst query
        simp [spreadFold, found, ih, copiedDescriptor]
      · simp [spreadFold, found, ih, same]
    | some value =>
      by_cases same : query = key
      · subst query
        simp [spreadFold, found, ih, newDataObject, putOwn_self, copiedDescriptor]
      · simp [spreadFold, found, ih, newDataObject, spread_putOwn_other key query _ _ same, same]

/-- Actual CopyDataProperties sequence: descriptor enum check, DATA Get,
CreateDataProperty, then next key. Target updates never dispatch [[Set]]. -/
def copyDataPropertiesInOrder : Nat → Nat → Nat → List JSString → State → Except EvalError State
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, [], state => .ok state
  | fuel + 1, target, source, key :: rest, state => do
    let object ← match state.objects[source]? with
      | none => .error .invalidReference
      | some object => .ok object
    match object.own.lookup key with
    | none | some (.data _ _ false _) | some (.accessor _ _ false _) =>
      copyDataPropertiesInOrder fuel target source rest state
    | some (.accessor _ _ true _) => .error .unsupported
    | some (.data _ _ true _) =>
      let value ← (getProperty propertyFuel state.objects source key).mapError .objectError
      let state ← defineLiteralProperty target key value state
      copyDataPropertiesInOrder fuel target source rest state

def copyDataProperties (fuel target source : Nat) (state : State) : Except EvalError State := do
  let object ← match state.objects[source]? with | none => .error .invalidReference | some object => .ok object
  copyDataPropertiesInOrder fuel target source (ownStringKeys object) state

theorem newDataObject_wellFormed (target : OrdinaryObject) (key : JSString) (value : Value)
    (wellFormed : WellFormedObject target) : WellFormedObject (newDataObject target key value) := by
  unfold WellFormedObject newDataObject putOwn
  simp only [List.map_cons]
  have filtered : (target.own.filter (fun entry => entry.1 != key)).map Prod.fst =
      (target.own.map Prod.fst).filter (fun other => other != key) := by
    symm
    exact List.filter_map
  rw [filtered]
  apply List.Pairwise.cons
  · intro other member
    have different := (List.mem_filter.mp member).2
    have unequal : other ≠ key := by simpa using different
    exact Ne.symm unequal
  · exact List.Pairwise.filter _ wellFormed

theorem spreadFold_wellFormed (source : OrdinaryObject) (keys : List JSString) (target : OrdinaryObject)
    (wellFormed : WellFormedObject target) : WellFormedObject (spreadFold source keys target) := by
  induction keys generalizing target with
  | nil => exact wellFormed
  | cons key rest ih =>
    cases found : spreadValue source key with
    | none => simpa [spreadFold, found] using ih target wellFormed
    | some value => simpa [spreadFold, found] using ih (newDataObject target key value) (newDataObject_wellFormed target key value wellFormed)

theorem defineSpreadData_ready (state : State) (reference : Nat) (target : OrdinaryObject) (key : JSString) (value : Value)
    (found : state.objects[reference]? = some target) (ready : SpreadTargetReady target) :
    defineLiteralProperty reference key value state =
      .ok {state with objects := state.objects.set reference (newDataObject target key value)} := by
  cases present : target.own.lookup key with
  | none => simp [defineLiteralProperty, found, present, ready.extensible, pure, Except.pure]
  | some descriptor =>
    obtain ⟨old, same⟩ := ready.ownData key descriptor present
    subst descriptor
    simp [defineLiteralProperty, found, present, pure, Except.pure]

theorem spreadData_get (state : State) (reference : Nat) (source : OrdinaryObject) (key : JSString) (value : Value)
    (writable configurable : Bool) (found : state.objects[reference]? = some source)
    (descriptor : source.own.lookup key = some (.data value writable true configurable)) :
    getProperty propertyFuel state.objects reference key = .ok value := by
  simp [getProperty, lookupProperty, propertyFuel, found, descriptor, bind, Except.bind, pure, Except.pure]

private theorem set_found_self (heap : ObjectHeap) (reference : Nat) (object : OrdinaryObject)
    (found : heap[reference]? = some object) : heap.set reference object = heap := by
  apply List.ext_getElem?
  intro other
  by_cases same : other = reference
  · subst other
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, found]
  · exact List.getElem?_set_ne (Ne.symm same)

/-- The actual descriptor/Get/CreateDataProperty loop equals the pure fold
under INITIAL source/target facts. Source and target are distinct cells; each
step proves its source read still sees the original descriptor/value. -/
theorem copyDataPropertiesInOrder_exec (extra target source : Nat) (keys : List JSString) (before : State)
    (sourceObject targetObject : OrdinaryObject)
    (sourceFound : before.objects[source]? = some sourceObject)
    (targetFound : before.objects[target]? = some targetObject)
    (separate : source ≠ target) (copyReady : CopyReady sourceObject) (targetReady : SpreadTargetReady targetObject) :
    copyDataPropertiesInOrder (extra + keys.length + 1) target source keys before =
      .ok {before with objects := before.objects.set target (spreadFold sourceObject keys targetObject)} := by
  induction keys generalizing before targetObject with
  | nil => simp [copyDataPropertiesInOrder, spreadFold, set_found_self before.objects target targetObject targetFound]
  | cons key rest ih =>
    cases descriptor : sourceObject.own.lookup key with
    | none =>
      simpa [copyDataPropertiesInOrder, sourceFound, descriptor, spreadFold, spreadValue, Nat.add_assoc, bind, Except.bind]
        using ih before targetObject sourceFound targetFound targetReady
    | some field =>
      cases field with
      | accessor getter setter enumerable configurable =>
        cases enumerable with
        | true => exact False.elim (copyReady key getter setter configurable descriptor)
        | false =>
          simpa [copyDataPropertiesInOrder, sourceFound, descriptor, spreadFold, spreadValue, Nat.add_assoc, bind, Except.bind]
            using ih before targetObject sourceFound targetFound targetReady
      | data value writable enumerable configurable =>
        cases enumerable with
        | false =>
          simpa [copyDataPropertiesInOrder, sourceFound, descriptor, spreadFold, spreadValue, Nat.add_assoc, bind, Except.bind]
            using ih before targetObject sourceFound targetFound targetReady
        | true =>
          let changed : State := {before with objects := before.objects.set target (newDataObject targetObject key value)}
          have sourceNext : changed.objects[source]? = some sourceObject :=
            (List.getElem?_set_ne (Ne.symm separate)).trans sourceFound
          have targetNext : changed.objects[target]? = some (newDataObject targetObject key value) :=
            List.getElem?_set_self (List.getElem?_eq_some_iff.mp targetFound).1
          have later := ih changed (newDataObject targetObject key value) sourceNext targetNext
            (newDataObject_spreadReady targetObject key value targetReady)
          have got := spreadData_get before source sourceObject key value writable configurable sourceFound descriptor
          have made := defineSpreadData_ready before target targetObject key value targetFound targetReady
          simpa [copyDataPropertiesInOrder, sourceFound, descriptor, got, made, spreadFold, spreadValue,
            Nat.add_assoc, changed, List.set_set, bind, Except.bind, Except.mapError]
            using later

/-- Extensional all-and-only own data descriptors from every complete own-key
order. This intentionally does not equate raw property-list order. -/
theorem spreadFold_all_keys (source : OrdinaryObject) (keys : List JSString) (order : OwnStringKeyOrder source keys)
    (query : JSString) :
    (spreadFold source keys emptyLiteralObject).own.lookup query = copiedDescriptor source query := by
  rw [spreadFold_lookup]
  by_cases member : query ∈ keys
  · simp [member, emptyLiteralObject]
  · have absent : source.own.lookup query = none := by
      cases found : source.own.lookup query with
      | none => rfl
      | some descriptor => exact False.elim (member ((order.complete query).mpr ⟨descriptor, found⟩))
    simp [member, emptyLiteralObject, copiedDescriptor, spreadValue, absent]

structure FreshObjectSpreadContract (before after : State) (source : Nat) (sourceObject : OrdinaryObject) (returned : Value) : Prop where
  sourceBefore : before.objects[source]? = some sourceObject
  returnedReference : returned = .object before.objects.length
  objectsLength : after.objects.length = before.objects.length + 1
  oldObjects : ∀ reference, reference < before.objects.length → after.objects[reference]? = before.objects[reference]?
  sourceFrame : after.objects[source]? = some sourceObject
  environment : after.environment = before.environment
  heap : after.heap = before.heap
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue
  target : ∃ object, after.objects[before.objects.length]? = some object ∧
    object.prototype = some ordinaryObjectPrototype ∧ WellFormedObject object ∧ SpreadTargetReady object ∧
    ∀ key, object.own.lookup key = copiedDescriptor sourceObject key

def spreadFreshState (before : State) (sourceObject : OrdinaryObject) (keys : List JSString) : State :=
  {before with objects := before.objects ++ [spreadFold sourceObject keys emptyLiteralObject]}

theorem spreadFreshState_satisfies (before : State) (source : Nat) (sourceObject : OrdinaryObject)
    (keys : List JSString) (sourceFound : before.objects[source]? = some sourceObject)
    (order : OwnStringKeyOrder sourceObject keys) :
    FreshObjectSpreadContract before (spreadFreshState before sourceObject keys) source sourceObject (.object before.objects.length) := by
  have oldBound := (List.getElem?_eq_some_iff.mp sourceFound).1
  refine ⟨sourceFound, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [spreadFreshState]
  · intro reference inside
    exact List.getElem?_append_left inside
  · exact (List.getElem?_append_left oldBound).trans sourceFound
  · refine ⟨spreadFold sourceObject keys emptyLiteralObject, ?_, spreadFold_prototype sourceObject keys emptyLiteralObject,
      spreadFold_wellFormed sourceObject keys emptyLiteralObject (by simp [WellFormedObject, emptyLiteralObject]),
      spreadFold_ready sourceObject keys emptyLiteralObject emptyLiteral_spreadReady, spreadFold_all_keys sourceObject keys order⟩
    simp [spreadFreshState]

/-- Every legal order executes from initial frozen DATA facts and has the same
extensional copied descriptors/freshness/old frames. Raw list order may differ. -/
theorem copyDataPropertiesInOrder_fresh (extra : Nat) (before : State) (source : Nat) (sourceObject : OrdinaryObject)
    (keys : List JSString) (sourceFound : before.objects[source]? = some sourceObject)
    (copyReady : CopyReady sourceObject) (order : OwnStringKeyOrder sourceObject keys) :
    let allocated : State := {before with objects := before.objects ++ [emptyLiteralObject]}
    copyDataPropertiesInOrder (extra + keys.length + 1) before.objects.length source keys allocated =
      .ok (spreadFreshState before sourceObject keys) ∧
      FreshObjectSpreadContract before (spreadFreshState before sourceObject keys) source sourceObject (.object before.objects.length) := by
  have sourceBound := (List.getElem?_eq_some_iff.mp sourceFound).1
  constructor
  · have sourceAfter : (before.objects ++ [emptyLiteralObject])[source]? = some sourceObject :=
      (List.getElem?_append_left sourceBound).trans sourceFound
    have targetAfter : (before.objects ++ [emptyLiteralObject])[before.objects.length]? = some emptyLiteralObject := by simp
    have actual := copyDataPropertiesInOrder_exec extra before.objects.length source keys
      {before with objects := before.objects ++ [emptyLiteralObject]} sourceObject emptyLiteralObject
      sourceAfter targetAfter (by omega) copyReady emptyLiteral_spreadReady
    simpa [spreadFreshState, List.set_append_right] using actual
  · exact spreadFreshState_satisfies before source sourceObject keys sourceFound order

theorem spreadFold_orders_extensional (source : OrdinaryObject) (first second : List JSString)
    (one : OwnStringKeyOrder source first) (two : OwnStringKeyOrder source second) (key : JSString) :
    (spreadFold source first emptyLiteralObject).own.lookup key =
      (spreadFold source second emptyLiteralObject).own.lookup key :=
  (spreadFold_all_keys source first one key).trans (spreadFold_all_keys source second two key).symm

end HonoLean.Upstream.ECMA2025
