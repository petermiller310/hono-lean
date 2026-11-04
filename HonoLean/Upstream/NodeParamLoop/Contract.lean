import HonoLean.Upstream.NodeParamAssignment.Correctness

namespace HonoLean.Upstream.NodeParamLoop

open SourceSubset ECMA2025

def possibleKeysKey : JSString := [112, 111, 115, 115, 105, 98, 108, 101, 75, 101, 121, 115]
def lengthKey : JSString := [108, 101, 110, 103, 116, 104]

/-- Values observed after the allocation/reset and handler-array append, before
iteration. These are not values computed by executing the loop. The source
proof must relate them to admissible property reads in that entry state. -/
structure Snapshot where
  keys : List JSString
  parameter : JSString → Value
  node : JSString → Value

/-- Independent iteration-order association list. No evaluator/Set invocation
appears here; each step uses the already independent value-selection relation
at the actual zero-based key index. Duplicate keys are not silently removed. -/
inductive Captures (snapshot : Snapshot) : Nat → List (JSString × Value) → Prop where
  | empty : Captures snapshot 0 []
  | step {count : Nat} {entries : List (JSString × Value)} {key : JSString} {value : Value}
      (prior : Captures snapshot count entries)
      (atKey : snapshot.keys[count]? = some key)
      (selected : NodeParamAssignment.Selected (snapshot.parameter key) (snapshot.node key) (count : Int) value) :
      Captures snapshot (count + 1) (entries ++ [(key, value)])

/-- Own-store order is a representation detail. Native [[OwnPropertyKeys]] and
JSON serialization are outside this observation; each captured descriptor is
ordinary writable/enumerable/configurable data on a null-prototype object. -/
def capturedObject (entries : List (JSString × Value)) : OrdinaryObject :=
  ⟨entries.reverse.map (fun (key, value) => (key, .data value true true true)), none, true⟩

def Prefix (snapshot : Snapshot) (count : Nat) (object : OrdinaryObject) : Prop :=
  ∃ entries, Captures snapshot count entries ∧ object = capturedObject entries

theorem captures_length {snapshot : Snapshot} {count : Nat} {entries : List (JSString × Value)}
    (captures : Captures snapshot count entries) : entries.length = count := by
  induction captures with
  | empty => rfl
  | step _ _ _ ih => simpa using ih

theorem captures_keys {snapshot : Snapshot} {count : Nat} {entries : List (JSString × Value)}
    (captures : Captures snapshot count entries) : entries.map Prod.fst = snapshot.keys.take count := by
  induction captures with
  | empty => rfl
  | @step count entries key value prior atKey selected ih =>
    obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp atKey
    simp only [List.map_append, List.map_cons, List.map_nil, ih]
    rw [List.take_succ_eq_append_getElem bound, equal]

theorem captures_bound {snapshot : Snapshot} {count : Nat} {entries : List (JSString × Value)}
    (captures : Captures snapshot count entries) : count ≤ snapshot.keys.length := by
  have lengths := congrArg List.length (captures_keys captures)
  simp only [List.length_map, captures_length captures, List.length_take] at lengths
  omega

theorem current_key_not_processed (keys : List JSString) (unique : keys.Nodup)
    (count : Nat) (key : JSString) (atKey : keys[count]? = some key) : key ∉ keys.take count := by
  intro member
  obtain ⟨earlier, earlierBound, equal⟩ := List.mem_take_iff_getElem.mp member
  obtain ⟨bound, current⟩ := List.getElem?_eq_some_iff.mp atKey
  have sameIndex := unique.eq_of_getElem_eq (by omega : earlier < keys.length) bound (equal.trans current.symm)
  omega

theorem prefix_empty (snapshot : Snapshot) : Prefix snapshot 0 emptyNullObject :=
  ⟨[], .empty, rfl⟩

theorem prefix_null_extensible {snapshot : Snapshot} {count : Nat} {object : OrdinaryObject}
    (invariant : Prefix snapshot count object) : object.prototype = none ∧ object.extensible = true := by
  obtain ⟨entries, _, rfl⟩ := invariant
  exact ⟨rfl, rfl⟩

theorem prefix_next_absent {snapshot : Snapshot} {count : Nat} {object : OrdinaryObject}
    (invariant : Prefix snapshot count object) (unique : snapshot.keys.Nodup)
    (key : JSString) (atKey : snapshot.keys[count]? = some key) : object.own.lookup key = none := by
  obtain ⟨entries, captures, rfl⟩ := invariant
  have absent := current_key_not_processed snapshot.keys unique count key atKey
  apply List.lookup_eq_none_iff.mpr
  intro entry member
  simp only [capturedObject, List.mem_map] at member
  obtain ⟨pair, pairMember, pairEqual⟩ := member
  have keyMember : pair.1 ∈ snapshot.keys.take count := by
    rw [← captures_keys captures]
    exact List.mem_map.mpr ⟨pair, List.mem_reverse.mp pairMember, rfl⟩
  have different : key ≠ pair.1 := by intro equal; exact absent (equal ▸ keyMember)
  cases pair
  cases pairEqual
  simpa using different

theorem prefix_step {snapshot : Snapshot} {count : Nat} {object : OrdinaryObject}
    (invariant : Prefix snapshot count object) (unique : snapshot.keys.Nodup)
    (key : JSString) (value : Value) (atKey : snapshot.keys[count]? = some key)
    (selected : NodeParamAssignment.Selected (snapshot.parameter key) (snapshot.node key) (count : Int) value) :
    Prefix snapshot (count + 1) (newDataObject object key value) := by
  have absent := prefix_next_absent invariant unique key atKey
  obtain ⟨entries, captures, rfl⟩ := invariant
  refine ⟨entries ++ [(key, value)], .step captures atKey selected, ?_⟩
  have own := NodeParamAssignment.absent_key_preserves_prior_properties (capturedObject entries) key value absent
  have lifted := congrArg (fun properties => OrdinaryObject.mk properties none true) own
  simpa [capturedObject, newDataObject] using lifted

/-- Closed existing prototype references support a structural read-frame proof.
This is not a claim of acyclicity or a complete native-heap wellformedness test.
Lookup still has its declared fuel and can reject unsupported descriptors. -/
def PrototypeClosed (heap : ObjectHeap) (bound : Nat) : Prop :=
  ∀ reference, reference < bound → ∀ object, heap[reference]? = some object →
    ∀ parent, object.prototype = some parent → parent < bound

theorem lookupProperty_frame (fuel : Nat) (before after : ObjectHeap) (bound : Nat)
    (frame : ∀ reference, reference < bound → before[reference]? = after[reference]?)
    (closed : PrototypeClosed before bound) (reference : ObjectRef) (inside : reference < bound)
    (key : JSString) :
    lookupProperty fuel before reference key = lookupProperty fuel after reference key := by
  induction fuel generalizing reference with
  | zero => rfl
  | succ fuel ih =>
    have equal := frame reference inside
    cases found : before[reference]? with
    | none => simp [lookupProperty, ← equal, found]
    | some object =>
      cases own : object.own.lookup key with
      | some descriptor => simp [lookupProperty, ← equal, found, own]
      | none =>
        cases parent : object.prototype with
        | none => simp [lookupProperty, ← equal, found, own, parent]
        | some next =>
          simp only [lookupProperty, ← equal, found, own, parent]
          exact ih next (closed reference inside object found next parent)

theorem callGetter_frame (getter : Getter) (before after : ObjectHeap) (reference : ObjectRef)
    (same : before[reference]? = after[reference]?) :
    callGetter getter before reference = callGetter getter after reference := by
  cases getter <;> simp [callGetter, ← same]

theorem getProperty_frame (fuel : Nat) (before after : ObjectHeap) (bound : Nat)
    (frame : ∀ reference, reference < bound → before[reference]? = after[reference]?)
    (closed : PrototypeClosed before bound) (reference : ObjectRef) (inside : reference < bound)
    (key : JSString) :
    getProperty fuel before reference key = getProperty fuel after reference key := by
  unfold getProperty
  rw [← lookupProperty_frame fuel before after bound frame closed reference inside key]
  cases lookupProperty fuel before reference key with
  | error error => rfl
  | ok descriptor =>
    cases descriptor with
    | none => rfl
    | some descriptor =>
      cases descriptor with
      | data => rfl
      | accessor getter setter enumerable configurable =>
        exact callGetter_frame getter before after reference (frame reference inside)

def resetState (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject) : State :=
  {before with objects :=
    (before.objects.set handlerSet (newDataObject handler NodeParamAssignment.paramsKey
      (.object before.objects.length))) ++ [emptyNullObject]}

def setupState (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) : State :=
  {resetState before handlerSet handler with heap := before.heap.set handlerSets (priorHandlers ++ [.object handlerSet])}

theorem putOwn_other (key other : JSString) (descriptor : PropertyDescriptor)
    (properties : List (JSString × PropertyDescriptor)) (different : other ≠ key) :
    (putOwn key descriptor properties).lookup other = properties.lookup other := by
  have differentBool := beq_false_of_ne different
  induction properties with
  | nil => simp [putOwn, List.lookup_cons, differentBool]
  | cons pair rest ih =>
    rcases pair with ⟨name, old⟩
    by_cases same : name = key
    · subst name
      simpa [putOwn, List.lookup_cons, differentBool] using ih
    · have filtered : (rest.filter (fun entry => entry.1 != key)).lookup other = rest.lookup other := by
        simpa [putOwn, List.lookup_cons, differentBool] using ih
      simp [putOwn, List.lookup_cons, same, filtered, differentBool]

theorem setup_length (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) :
    (setupState before handlerSet handler handlerSets priorHandlers).objects.length = before.objects.length + 1 := by
  simp [setupState, resetState]

theorem setup_handler (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (found : before.objects[handlerSet]? = some handler) :
    (setupState before handlerSet handler handlerSets priorHandlers).objects[handlerSet]? =
      some (newDataObject handler NodeParamAssignment.paramsKey (.object before.objects.length)) := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
  simp only [setupState, resetState]
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_set_self inside]

theorem setup_old_cell (before : State) (handlerSet reference : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (inside : reference < before.objects.length)
    (different : reference ≠ handlerSet) :
    (setupState before handlerSet handler handlerSets priorHandlers).objects[reference]? = before.objects[reference]? := by
  simp only [setupState, resetState]
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_set_ne (Ne.symm different)]

theorem setup_fresh_cell (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) :
    (setupState before handlerSet handler handlerSets priorHandlers).objects[before.objects.length]? = some emptyNullObject := by
  simp [setupState, resetState]

theorem setup_heap_other (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets reference : Nat) (priorHandlers : List Value) (different : handlerSets ≠ reference) :
    (setupState before handlerSet handler handlerSets priorHandlers).heap[reference]? = before.heap[reference]? :=
  List.getElem?_set_ne different

theorem setup_prototype_closed (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (found : before.objects[handlerSet]? = some handler)
    (closed : PrototypeClosed before.objects before.objects.length) :
    PrototypeClosed (setupState before handlerSet handler handlerSets priorHandlers).objects before.objects.length := by
  intro reference inside object current parent prototype
  by_cases same : reference = handlerSet
  · subst reference
    have equal := (setup_handler before handlerSet handler handlerSets priorHandlers found).symm.trans current
    cases Option.some.inj equal
    exact closed handlerSet inside handler found parent prototype
  · rw [setup_old_cell before handlerSet reference handler handlerSets priorHandlers inside same] at current
    exact closed reference inside object current parent prototype

/-- Independent normal-completion endpoint for actual lines75–81. The fresh
identity is relative to previously allocated object cells. Existing handler
array entries are the same Value references; an entry aliasing handlerSet can
observe its reset params. Snapshots refer to setupState, after reset and push.
The source proof must establish all setup operations and the prefix invariant.
Set-producer linkage is separate: the loop domain requires unique string keys. -/
def BlockContract (before after : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (snapshot : Snapshot) : Prop :=
  ∃ output, Prefix snapshot snapshot.keys.length output ∧
    after = {setupState before handlerSet handler handlerSets priorHandlers with
      objects := (setupState before handlerSet handler handlerSets priorHandlers).objects.set before.objects.length output}

end HonoLean.Upstream.NodeParamLoop
