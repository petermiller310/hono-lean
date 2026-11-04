import HonoLean.Upstream.SourceSubset.Values

namespace HonoLean.Upstream.ECMA2025

open SourceSubset (JSString Value)

/-!
Local ordinary-object mechanism motivated by pinned TrieRouter D1. The model
separates own descriptors, prototype traversal, getter/setter invocation and
receiver data-property creation. Relevant ECMA-262 2025 operations:
https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinarysetwithowndescriptor
https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-object.prototype.__proto__

The legacy accessor is normative optional: its standard presence is a realm
premise. This is neither full ECMAScript semantics nor a whole-TrieRouter proof.
Keys are already primitive UTF-16 strings; addresses are abstract heap identities.
Generic user functions, proxies, symbols, primitive receivers, prototype changes,
property enumeration and definition/deletion are unsupported. List order is a
lookup-store detail, not a model of [[OwnPropertyKeys]]. Errors model rejection, not a
complete JavaScript exception taxonomy. Fuel bounds prototype traversal; cycles
can exhaust. Descriptors retain writable/enumerable/configurable flags; writes
preserve existing flags, require writable data, and require extensibility for
new own data. Configurability does not gate ordinary writable-data assignment.
-/

abbrev ObjectRef := Nat

inductive Getter where
  | missing | prototype | unsupported
  deriving Repr, DecidableEq

inductive Setter where
  | missing | prototype | unsupported
  deriving Repr, DecidableEq

inductive PropertyDescriptor where
  | data (value : Value) (writable enumerable configurable : Bool)
  | accessor (getter : Getter) (setter : Setter) (enumerable configurable : Bool)
  deriving Repr, DecidableEq

structure OrdinaryObject where
  own : List (JSString × PropertyDescriptor) := []
  prototype : Option ObjectRef := none
  extensible : Bool := true
  deriving Repr, DecidableEq

abbrev ObjectHeap := List OrdinaryObject

/-- Intended objects have unique own keys and valid prototype references. The
local theorems use explicit concrete/lookup premises; no claim that an arbitrary
list with duplicate keys is a legal ECMAScript object is made. -/
def WellFormedObject (object : OrdinaryObject) : Prop := (object.own.map Prod.fst).Nodup

def WellFormedHeap (heap : ObjectHeap) : Prop :=
  ∀ object ∈ heap, WellFormedObject object ∧
    ∀ reference, object.prototype = some reference → reference < heap.length

inductive ObjectError where
  | exhausted | invalidReference | notWritable | notExtensible | unsupported
  deriving Repr, DecidableEq

def emptyNullObject : OrdinaryObject := ⟨[], none, true⟩

def createNull (heap : ObjectHeap) : ObjectRef × ObjectHeap :=
  (heap.length, heap ++ [emptyNullObject])

def createOrdinary (heap : ObjectHeap) (prototype : ObjectRef) : ObjectRef × ObjectHeap :=
  (heap.length, heap ++ [⟨[], some prototype, true⟩])

def hasOwn (heap : ObjectHeap) (receiver : ObjectRef) (key : JSString) :
    Except ObjectError Bool :=
  match heap[receiver]? with
  | none => .error .invalidReference
  | some object => .ok (object.own.lookup key).isSome

/-- Resolve a descriptor, preserving the original receiver for later accessor
invocation. An own property always shadows the prototype chain. -/
def lookupProperty : Nat → ObjectHeap → ObjectRef → JSString →
    Except ObjectError (Option PropertyDescriptor)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, heap, holder, key =>
    match heap[holder]? with
    | none => .error .invalidReference
    | some object =>
      match object.own.lookup key with
      | some descriptor => .ok (some descriptor)
      | none =>
        match object.prototype with
        | none => .ok none
        | some parent => lookupProperty fuel heap parent key

def callGetter (getter : Getter) (heap : ObjectHeap) (receiver : ObjectRef) :
    Except ObjectError Value :=
  match getter with
  | .missing => .ok .undefined
  | .unsupported => .error .unsupported
  | .prototype =>
    match heap[receiver]? with
    | none => .error .invalidReference
    | some object => .ok (object.prototype.map Value.object |>.getD .null)

def getProperty (fuel : Nat) (heap : ObjectHeap) (receiver : ObjectRef) (key : JSString) :
    Except ObjectError Value := do
  match ← lookupProperty fuel heap receiver key with
  | none => return .undefined
  | some (.data value _ _ _) => return value
  | some (.accessor getter _ _ _) => callGetter getter heap receiver

/-- A recognized primitive RHS makes the standard legacy prototype setter
return before calling [[SetPrototypeOf]]. Object/null RHS mutation is explicitly
unsupported, including function/array tags that also denote native objects. -/
def callSetter (setter : Setter) (heap : ObjectHeap) (receiver : ObjectRef) (value : Value) :
    Except ObjectError ObjectHeap :=
  match setter with
  | .missing => .error .notWritable
  | .unsupported => .error .unsupported
  | .prototype =>
    match heap[receiver]? with
    | none => .error .invalidReference
    | some _ =>
      match value with
      | .string _ | .number _ | .boolean _ | .undefined => .ok heap
      | .null | .object _ | .array _ | .objectConstructor | .function _ | .set _ | .setConstructor => .error .unsupported

def putOwn (key : JSString) (descriptor : PropertyDescriptor)
    (properties : List (JSString × PropertyDescriptor)) : List (JSString × PropertyDescriptor) :=
  (key, descriptor) :: properties.filter (fun entry => entry.1 != key)

def newDataObject (object : OrdinaryObject) (key : JSString) (value : Value) : OrdinaryObject :=
  {object with own := putOwn key (.data value true true true) object.own}

/-- Receiver-side data update after ordinary Set descriptor dispatch. Existing
data attributes are preserved; absent data requires an extensible receiver. -/
def writeOwnData (heap : ObjectHeap) (receiver : ObjectRef) (key : JSString) (value : Value) :
    Except ObjectError ObjectHeap :=
  match heap[receiver]? with
  | none => .error .invalidReference
  | some object =>
    match object.own.lookup key with
    | some (.accessor _ _ _ _) => .error .notWritable
    | some (.data _ writable enumerable configurable) =>
      if writable then
        .ok (heap.set receiver {object with
          own := putOwn key (.data value writable enumerable configurable) object.own})
      else .error .notWritable
    | none =>
      if object.extensible then .ok (heap.set receiver (newDataObject object key value))
      else .error .notExtensible

def setProperty (fuel : Nat) (heap : ObjectHeap) (receiver : ObjectRef) (key : JSString)
    (value : Value) : Except ObjectError ObjectHeap := do
  match ← lookupProperty fuel heap receiver key with
  | none => writeOwnData heap receiver key value
  | some (.data _ writable _ _) =>
    if writable then writeOwnData heap receiver key value else .error .notWritable
  | some (.accessor _ setter _ _) => callSetter setter heap receiver value

theorem putOwn_self (key : JSString) (descriptor : PropertyDescriptor)
    (properties : List (JSString × PropertyDescriptor)) :
    (putOwn key descriptor properties).lookup key = some descriptor := by
  simp [putOwn]

theorem createNull_fresh (heap : ObjectHeap) :
    (createNull heap).1 = heap.length ∧
    (createNull heap).2.length = heap.length + 1 ∧
    (createNull heap).2[heap.length]? = some emptyNullObject := by
  simp [createNull]

theorem createNull_noOwn (heap : ObjectHeap) (key : JSString) :
    hasOwn (createNull heap).2 (createNull heap).1 key = .ok false := by
  simp [hasOwn, createNull, emptyNullObject]

theorem createNull_nullPrototype (heap : ObjectHeap) :
    ((createNull heap).2[heap.length]?).map OrdinaryObject.prototype = some none := by
  simp [createNull, emptyNullObject]

theorem createNull_preserves_other_cells (heap : ObjectHeap) (reference : Nat)
    (existing : reference < heap.length) :
    (createNull heap).2[reference]? = heap[reference]? :=
  List.getElem?_append_left existing

theorem createNull_wellFormed (heap : ObjectHeap) (well : WellFormedHeap heap) :
    WellFormedHeap (createNull heap).2 := by
  intro object member
  simp only [createNull, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with old | fresh
  · have original := well object old
    refine ⟨original.1, ?_⟩
    intro reference prototype
    have bound := original.2 reference prototype
    simp only [createNull, List.length_append, List.length_cons, List.length_nil]
    exact Nat.lt_succ_of_lt bound
  · subst object
    constructor
    · simp [WellFormedObject, emptyNullObject]
    · intro reference impossible
      simp [emptyNullObject] at impossible

theorem getProperty_data (heap : ObjectHeap) (reference fuel : Nat) (key : JSString)
    (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool)
    (found : heap[reference]? = some object)
    (own : object.own.lookup key = some (.data value writable enumerable configurable)) :
    getProperty (fuel + 1) heap reference key = .ok value := by
  simp [getProperty, lookupProperty, found, own, bind, pure, Except.bind, Except.pure]

theorem setProperty_null (heap : ObjectHeap) (reference fuel : Nat) (key : JSString)
    (value : Value) (found : heap[reference]? = some emptyNullObject) :
    setProperty (fuel + 1) heap reference key value =
      .ok (heap.set reference (newDataObject emptyNullObject key value)) := by
  simp [setProperty, lookupProperty, found, emptyNullObject, writeOwnData,
    bind, Except.bind]

theorem null_set_get (heap : ObjectHeap) (reference fuel : Nat) (key : JSString)
    (value : Value) (found : heap[reference]? = some emptyNullObject) :
    getProperty (fuel + 1) (heap.set reference (newDataObject emptyNullObject key value))
        reference key = .ok value ∧
    hasOwn (heap.set reference (newDataObject emptyNullObject key value)) reference key = .ok true := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have updated := List.getElem?_set_self (l := heap) (a := newDataObject emptyNullObject key value) bound
  constructor
  · exact getProperty_data _ _ _ _ _ _ true true true updated (putOwn_self _ _ _)
  · simp only [hasOwn, updated]
    simp [newDataObject, putOwn_self]

theorem newData_get_hasOwn (heap : ObjectHeap) (reference fuel : Nat) (key : JSString)
    (object : OrdinaryObject) (value : Value) (found : heap[reference]? = some object) :
    getProperty (fuel + 1) (heap.set reference (newDataObject object key value)) reference key = .ok value ∧
    hasOwn (heap.set reference (newDataObject object key value)) reference key = .ok true := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have updated := List.getElem?_set_self (l := heap) (a := newDataObject object key value) bound
  constructor
  · exact getProperty_data _ _ _ _ _ _ true true true updated (putOwn_self _ _ _)
  · simp only [hasOwn, updated]
    simp [newDataObject, putOwn_self]

theorem writable_data_preserves_attributes (heap : ObjectHeap) (reference fuel : Nat)
    (key : JSString) (object : OrdinaryObject) (old value : Value)
    (enumerable configurable : Bool) (found : heap[reference]? = some object)
    (own : object.own.lookup key = some (.data old true enumerable configurable)) :
    setProperty (fuel + 1) heap reference key value =
      .ok (heap.set reference {object with
        own := putOwn key (.data value true enumerable configurable) object.own}) := by
  simp [setProperty, lookupProperty, found, own, writeOwnData, bind, Except.bind]

theorem nonwritable_data_rejected (heap : ObjectHeap) (reference fuel : Nat)
    (key : JSString) (object : OrdinaryObject) (old value : Value)
    (enumerable configurable : Bool) (found : heap[reference]? = some object)
    (own : object.own.lookup key = some (.data old false enumerable configurable)) :
    setProperty (fuel + 1) heap reference key value = .error .notWritable := by
  simp [setProperty, lookupProperty, found, own, bind, Except.bind]

theorem prototype_setter_ignores_string (heap : ObjectHeap) (reference : Nat)
    (object : OrdinaryObject) (contents : JSString)
    (found : heap[reference]? = some object) :
    callSetter .prototype heap reference (.string contents) = .ok heap := by
  simp [callSetter, found]

theorem data_write_preserves_other_cells (heap : ObjectHeap) (reference other : Nat)
    (object : OrdinaryObject) (different : other ≠ reference) :
    (heap.set reference object)[other]? = heap[other]? :=
  List.getElem?_set_ne (Ne.symm different)

def protoKey : JSString := [95, 95, 112, 114, 111, 116, 111, 95, 95]
def constructorKey : JSString := [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114]
def idKey : JSString := [105, 100]

/-- A projection of the standard realm's relevant descriptors, with remaining
properties supplied as a frame. Real Object.prototype has other non-enumerable
properties and is not the empty object suggested by JSON serialization. Its
special immutable [[SetPrototypeOf]] is outside the supported mutation domain. -/
def objectPrototypeProjection (frame : List (JSString × PropertyDescriptor) := []) : OrdinaryObject :=
  ⟨[(protoKey, .accessor .prototype .prototype false true),
    (constructorKey, .data .objectConstructor true false true)] ++ frame, none, true⟩

def d1Realm (frame : List (JSString × PropertyDescriptor) := []) : ObjectHeap :=
  [objectPrototypeProjection frame, ⟨[], some 0, true⟩]

/-- Lookup dispatches the inherited setter; a string RHS leaves the entire
heap unchanged. The inherited getter later reads the receiver's prototype. -/
theorem proto_string_ignored (contents : JSString)
    (frame : List (JSString × PropertyDescriptor)) (fuel : Nat) :
    setProperty (fuel + 2) (d1Realm frame) 1 protoKey (.string contents) = .ok (d1Realm frame) ∧
    hasOwn (d1Realm frame) 1 protoKey = .ok false ∧
    getProperty (fuel + 2) (d1Realm frame) 1 protoKey = .ok (.object 0) := by
  constructor
  · rfl
  · constructor <;> rfl

theorem constructor_string_own_data (contents : JSString) (fuel : Nat) :
    setProperty (fuel + 2) (d1Realm []) 1 constructorKey (.string contents) =
      .ok ((d1Realm []).set 1 (newDataObject ⟨[], some 0, true⟩ constructorKey (.string contents))) := by
  rfl

theorem id_string_own_data (contents : JSString) (fuel : Nat) :
    setProperty (fuel + 2) (d1Realm []) 1 idKey (.string contents) =
      .ok ((d1Realm []).set 1 (newDataObject ⟨[], some 0, true⟩ idKey (.string contents))) := by
  rfl

end HonoLean.Upstream.ECMA2025
