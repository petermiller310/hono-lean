import HonoLean.Upstream.NodeChildEnumeration.Source

namespace HonoLean.Upstream.NodeChildEnumeration

open SourceSubset ECMA2025

/-- Initial source read and actual descriptor-bearing children object. This
source-normal domain is null-prototype with unique own string keys; inherited
enumeration, symbols, proxies and exotic mutations are outside this theorem. -/
structure ChildrenInputs (before : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject) : Prop where
  binding : before.regexp.arrays.environment.lookup "child" = some (.object owner)
  allocated : ∃ ownerObject, before.ambient.objects[owner]? = some ownerObject
  lexical : before.ambient.privates.names.lookup "children" = some childrenIdentity
  data : ∃ fields, before.ambient.privates.elements.lookup owner = some fields ∧
    fields.lookup childrenIdentity = some (.data (.object children))
  found : before.ambient.objects[children]? = some object
  nullPrototype : object.prototype = none
  wellFormed : WellFormedObject object

/-- Needed only when an actual enumerable descriptor exists. All facts concern
the BEFORE-loop state; there is no supplied count, enumeration result, regex
match, later target layout, or completed body premise. -/
structure BodyInputs (before : ForInState) (owner childrenIdentity paramsIdentity : Nat) (old params : Value)
    (m queue : Nat) (matched queued : IndexedArray) (input : JSString) : Prop where
  writable : NodePrivateWrite.Writable (forInStateView before) owner paramsIdentity old
  paramsBinding : before.regexp.arrays.environment.lookup "params" = some params
  distinct : childrenIdentity ≠ paramsIdentity
  count : NodeComponentCount.Inputs before.regexp m matched input
  queue : NodeComponentCount.ScheduleInputs before.regexp queue queued (.object owner) input
  admitted : NodeComponentCount.AdmittedTarget before.regexp queued input

def NoEnumerable (object : OrdinaryObject) : Prop :=
  ∀ key descriptor, object.own.lookup key = some descriptor → descriptorEnumerable descriptor = false

structure EmptyContract (before after : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject) : Prop where
  initial : ChildrenInputs before owner childrenIdentity children object
  descriptors : NoEnumerable object
  unchanged : after = before

/-- One genuine body, then consumed break and lexical scope exit. The internal
count/schedule relation is stage-specific: final m/queue aliases can change a
source array, while the saved count and ordinary children object stay correct. -/
structure EnteredContract (before after : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (queue : Nat) (queued : IndexedArray) (input : JSString) : Prop where
  initial : ChildrenInputs before owner childrenIdentity children object
  paramsWritable : NodePrivateWrite.Writable (forInStateView before) owner paramsIdentity old
  paramsBinding : before.regexp.arrays.environment.lookup "params" = some params
  distinct : childrenIdentity ≠ paramsIdentity
  phases : ∃ key active written completed,
    EnumerableName object key ∧ active = bindForInKey "_" key before ∧
    NodePrivateWrite.WriteContract (forInStateView active) (forInStateView written) owner paramsIdentity old params params ∧
    written.regexp = active.regexp ∧
    NodeComponentCount.ScheduleContract written.regexp completed.regexp queue queued (.object owner) input ∧
    completed.ambient = written.ambient ∧ after = restoreForInEnvironment before.regexp.arrays.environment completed
  privateChange : NodePrivateWrite.PrivateReplacement owner paramsIdentity old params
    before.ambient.privates.elements after.ambient.privates.elements
  childrenRead : privateGet (.object owner) "children" (forInStateView after) = .ok (.object children)
  environment : after.regexp.arrays.environment = before.regexp.arrays.environment
  objects : after.ambient.objects = before.ambient.objects
  functions : after.ambient.functions = before.ambient.functions
  sets : after.ambient.sets = before.ambient.sets
  thisValue : after.ambient.thisValue = before.ambient.thisValue
  names : after.ambient.privates.names = before.ambient.privates.names
  ambientEnvironment : after.ambient.environment = before.ambient.environment
  ambientHeap : after.ambient.heap = before.ambient.heap

inductive Contract (before after : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject) : Prop
  | empty (contract : EmptyContract before after owner childrenIdentity children object) : Contract before after owner childrenIdentity children object
  | entered (paramsIdentity : Nat) (old params : Value) (queue : Nat) (queued : IndexedArray) (input : JSString)
      (contract : EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input) :
      Contract before after owner childrenIdentity children object

end HonoLean.Upstream.NodeChildEnumeration
