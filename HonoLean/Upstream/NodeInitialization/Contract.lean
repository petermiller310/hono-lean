import HonoLean.Upstream.NodeInitialization.Program

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

def nodeNames (firstIdentity : Nat) : List (String × Nat) :=
  [("methods", firstIdentity), ("children", firstIdentity + 1),
   ("patterns", firstIdentity + 2), ("pattern", firstIdentity + 3), ("params", firstIdentity + 4)]

/-- Private storage observations are ordinary lookup facts over opaque lexical
identities, not public object-property descriptors or native reflection. -/
def FieldsStored (fields : List (Nat × Value)) (firstIdentity methods patterns children : Nat)
    (emptyParams : Value) : Prop :=
  fields.lookup firstIdentity = some (.array methods) ∧
  fields.lookup (firstIdentity + 1) = some (.object children) ∧
  fields.lookup (firstIdentity + 2) = some (.array patterns) ∧
  fields.lookup (firstIdentity + 3) = some .undefined ∧
  fields.lookup (firstIdentity + 4) = some emptyParams

/-- Independent endpoint for the five selected data fields on a freshly
allocated ordinary owner. The caller's environment/private lexical context is
restored, but fresh per-instance slots and allocation effects are retained.
The shared emptyParams value is a separate module-produced reference. -/
structure InstanceContract (before after : State) (prototype : Option Nat)
    (firstIdentity owner : Nat) (emptyParams : Value) : Prop where
  ownerAddress : owner = before.objects.length
  objects : after.objects = before.objects ++ [⟨[], prototype, true⟩, emptyNullObject]
  arrays : after.heap = before.heap ++ [[], []]
  environment : after.environment = before.environment
  names : after.privates.names = before.privates.names
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  fields : ∃ stored,
    after.privates.slots = (owner, stored) :: before.privates.slots ∧
    FieldsStored stored firstIdentity before.heap.length (before.heap.length + 1)
      (before.objects.length + 1) emptyParams

theorem instance_methods (before after : State) (prototype : Option Nat)
    (firstIdentity owner : Nat) (emptyParams : Value)
    (contract : InstanceContract before after prototype firstIdentity owner emptyParams) :
    ∃ stored, after.privates.slots.lookup owner = some stored ∧
      stored.lookup firstIdentity = some (.array before.heap.length) ∧
      after.heap[before.heap.length]? = some [] := by
  obtain ⟨stored, slots, methods, _⟩ := contract.fields
  exact ⟨stored, by simp [slots], methods, by simp [contract.arrays]⟩

theorem instance_separate_arrays (before after : State) (prototype : Option Nat)
    (firstIdentity owner : Nat) (emptyParams : Value)
    (_contract : InstanceContract before after prototype firstIdentity owner emptyParams) :
    before.heap.length ≠ before.heap.length + 1 := by omega

end HonoLean.Upstream.NodeInitialization
