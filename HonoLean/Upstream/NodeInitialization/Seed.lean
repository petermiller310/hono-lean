import HonoLean.Upstream.NodeInitialization.Contract
import HonoLean.Upstream.RegistrationHistory.Correctness

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

/-- Explicit class DATA lexical context for the later source fragments. The
names come from the selected declarations/class definition; this handoff does
not install the omitted private method or prove native class/call linking. -/
def classActivation (after : State) (firstIdentity : Nat) : State :=
  {after with privates := {after.privates with names := nodeNames firstIdentity}}

theorem contract_owner_found (before after : State) (prototype : Option Nat)
    (firstIdentity owner : Nat) (emptyParams : Value)
    (contract : InstanceContract before after prototype firstIdentity owner emptyParams) :
    after.objects[owner]? = some ⟨[], prototype, true⟩ := by
  rw [contract.ownerAddress, contract.objects]
  simp

/-- The methods slot, empty methods array and zero counter are conclusions of
the source preamble/instance contracts. Only the old root and class-context
handoff remain as entry facts; no completed Seed is assumed. -/
theorem initialized_seed (moduleBefore after : State) (prototype : Option Nat)
    (firstIdentity owner : Nat)
    (rootFound : ∃ root, moduleBefore.objects[0]? = some root)
    (contract : InstanceContract (preambleState moduleBefore) after prototype firstIdentity owner
      (.object moduleBefore.objects.length)) :
    RegistrationHistory.Seed (classActivation after firstIdentity) owner firstIdentity
      moduleBefore.heap.length 0 [] := by
  obtain ⟨root, found⟩ := rootFound
  have rootInside := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨stored, fieldsFound, methodsFound, arrayFound⟩ :=
    instance_methods (preambleState moduleBefore) after prototype firstIdentity owner
      (.object moduleBefore.objects.length) contract
  refine ⟨?_, ⟨root, ?_⟩, ⟨⟨[], prototype, true⟩, ?_⟩, ?_, ⟨stored, ?_, methodsFound⟩, ?_⟩
  · change after.environment.lookup "order" = some (.number 0)
    rw [contract.environment]
    exact preamble_order moduleBefore
  · change after.objects[0]? = some root
    rw [contract.objects, List.getElem?_append_left (by simp [preambleState])]
    change (moduleBefore.objects ++ [emptyNullObject])[0]? = some root
    rw [List.getElem?_append_left rootInside]
    exact found
  · change after.objects[owner]? = some ⟨[], prototype, true⟩
    exact contract_owner_found _ _ _ _ _ _ contract
  · simp [classActivation, nodeNames]
  · exact fieldsFound
  · change after.heap[moduleBefore.heap.length]? = some []
    simpa [preambleState] using arrayFound

end HonoLean.Upstream.NodeInitialization
