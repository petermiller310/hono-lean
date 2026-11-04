import HonoLean.Upstream.NodeInitialization.Correctness

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

def initialNodeWorld (before : State) : PrivateWorld := initialPrivateWorld (preambleState before)

/-- Freshness relative to all identities represented in the initial state.
Definitions without instances also require threading the returned reservation
world; rebuilding an initial world cannot recover unrepresented reservations. -/
theorem initial_definition_fresh (before : State) (name : String) (identity : Nat)
    (member : (name, identity) ∈ (definition (preambleState before).environment
      (initialNodeWorld before).nextIdentity).names) :
    identity ∉ storedPrivateIdentities (preambleState before) := by
  intro used
  have lower := (definition_name_range _ name identity member).1
  have smaller := initialPrivateWorld_fresh (preambleState before) identity used
  change (initialNodeWorld before).nextIdentity ≤ identity at lower
  change identity < (initialNodeWorld before).nextIdentity at smaller
  omega

/-- Source-facing initial-world specialization. Private data identities are
derived from the declarations and the fresh reservation cursor, not supplied
desired names/slots. This does not assert unmodeled native class reservations. -/
theorem parsed_fresh_initialization_seed (before : State) (prototype : Option Nat)
    (helper : HelperBinding before)
    (rootFound : ∃ root, before.objects[0]? = some root)
    (fresh : (preambleState before).privates.slots.lookup (preambleState before).objects.length = none)
    (prototypeReady : PrototypeReady (preambleState before) prototype) :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) =
        some (.ok (.normal (preambleState before))) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
      (fun fields => defineDataClass fields (preambleState before) (initialNodeWorld before)) =
        some (definition (preambleState before).environment (initialNodeWorld before).nextIdentity,
          ⟨(initialNodeWorld before).nextIdentity + 5⟩) ∧
    (∀ name identity, (name, identity) ∈ (definition (preambleState before).environment
      (initialNodeWorld before).nextIdentity).names → identity ∉ storedPrivateIdentities (preambleState before)) ∧
    ∃ owner after,
      (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
        (fun fields => instantiateDataClass 64 defaultSplitLimit
          ⟨fields, (initialNodeWorld before).nextIdentity, (preambleState before).environment⟩ prototype (preambleState before)) =
            some (.ok (owner, after)) ∧
      InstanceContract (preambleState before) after prototype (initialNodeWorld before).nextIdentity owner
        (.object before.objects.length) ∧
      RegistrationHistory.Seed (classActivation after (initialNodeWorld before).nextIdentity) owner
        (initialNodeWorld before).nextIdentity before.heap.length 0 [] := by
  obtain ⟨preamble, defined, constructed⟩ := parsed_initialization_seed before prototype (initialNodeWorld before)
    helper rootFound fresh prototypeReady
  exact ⟨preamble, defined, initial_definition_fresh before, constructed⟩

/-- info: 'HonoLean.Upstream.NodeInitialization.parsed_fresh_initialization_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_fresh_initialization_seed

end HonoLean.Upstream.NodeInitialization
