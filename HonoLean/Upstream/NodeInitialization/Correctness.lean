import HonoLean.Upstream.NodeInitialization.Runtime
import HonoLean.Upstream.NodeInitialization.Seed

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

theorem stored_fields (before : State) (firstIdentity : Nat) (emptyParams : Value) :
    FieldsStored (storedFields before firstIdentity emptyParams) firstIdentity
      before.heap.length (before.heap.length + 1) (before.objects.length + 1) emptyParams := by
  have d04 : (firstIdentity == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d03 : (firstIdentity == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d02 : (firstIdentity == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d01 : (firstIdentity == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d14 : (firstIdentity + 1 == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d13 : (firstIdentity + 1 == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d12 : (firstIdentity + 1 == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d24 : (firstIdentity + 2 == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d23 : (firstIdentity + 2 == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d34 : (firstIdentity + 3 == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [FieldsStored, storedFields, List.lookup, d04, d03, d02, d01, d14, d13, d12, d24, d23, d34]

theorem instance_contract (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value) :
    InstanceContract before (instanceState before prototype environment firstIdentity emptyParams)
      prototype firstIdentity before.objects.length emptyParams := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    storedFields before firstIdentity emptyParams, rfl, stored_fields before firstIdentity emptyParams⟩

/-- The generic private-data parser and ordered initializer execute the exact
five source declarations. The instance endpoint is constructed, not assumed.
The prototype/helper/captured-value context is a declared interpretation domain. -/
theorem parsed_instance_satisfies (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (prototypeReady : PrototypeReady before prototype)
    (bindings : InitializerBindings before environment emptyParams) :
    ∃ owner after,
      (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
        (fun fields => instantiateDataClass 64 defaultSplitLimit
          ⟨fields, firstIdentity, environment⟩ prototype before) = some (.ok (owner, after)) ∧
      InstanceContract before after prototype firstIdentity owner emptyParams := by
  refine ⟨before.objects.length, instanceState before prototype environment firstIdentity emptyParams, ?_,
    instance_contract before prototype environment firstIdentity emptyParams⟩
  rw [parses_fields, Option.map_some]
  exact congrArg some (instantiate_node before prototype environment firstIdentity emptyParams fresh prototypeReady bindings)

theorem preamble_initializer_bindings (before : State) (helper : HelperBinding before) :
    InitializerBindings (preambleState before) (preambleState before).environment
      (.object before.objects.length) :=
  ⟨preamble_helper before helper, preamble_empty_binding before⟩

/-- Actual module declarations and selected field initialization derive the
registration Seed. The history owner/slot/counter are not caller-chosen outputs;
the explicit lexical handoff supplies the source-derived data-name context. -/
theorem parsed_initialization_seed (before : State) (prototype : Option Nat) (world : PrivateWorld)
    (helper : HelperBinding before)
    (rootFound : ∃ root, before.objects[0]? = some root)
    (fresh : (preambleState before).privates.slots.lookup (preambleState before).objects.length = none)
    (prototypeReady : PrototypeReady (preambleState before) prototype) :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) =
        some (.ok (.normal (preambleState before))) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
      (fun fields => defineDataClass fields (preambleState before) world) =
        some (definition (preambleState before).environment world.nextIdentity, ⟨world.nextIdentity + 5⟩) ∧
    ∃ owner after,
      (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
        (fun fields => instantiateDataClass 64 defaultSplitLimit
          ⟨fields, world.nextIdentity, (preambleState before).environment⟩ prototype (preambleState before)) =
            some (.ok (owner, after)) ∧
      InstanceContract (preambleState before) after prototype world.nextIdentity owner (.object before.objects.length) ∧
      RegistrationHistory.Seed (classActivation after world.nextIdentity) owner world.nextIdentity before.heap.length 0 [] := by
  refine ⟨?_, parsed_define_node (preambleState before) world, ?_⟩
  · rw [parses_preamble, Option.map_some, run_preamble before helper]
  · obtain ⟨owner, after, execution, contract⟩ := parsed_instance_satisfies (preambleState before) prototype
      (preambleState before).environment world.nextIdentity (.object before.objects.length) fresh prototypeReady
      (preamble_initializer_bindings before helper)
    exact ⟨owner, after, execution, contract,
      initialized_seed before after prototype world.nextIdentity owner rootFound contract⟩

/-- info: 'HonoLean.Upstream.NodeInitialization.parsed_instance_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_instance_satisfies

/-- info: 'HonoLean.Upstream.NodeInitialization.parsed_initialization_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_initialization_seed

end HonoLean.Upstream.NodeInitialization
