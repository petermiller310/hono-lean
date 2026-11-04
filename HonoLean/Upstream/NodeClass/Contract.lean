import HonoLean.Upstream.NodeClass.Runtime
import HonoLean.Upstream.NodePrivateCall.Contract

namespace HonoLean.Upstream.NodeClass

open SourceSubset ECMA2025

/-- Exact kind/value observations for the source's five data fields and method.
Type annotations do not decide the kind; installation supplies these tags. -/
def TaggedStored (elements : List (Nat × PrivateElement)) (firstIdentity methods patterns children firstHandle : Nat)
    (emptyParams : Value) : Prop :=
  elements.lookup firstIdentity = some (.data (.array methods)) ∧
  elements.lookup (firstIdentity + 1) = some (.data (.object children)) ∧
  elements.lookup (firstIdentity + 2) = some (.data (.array patterns)) ∧
  elements.lookup (firstIdentity + 3) = some (.data .undefined) ∧
  elements.lookup (firstIdentity + 4) = some (.data emptyParams) ∧
  elements.lookup (firstIdentity + 5) = some (.method (.function firstHandle))

/-- Independent allocation/frame/field observations, extended with the installed
private method read handle. Raw DATA/METHOD tags and all older element tags
are retained; native accessors and full class/engine adequacy remain open. -/
structure InstanceContract (before after : State) (prototype : Option Nat)
    (firstIdentity firstHandle owner : Nat) (emptyParams : Value) : Prop extends
    NodeInitialization.InstanceContract before after prototype firstIdentity owner emptyParams where
  methodStored : ∃ stored, after.privates.slots.lookup owner = some stored ∧
    stored.lookup (firstIdentity + 5) = some (.function firstHandle)
  tagged : ∃ elements, after.privates.elements = (owner, elements) :: before.privates.elements ∧
    TaggedStored elements firstIdentity before.heap.length (before.heap.length + 1)
      (before.objects.length + 1) firstHandle emptyParams

def classActivation (after : State) (firstIdentity : Nat) : State :=
  {after with privates := {after.privates with names := names firstIdentity}}

def extendedTable (table : PrivateMethodTable) (environment : List (String × Value))
    (firstIdentity : Nat) : PrivateMethodTable :=
  {table with entries := table.entries ++ [closure environment firstIdentity]}

theorem stored_fields (before : State) (firstIdentity firstHandle : Nat) (emptyParams : Value) :
    NodeInitialization.FieldsStored (storedFields before firstIdentity firstHandle emptyParams) firstIdentity
      before.heap.length (before.heap.length + 1) (before.objects.length + 1) emptyParams := by
  obtain ⟨a, b, c, d, e⟩ := NodeInitialization.stored_fields before firstIdentity emptyParams
  simp [NodeInitialization.FieldsStored, storedFields, List.lookup_append, a, b, c, d, e]

theorem stored_method (before : State) (firstIdentity firstHandle : Nat) (emptyParams : Value) :
    (storedFields before firstIdentity firstHandle emptyParams).lookup (firstIdentity + 5) =
      some (.function firstHandle) := by
  have d50 : (firstIdentity + 5 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d51 : (firstIdentity + 5 == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d52 : (firstIdentity + 5 == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d53 : (firstIdentity + 5 == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d54 : (firstIdentity + 5 == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [storedFields, NodeInitialization.storedFields, List.lookup, d50, d51, d52, d53, d54]

private theorem data_elements_lookup (elements : List (Nat × Value)) (identity : Nat) :
    (dataElements elements).lookup identity = (elements.lookup identity).map PrivateElement.data :=
  lookup_map_values elements PrivateElement.data identity

theorem stored_tagged (before : State) (firstIdentity firstHandle : Nat) (emptyParams : Value) :
    TaggedStored (storedElements before firstIdentity firstHandle emptyParams) firstIdentity
      before.heap.length (before.heap.length + 1) (before.objects.length + 1) firstHandle emptyParams := by
  obtain ⟨a, b, c, d, e⟩ := NodeInitialization.stored_fields before firstIdentity emptyParams
  have d50 : (firstIdentity + 5 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d51 : (firstIdentity + 5 == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d52 : (firstIdentity + 5 == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d53 : (firstIdentity + 5 == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d54 : (firstIdentity + 5 == firstIdentity + 4) = false := beq_eq_false_iff_ne.mpr (by omega)
  have absent : (NodeInitialization.storedFields before firstIdentity emptyParams).lookup (firstIdentity + 5) = none := by
    simp [NodeInitialization.storedFields, List.lookup, d50, d51, d52, d53, d54]
  simp [TaggedStored, storedElements, List.lookup_append, data_elements_lookup, a, b, c, d, e, absent]

theorem instance_contract (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value) :
    InstanceContract before (instanceState before prototype environment firstIdentity firstHandle emptyParams)
      prototype firstIdentity firstHandle before.objects.length emptyParams := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    storedFields before firstIdentity firstHandle emptyParams, rfl,
    stored_fields before firstIdentity firstHandle emptyParams⟩, ?_,
    storedElements before firstIdentity firstHandle emptyParams, rfl, stored_tagged before firstIdentity firstHandle emptyParams⟩
  exact ⟨storedFields before firstIdentity firstHandle emptyParams, by simp [instanceState, rawFieldsState, restoreDataCaller, PrivateStore.slots, storedElements, dataElements, storedFields, NodeInitialization.storedFields],
    stored_method before firstIdentity firstHandle emptyParams⟩

/-- Installing the source-derived method handle preserves the original empty
methods-array Seed; no Seed is assumed as an initialization premise. -/
theorem initialized_seed (moduleBefore after : State) (prototype : Option Nat)
    (firstIdentity firstHandle owner : Nat)
    (rootFound : ∃ root, moduleBefore.objects[0]? = some root)
    (contract : InstanceContract (NodeInitialization.preambleState moduleBefore) after prototype
      firstIdentity firstHandle owner (.object moduleBefore.objects.length)) :
    RegistrationHistory.Seed (classActivation after firstIdentity) owner firstIdentity
      moduleBefore.heap.length 0 [] := by
  have seed := NodeInitialization.initialized_seed moduleBefore after prototype firstIdentity owner
    rootFound contract.toInstanceContract
  exact ⟨seed.orderBinding, seed.rootFound, seed.ownerFound,
    by simp [classActivation, names, NodeInitialization.nodeNames], seed.privateSlot, seed.methodsFound⟩

/-- The callable's program, captured scope, table identity and branded read are
conclusions of definition/initialization. The table prefix and import/helper
value context remain supplied; no completed call execution is assumed. -/
theorem initialized_callable (before after : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity owner : Nat) (emptyParams : Value)
    (table : PrivateMethodTable) (separate : before.functions.length ≤ table.base)
    (contract : InstanceContract before after prototype firstIdentity
      (table.base + table.entries.length) owner emptyParams) :
    NodePrivateCall.Callable (classActivation after firstIdentity)
      (extendedTable table environment firstIdentity) (closure environment firstIdentity)
      owner (table.base + table.entries.length) := by
  obtain ⟨stored, fields, method⟩ := contract.methodStored
  refine ⟨rfl, ?_, by simp [extendedTable], ?_, ?_⟩
  · simpa [classActivation, contract.functions, extendedTable] using separate
  · simp [extendedTable]
  · exact privateGet_field _ owner (firstIdentity + 5) "pushHandlerSets" ⟨[], prototype, true⟩ stored
      (.function (table.base + table.entries.length))
      (by simp [classActivation, names, NodeInitialization.nodeNames, List.lookup])
      (NodeInitialization.contract_owner_found before after prototype firstIdentity owner emptyParams contract.toInstanceContract) fields method

end HonoLean.Upstream.NodeClass
