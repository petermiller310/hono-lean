import HonoLean.Upstream.MethodsLoopInitial.Correctness
import HonoLean.Upstream.NodePrivateWrite.Transport

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025 MethodsLoopInitial

/-- Restrict row admission while retaining the complete set of mutable handler
records. A first call therefore protects reads needed by the second call. -/
theorem layout_prefix {origin : State} {left right : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin (left ++ right) method collector keyBound records parameterReceiver nodeParams initial) :
    Layout origin left method collector keyBound records parameterReceiver nodeParams initial := by
  refine {layout with capacity := ?_, rowChoices := ?_}
  · have := layout.capacity; simp only [List.length_append] at this; omega
  · intro count inside
    obtain ⟨row, chosen, atRow, safe, choice, admitted⟩ := layout.rowChoices count (by simp; omega)
    rw [List.getElem?_append_left inside] at atRow
    exact ⟨row, chosen, atRow, safe, choice, admitted⟩

theorem layout_suffix {origin : State} {left right : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin (left ++ right) method collector keyBound records parameterReceiver nodeParams initial) :
    Layout origin right method collector keyBound records parameterReceiver nodeParams initial := by
  refine {layout with capacity := ?_, rowChoices := ?_}
  · have := layout.capacity; simp only [List.length_append] at this; omega
  · intro count inside
    obtain ⟨row, chosen, atRow, safe, choice, admitted⟩ := layout.rowChoices (left.length + count) (by simp; omega)
    rw [List.getElem?_append_right (by omega)] at atRow
    refine ⟨row, chosen, ?_, safe, choice, admitted⟩
    simpa using atRow

theorem layout_keyBound {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound larger : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (bound : keyBound ≤ larger) :
    Layout origin rows method collector larger records parameterReceiver nodeParams initial := by
  refine {layout with recordsFound := ?_}
  intro record member
  exact {layout.recordsFound record member with keyBound := Nat.le_trans (layout.recordsFound record member).keyBound bound}

/-- The helper's target node is not a free capture binding. Rebinding that
formal, runtime this, or private names does not alter the admitted read cells. -/
theorem layout_environment {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (environment : List (String × Value)) (thisValue : Value) (privateNames : List (String × Nat))
    (bindings : ∀ name, name ∈ ["handlerSets", "params", "nodeParams", "METHOD_NAME_ALL", "createNullObject"] →
      environment.lookup name = origin.environment.lookup name) :
    Layout {origin with environment, thisValue, privates := {origin.privates with names := privateNames}}
      rows method collector keyBound records parameterReceiver nodeParams initial := by
  refine {layout with
    collectorBinding := (bindings _ (by simp)).trans layout.collectorBinding
    parameterBinding := (bindings _ (by simp)).trans layout.parameterBinding
    nodeBinding := (bindings _ (by simp)).trans layout.nodeBinding
    allBinding := (bindings _ (by simp)).trans layout.allBinding
    helper := ?_
    recordsFound := ?_
    rowChoices := ?_ }
  · obtain ⟨reference, env, binding, found, standard⟩ := layout.helper
    exact ⟨reference, env, (bindings _ (by simp)).trans binding, found, standard⟩
  · intro record member
    have facts := layout.recordsFound record member
    refine {facts with reads := ?_}
    intro key keyMember
    obtain ⟨parameterRead, nodeRead⟩ := facts.reads key keyMember
    constructor
    · exact NodePrivateWrite.parameterRead_frame (before := origin)
        (after := {origin with environment, thisValue, privates := {origin.privates with names := privateNames}}) rfl parameterRead
    · exact nodeRead
  · intro count inside
    obtain ⟨row, chosen, atRow, safe, choice, admitted⟩ := layout.rowChoices count inside
    refine ⟨row, chosen, atRow, safe, ?_, admitted⟩
    have all := bindings "METHOD_NAME_ALL" (by simp)
    simpa only [SearchEntry.Choice, all] using choice

/-- A capture allocates one null-prototype cell. Admitted mutable handlers were
already present at entry, so later captures cannot turn a fresh cell into a
handler cell. This additional derived fact supports a fresh initial layout. -/
theorem processed_new_null {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound count : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value} {selected : List ObjectRef}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (trace : MethodsLoop.Processed origin rows method collector count before selected) :
    ∀ reference, origin.objects.length ≤ reference → ∀ object,
      before.objects[reference]? = some object → object.prototype = none := by
  induction trace with
  | start =>
    intro reference outside object found
    have := (List.getElem?_eq_some_iff.mp found).1
    change reference < origin.objects.length at this
    omega
  | skip _ _ _ _ ih => exact ih
  | @capture count before after selected row handlerRef handler keysArray priorHandlers parameterReceiver' nodeParams' snapshot
      prior atRow choice entry contract ih =>
    have invariant := processed_invariant layout prior
    obtain ⟨record, member, equal⟩ := chosen_record layout invariant count row handlerRef atRow (processed_all_binding prior) choice
    have handlerOld : handlerRef < origin.objects.length := by
      rw [equal]
      exact (List.getElem?_eq_some_iff.mp (layout.recordsFound record member).found).1
    intro reference outside object found
    change after.objects[reference]? = some object at found
    by_cases fresh : reference = before.objects.length
    · subst reference
      obtain ⟨output, captured, rfl⟩ := contract
      have inside : before.objects.length < (NodeParamLoop.setupState
          (MethodsLoop.selectedState before row (.object handlerRef)) handlerRef handler collector priorHandlers).objects.length := by
        rw [NodeParamLoop.setup_length]
        change before.objects.length < before.objects.length + 1
        omega
      change ((NodeParamLoop.setupState (MethodsLoop.selectedState before row (.object handlerRef))
        handlerRef handler collector priorHandlers).objects.set before.objects.length output)[before.objects.length]? = some object at found
      rw [List.getElem?_set_self inside] at found
      cases Option.some.inj found
      exact (NodeParamLoop.prefix_null_extensible captured).1
    · have inside : reference < before.objects.length := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        rw [block_length contract] at bound
        change reference < before.objects.length + 1 at bound
        omega
      have different : reference ≠ handlerRef := Nat.ne_of_gt (Nat.lt_of_lt_of_le handlerOld outside)
      have old := block_old_cell contract reference inside different
      exact ih reference outside object (old.symm.trans found)

def currentRecord (before : State) (record : Record) : Record :=
  {record with object := before.objects[record.reference]?.getD record.object}

def currentRecords (before : State) (records : List Record) : List Record := records.map (currentRecord before)

theorem currentRecord_found {origin before : State} {collector : Nat} {records : List Record}
    (invariant : Invariant origin before collector records) (record : Record) (member : record ∈ records) :
    before.objects[record.reference]? = some (currentRecord before record).object ∧
      Shape record (currentRecord before record).object := by
  obtain ⟨object, found, shape⟩ := invariant.handlers record member
  simpa [currentRecord, found] using And.intro found shape

theorem protected_rebased {origin before : State} {collector : Nat} {records : List Record}
    (invariant : Invariant origin before collector records) (reference : Nat)
    (safe : Protected origin records reference) : Protected before (currentRecords before records) reference := by
  refine ⟨Nat.lt_of_lt_of_le safe.1 invariant.oldBound, ?_⟩
  intro record member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact safe.2 old oldMember

theorem rebased_old_protected {origin before : State} {records : List Record}
    (reference : Nat) (inside : reference < origin.objects.length)
    (safe : Protected before (currentRecords before records) reference) : Protected origin records reference := by
  refine ⟨inside, ?_⟩
  intro record member
  exact safe.2 (currentRecord before record) (List.mem_map.mpr ⟨record, member, rfl⟩)

/-- Rebase an initially admitted row set after a different admitted prefix.
All inputs below are structural consequences of that prefix's trace. In
particular no later Entry or successful evaluator result is assumed. -/
theorem rebase_layout {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial current : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (invariant : Invariant origin before collector records)
    (newNull : ∀ reference, origin.objects.length ≤ reference → ∀ object,
      before.objects[reference]? = some object → object.prototype = none)
    (bindings : ∀ name, name ∈ ["handlerSets", "params", "nodeParams", "METHOD_NAME_ALL", "createNullObject"] →
      before.environment.lookup name = origin.environment.lookup name)
    (collectorFound : before.heap[collector]? = some current)
    (capacity : current.length + rows.length ≤ 4294967295) :
    Layout before rows method collector keyBound (currentRecords before records) parameterReceiver nodeParams current := by
  refine {
    collectorBinding := (bindings _ (by simp)).trans layout.collectorBinding
    parameterBinding := (bindings _ (by simp)).trans layout.parameterBinding
    nodeBinding := (bindings _ (by simp)).trans layout.nodeBinding
    allBinding := ?_
    helper := ?_
    collectorFound := collectorFound
    capacity := capacity
    closed := invariant.closed
    protectedParents := ?_
    nodeProtected := protected_rebased invariant _ layout.nodeProtected
    parameterProtected := fun reference equal => protected_rebased invariant reference (layout.parameterProtected reference equal)
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · exact (bindings _ (by simp)).trans layout.allBinding
  · obtain ⟨reference, environment, binding, found, standard⟩ := layout.helper
    exact ⟨reference, environment, (bindings _ (by simp)).trans binding, invariant.functions ▸ found, standard⟩
  · intro reference safe object found parent atParent
    by_cases inside : reference < origin.objects.length
    · have oldSafe := rebased_old_protected reference inside safe
      have oldFound := (invariant.protectedFrame reference oldSafe).symm.trans found
      exact protected_rebased invariant parent (layout.protectedParents reference oldSafe object oldFound parent atParent)
    · rw [newNull reference (by omega) object found] at atParent
      cases atParent
  · intro record member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have facts := layout.recordsFound old oldMember
    obtain ⟨found, shape⟩ := currentRecord_found invariant old oldMember
    refine {
      found := found
      possibleKeys := shape.2.2.1.trans facts.possibleKeys
      keysFound := (invariant.arrays old.keysArray (Ne.symm facts.separate)).trans facts.keysFound
      separate := facts.separate
      resettable := current_resettable layout invariant old oldMember _ found shape
      unique := facts.unique
      legalKeys := facts.legalKeys
      keyBound := facts.keyBound
      reads := ?_ }
    intro key keyMember
    obtain ⟨parameterRead, nodeRead⟩ := facts.reads key keyMember
    refine ⟨parameter_read_frame layout invariant.protectedFrame key _ parameterRead, ?_⟩
    rw [← get_protected propertyFuel invariant.protectedFrame layout.protectedParents nodeParams layout.nodeProtected key]
    exact nodeRead
  · intro record member parent atParent
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have shape := (currentRecord_found invariant old oldMember).2
    rw [shape.1] at atParent
    exact protected_rebased invariant parent (layout.handlerParents old oldMember parent atParent)
  · intro count inside
    obtain ⟨row, chosen, atRow, safe, choice, admitted⟩ := layout.rowChoices count inside
    refine ⟨row, chosen, atRow, protected_rebased invariant row safe,
      (choice_frame invariant.protectedFrame layout.protectedParents row safe (bindings _ (by simp)) method chosen).mp choice, ?_⟩
    intro truth
    obtain ⟨record, member, equal⟩ := admitted truth
    exact ⟨currentRecord before record, List.mem_map.mpr ⟨record, member, rfl⟩, equal⟩

end HonoLean.Upstream.NodeLiteralBranch
