import HonoLean.Upstream.MethodsLoopInitial.Contract

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

theorem lookup_protected (fuel : Nat) {origin before : State} {records : List Record}
    (frame : ∀ reference, Protected origin records reference → before.objects[reference]? = origin.objects[reference]?)
    (parents : ∀ reference, Protected origin records reference → ∀ object,
      origin.objects[reference]? = some object → ∀ parent, object.prototype = some parent → Protected origin records parent)
    (reference : Nat) (safe : Protected origin records reference) (key : JSString) :
    lookupProperty fuel origin.objects reference key = lookupProperty fuel before.objects reference key := by
  induction fuel generalizing reference with
  | zero => rfl
  | succ fuel ih =>
    cases found : origin.objects[reference]? with
    | none => simp [lookupProperty, frame reference safe, found]
    | some object =>
      cases own : object.own.lookup key with
      | some descriptor => simp [lookupProperty, frame reference safe, found, own]
      | none =>
        cases parent : object.prototype with
        | none => simp [lookupProperty, frame reference safe, found, own, parent]
        | some next =>
          simp only [lookupProperty, frame reference safe, found, own, parent]
          exact ih next (parents reference safe object found next parent)

theorem get_protected (fuel : Nat) {origin before : State} {records : List Record}
    (frame : ∀ reference, Protected origin records reference → before.objects[reference]? = origin.objects[reference]?)
    (parents : ∀ reference, Protected origin records reference → ∀ object,
      origin.objects[reference]? = some object → ∀ parent, object.prototype = some parent → Protected origin records parent)
    (reference : Nat) (safe : Protected origin records reference) (key : JSString) :
    getProperty fuel origin.objects reference key = getProperty fuel before.objects reference key := by
  unfold getProperty
  rw [lookup_protected fuel frame parents reference safe key]
  cases lookupProperty fuel before.objects reference key with
  | error error => rfl
  | ok descriptor =>
    cases descriptor with
    | none => rfl
    | some descriptor =>
      cases descriptor with
      | data => rfl
      | accessor getter setter enumerable configurable =>
        exact NodeParamLoop.callGetter_frame getter origin.objects before.objects reference (frame reference safe).symm

theorem lookup_same_root (fuel : Nat) {origin before : State} {records : List Record}
    (frame : ∀ reference, Protected origin records reference → before.objects[reference]? = origin.objects[reference]?)
    (parents : ∀ reference, Protected origin records reference → ∀ object,
      origin.objects[reference]? = some object → ∀ parent, object.prototype = some parent → Protected origin records parent)
    (reference : Nat) (object : OrdinaryObject)
    (old : origin.objects[reference]? = some object) (current : before.objects[reference]? = some object)
    (rootParents : ∀ parent, object.prototype = some parent → Protected origin records parent) (key : JSString) :
    lookupProperty fuel origin.objects reference key = lookupProperty fuel before.objects reference key := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases own : object.own.lookup key with
    | some descriptor => simp [lookupProperty, old, current, own]
    | none =>
      cases parent : object.prototype with
      | none => simp [lookupProperty, old, current, own, parent]
      | some next =>
        simpa only [lookupProperty, old, current, own, parent] using
          lookup_protected fuel frame parents next (rootParents next parent) key

theorem initial_invariant {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (environment : List (String × Value)) :
    Invariant origin {origin with environment} collector records := by
  refine ⟨Nat.le_refl _, ?_, ?_, rfl, layout.closed, ?_⟩
  · intro reference _; rfl
  · intro reference _; rfl
  · intro record member
    exact ⟨record.object, (layout.recordsFound record member).found, rfl, rfl, rfl, Or.inl rfl⟩

theorem block_length {before after : State} {handlerRef collector : Nat} {handler : OrdinaryObject}
    {prior : List Value} {snapshot : NodeParamLoop.Snapshot}
    (contract : NodeParamLoop.BlockContract before after handlerRef handler collector prior snapshot) :
    after.objects.length = before.objects.length + 1 := by
  obtain ⟨output, _, rfl⟩ := contract
  simp [NodeParamLoop.setupState, NodeParamLoop.resetState]

theorem block_old_cell {before after : State} {handlerRef collector : Nat} {handler : OrdinaryObject}
    {prior : List Value} {snapshot : NodeParamLoop.Snapshot}
    (contract : NodeParamLoop.BlockContract before after handlerRef handler collector prior snapshot)
    (reference : Nat) (inside : reference < before.objects.length) (different : reference ≠ handlerRef) :
    after.objects[reference]? = before.objects[reference]? := by
  obtain ⟨output, _, rfl⟩ := contract
  simp only [NodeParamLoop.setupState, NodeParamLoop.resetState]
  rw [List.getElem?_set_ne (by omega : before.objects.length ≠ reference)]
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_set_ne (Ne.symm different)]

theorem block_handler_cell {before after : State} {handlerRef collector : Nat} {handler : OrdinaryObject}
    {prior : List Value} {snapshot : NodeParamLoop.Snapshot}
    (found : before.objects[handlerRef]? = some handler)
    (contract : NodeParamLoop.BlockContract before after handlerRef handler collector prior snapshot) :
    after.objects[handlerRef]? = some (newDataObject handler NodeParamAssignment.paramsKey (.object before.objects.length)) := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
  obtain ⟨output, _, rfl⟩ := contract
  rw [List.getElem?_set_ne (by omega : before.objects.length ≠ handlerRef)]
  exact NodeParamLoop.setup_handler before handlerRef handler collector prior found

theorem block_closed {before after : State} {handlerRef collector : Nat} {handler : OrdinaryObject}
    {prior : List Value} {snapshot : NodeParamLoop.Snapshot}
    (found : before.objects[handlerRef]? = some handler)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (contract : NodeParamLoop.BlockContract before after handlerRef handler collector prior snapshot) :
    NodeParamLoop.PrototypeClosed after.objects after.objects.length := by
  obtain ⟨output, captured, rfl⟩ := contract
  have outputNull := (NodeParamLoop.prefix_null_extensible captured).1
  have oldClosed := NodeParamLoop.setup_prototype_closed before handlerRef handler collector prior found closed
  intro reference inside object atObject parent prototype
  have length : (NodeParamLoop.setupState before handlerRef handler collector prior).objects.length = before.objects.length + 1 :=
    NodeParamLoop.setup_length before handlerRef handler collector prior
  have freshInside : before.objects.length < (NodeParamLoop.setupState before handlerRef handler collector prior).objects.length := by omega
  by_cases fresh : reference = before.objects.length
  · subst reference
    rw [List.getElem?_set_self freshInside] at atObject
    cases Option.some.inj atObject
    rw [outputNull] at prototype
    cases prototype
  · have earlier : reference < before.objects.length := by
      have bound : reference < before.objects.length + 1 := by simpa only [List.length_set, length] using inside
      omega
    rw [List.getElem?_set_ne (Ne.symm fresh)] at atObject
    have parentBound := oldClosed reference earlier object atObject parent prototype
    simpa only [List.length_set, length] using Nat.lt_succ_of_lt parentBound

theorem shape_reset (record : Record) (object : OrdinaryObject) (value : Value)
    (shape : Shape record object) : Shape record (newDataObject object NodeParamAssignment.paramsKey value) := by
  refine ⟨shape.1, shape.2.1, ?_, Or.inr ⟨value, putOwn_self _ _ _⟩⟩
  rw [newDataObject, NodeParamLoop.putOwn_other _ _ _ _ (by decide)]
  exact shape.2.2.1

theorem choice_frame {origin before : State} {records : List Record}
    (frame : ∀ reference, Protected origin records reference → before.objects[reference]? = origin.objects[reference]?)
    (parents : ∀ reference, Protected origin records reference → ∀ object,
      origin.objects[reference]? = some object → ∀ parent, object.prototype = some parent → Protected origin records parent)
    (row : Nat) (safe : Protected origin records row)
    (environment : before.environment.lookup "METHOD_NAME_ALL" = origin.environment.lookup "METHOD_NAME_ALL")
    (method : JSString) (chosen : Value) :
    SearchEntry.Choice origin row method chosen ↔ SearchEntry.Choice before row method chosen := by
  unfold SearchEntry.Choice
  simp only [← get_protected propertyFuel frame parents row safe, environment]

theorem processed_all_binding {origin before : State} {rows : List Value} {method : JSString}
    {collector count : Nat} {selected : List ObjectRef}
    (trace : MethodsLoop.Processed origin rows method collector count before selected) :
    before.environment.lookup "METHOD_NAME_ALL" = origin.environment.lookup "METHOD_NAME_ALL" := by
  rw [MethodsLoop.processed_environment trace]
  exact NodeParamLoop.header_lookup_other _ _ _ _ (by decide) (by decide)

theorem chosen_record {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (invariant : Invariant origin before collector records)
    (count : Nat) (row handlerRef : Nat)
    (atRow : rows[count]? = some (.object row))
    (environment : before.environment.lookup "METHOD_NAME_ALL" = origin.environment.lookup "METHOD_NAME_ALL")
    (choice : SearchEntry.Choice before row method (.object handlerRef)) :
    ∃ record ∈ records, handlerRef = record.reference := by
  have inside := (List.getElem?_eq_some_iff.mp atRow).1
  obtain ⟨initialRow, chosen, initialAt, safe, initialChoice, admitted⟩ := layout.rowChoices count inside
  have rowEqual : initialRow = row := Value.object.inj (Option.some.inj (initialAt.symm.trans atRow))
  subst initialRow
  have transferred := (choice_frame invariant.protectedFrame layout.protectedParents row safe environment method chosen).mp initialChoice
  have same := MethodsLoopSupport.choice_unique before row method chosen (.object handlerRef) transferred choice
  subst chosen
  obtain ⟨record, member, equal⟩ := admitted (by simp [NodeParamAssignment.Truthy])
  exact ⟨record, member, Value.object.inj equal⟩

theorem capture_invariant {origin before after : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (invariant : Invariant origin before collector records)
    (handlerRef : Nat) (handler : OrdinaryObject) (prior : List Value) (snapshot : NodeParamLoop.Snapshot)
    (member : ∃ record ∈ records, handlerRef = record.reference)
    (found : before.objects[handlerRef]? = some handler)
    (contract : NodeParamLoop.BlockContract before after handlerRef handler collector prior snapshot) :
    Invariant origin after collector records := by
  obtain ⟨record, member, equal⟩ := member
  refine ⟨?_, ?_, ?_, ?_, block_closed found invariant.closed contract, ?_⟩
  · rw [block_length contract]
    exact Nat.le_trans invariant.oldBound (Nat.le_succ _)
  · intro reference safe
    have inside : reference < before.objects.length := Nat.lt_of_lt_of_le safe.1 invariant.oldBound
    have different : reference ≠ handlerRef := by rw [equal]; exact safe.2 record member
    exact (block_old_cell contract reference inside different).trans (invariant.protectedFrame reference safe)
  · intro reference different
    obtain ⟨output, _, rfl⟩ := contract
    simpa [NodeParamLoop.setupState, NodeParamLoop.resetState, List.getElem?_set_ne (Ne.symm different)] using invariant.arrays reference different
  · obtain ⟨output, _, rfl⟩ := contract
    exact invariant.functions
  · intro other otherMember
    obtain ⟨current, currentFound, shape⟩ := invariant.handlers other otherMember
    by_cases same : other.reference = handlerRef
    · have sameObject : current = handler := Option.some.inj (currentFound.symm.trans (same ▸ found))
      subst current
      refine ⟨newDataObject handler NodeParamAssignment.paramsKey (.object before.objects.length), ?_, shape_reset other handler _ shape⟩
      rw [same]
      exact block_handler_cell found contract
    · have inside : other.reference < before.objects.length :=
        Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp (layout.recordsFound other otherMember).found).1 invariant.oldBound
      exact ⟨current, (block_old_cell contract other.reference inside same).trans currentFound, shape⟩

theorem processed_invariant {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound count : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    {selected : List ObjectRef}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (trace : MethodsLoop.Processed origin rows method collector count before selected) :
    Invariant origin before collector records := by
  induction trace with
  | start => exact initial_invariant layout _
  | skip prior _ _ _ ih => exact ⟨ih.oldBound, ih.protectedFrame, ih.arrays, ih.functions, ih.closed, ih.handlers⟩
  | @capture count before after selected row handlerRef handler keysArray priorHandlers parameterReceiver' nodeParams' snapshot
      prior atRow choice entry contract ih =>
    have member := chosen_record layout ih count row handlerRef atRow (processed_all_binding prior) choice
    have selectedInvariant : Invariant origin (MethodsLoop.selectedState before row (.object handlerRef)) collector records :=
      ⟨ih.oldBound, ih.protectedFrame, ih.arrays, ih.functions, ih.closed, ih.handlers⟩
    have afterInvariant := capture_invariant layout selectedInvariant handlerRef handler priorHandlers snapshot member entry.handlerFound contract
    exact ⟨afterInvariant.oldBound, afterInvariant.protectedFrame, afterInvariant.arrays,
      afterInvariant.functions, afterInvariant.closed, afterInvariant.handlers⟩

end HonoLean.Upstream.MethodsLoopInitial
