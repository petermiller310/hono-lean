import HonoLean.Upstream.MethodsLoopInitial.Invariant

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

theorem current_resettable {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (invariant : Invariant origin before collector records)
    (record : Record) (member : record ∈ records) (object : OrdinaryObject)
    (found : before.objects[record.reference]? = some object) (shape : Shape record object) :
    NodeParamLoop.Resettable before.objects record.reference object := by
  rcases shape.2.2.2 with original | ⟨value, own⟩
  · subst object
    have lookup := lookup_same_root propertyFuel invariant.protectedFrame layout.protectedParents
      record.reference record.object (layout.recordsFound record member).found found
      (layout.handlerParents record member) NodeParamAssignment.paramsKey
    constructor
    · rw [← lookup]
      exact (layout.recordsFound record member).resettable.1
    · exact (layout.recordsFound record member).resettable.2
  · have lookup : lookupProperty propertyFuel before.objects record.reference NodeParamAssignment.paramsKey =
        .ok (some (.data value true true true)) := by
      simp [propertyFuel, lookupProperty, found, own]
    exact ⟨Or.inr ⟨value, true, true, lookup⟩, Or.inr ⟨value, own⟩⟩

theorem selected_lookup {origin before : State} {rows : List Value} {method : JSString}
    {collector count : Nat} {selected : List ObjectRef}
    (trace : MethodsLoop.Processed origin rows method collector count before selected)
    (row : Nat) (chosen : Value) (name : String)
    (notI : name ≠ "i") (notLen : name ≠ "len") (notM : name ≠ "m") (notHandler : name ≠ "handlerSet") :
    (MethodsLoop.selectedState before row chosen).environment.lookup name = origin.environment.lookup name := by
  simp only [MethodsLoop.selectedState, List.lookup_cons, beq_false_of_ne notHandler]
  rw [MethodsLoop.row_lookup_other before row name notM notHandler, MethodsLoop.processed_environment trace]
  exact NodeParamLoop.header_lookup_other _ _ _ _ notI notLen

theorem selected_length_bound {origin before : State} {rows : List Value} {method : JSString}
    {collector count : Nat} {selected : List ObjectRef}
    (trace : MethodsLoop.Processed origin rows method collector count before selected) : selected.length ≤ count := by
  induction trace with
  | start => simp
  | skip _ _ _ _ ih => exact Nat.le_succ_of_le ih
  | capture _ _ _ _ _ ih => simpa using Nat.succ_le_succ ih

theorem setup_protected_frame {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (_layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (invariant : Invariant origin before collector records)
    (record : Record) (member : record ∈ records) (object : OrdinaryObject) (prior : List Value) :
    ∀ reference, Protected origin records reference →
      (NodeParamLoop.setupState before record.reference object collector prior).objects[reference]? = origin.objects[reference]? := by
  intro reference safe
  have inside := Nat.lt_of_lt_of_le safe.1 invariant.oldBound
  exact (NodeParamLoop.setup_old_cell before record.reference reference object collector prior inside
    (safe.2 record member)).trans (invariant.protectedFrame reference safe)

theorem parameter_read_frame {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (frame : ∀ reference, Protected origin records reference → before.objects[reference]? = origin.objects[reference]?)
    (key : JSString) (value : Value)
    (read : NodeParamAssignment.ParameterRead origin key parameterReceiver value) :
    NodeParamAssignment.ParameterRead before key parameterReceiver value := by
  cases read with
  | object reference value read =>
    apply NodeParamAssignment.ParameterRead.object
    rw [← get_protected propertyFuel frame layout.protectedParents reference
      (layout.parameterProtected reference rfl) key]
    exact read
  | nullish _ missing => exact .nullish _ missing

theorem current_entry {origin before : State} {rows : List Value} {method : JSString}
    {collector keyBound count : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    {selected : List ObjectRef}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (trace : MethodsLoop.Processed origin rows method collector count before selected)
    (inside : count < rows.length) (record : Record) (member : record ∈ records) (row : Nat) :
    ∃ object, NodeParamLoop.Entry (MethodsLoop.selectedState before row (.object record.reference))
      record.reference object collector record.keysArray (initial ++ selected.map Value.object)
      parameterReceiver nodeParams record.snapshot := by
  have invariant := processed_invariant layout trace
  have facts := layout.recordsFound record member
  obtain ⟨object, found, shape⟩ := invariant.handlers record member
  have selectedInvariant : Invariant origin (MethodsLoop.selectedState before row (.object record.reference)) collector records :=
    ⟨invariant.oldBound, invariant.protectedFrame, invariant.arrays, invariant.functions, invariant.closed, invariant.handlers⟩
  have protectedFrame := setup_protected_frame layout selectedInvariant record member object (initial ++ selected.map Value.object)
  refine ⟨object, ?_⟩
  refine {
    toSetupFacts := {
      handlerBinding := by simp [MethodsLoop.selectedState]
      handlersBinding := ?_
      helper := ?_
      handlerFound := found
      resettable := current_resettable layout invariant record member object found shape
      closed := invariant.closed
      handlersFound := by
        change before.heap[collector]? = some (initial ++ selected.map Value.object)
        exact MethodsLoop.processed_collector layout.collectorFound trace }
    possibleKeys := shape.2.2.1.trans facts.possibleKeys
    keysFound := (invariant.arrays record.keysArray (Ne.symm facts.separate)).trans facts.keysFound
    arraysSeparate := facts.separate
    parameterBinding := ?_
    nodeBinding := ?_
    parameterBound := ?_
    nodeBound := Nat.lt_of_lt_of_le layout.nodeProtected.1 invariant.oldBound
    unique := facts.unique
    legalKeys := facts.legalKeys
    pushCapacity := ?_
    reads := ?_ }
  · rw [selected_lookup trace row (.object record.reference) "handlerSets" (by decide) (by decide) (by decide) (by decide)]
    exact layout.collectorBinding
  · obtain ⟨helperRef, environment, binding, functionFound, standard⟩ := layout.helper
    refine ⟨helperRef, environment, ?_, ?_, standard⟩
    · rw [selected_lookup trace row (.object record.reference) "createNullObject" (by decide) (by decide) (by decide) (by decide)]
      exact binding
    · change before.functions[helperRef]? = _
      rw [invariant.functions]
      exact functionFound
  · rw [selected_lookup trace row (.object record.reference) "params" (by decide) (by decide) (by decide) (by decide)]
    exact layout.parameterBinding
  · rw [selected_lookup trace row (.object record.reference) "nodeParams" (by decide) (by decide) (by decide) (by decide)]
    exact layout.nodeBinding
  · intro reference equal
    exact Nat.lt_of_lt_of_le (layout.parameterProtected reference equal).1 invariant.oldBound
  · have bound := selected_length_bound trace
    have capacity := layout.capacity
    simp only [List.length_append, List.length_map]
    omega
  · intro key keyMember
    obtain ⟨parameterRead, nodeRead⟩ := facts.reads key keyMember
    refine ⟨parameter_read_frame layout protectedFrame key _ parameterRead, ?_⟩
    rw [← get_protected propertyFuel protectedFrame layout.protectedParents nodeParams layout.nodeProtected key]
    exact nodeRead

theorem choice_domain {before : State} {row : Nat} {method : JSString} {chosen : Value}
    (choice : SearchEntry.Choice before row method chosen) : SearchEntry.ChoiceDomain before row method := by
  obtain ⟨direct, read, cases⟩ := choice
  refine ⟨direct, read, ?_⟩
  intro falsy
  rcases cases with ⟨truth, _⟩ | ⟨_, key, binding, fallback⟩
  · exact False.elim (falsy truth)
  · exact ⟨key, chosen, binding, fallback⟩

/-- A preservation theorem, not an input condition: initial structural cells,
lookup chains, handler shapes and capacity establish readiness at every
independent prefix. No future evaluator outcome or Entry is supplied. -/
theorem layout_normalPrefixes {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial) :
    MethodsLoop.NormalPrefixes origin rows method collector keyBound := by
  intro count before selected trace inside
  have invariant := processed_invariant layout trace
  obtain ⟨row, chosen, atRow, safe, choice, admitted⟩ := layout.rowChoices count inside
  have currentChoice := (choice_frame invariant.protectedFrame layout.protectedParents row safe
    (processed_all_binding trace) method chosen).mp choice
  refine ⟨row, atRow, choice_domain currentChoice, ?_⟩
  intro other otherChoice truth
  have same := MethodsLoopSupport.choice_unique before row method other chosen otherChoice currentChoice
  subst other
  obtain ⟨record, member, equal⟩ := admitted truth
  subst chosen
  obtain ⟨object, entry⟩ := current_entry layout trace inside record member row
  exact ⟨record.reference, object, record.keysArray, initial ++ selected.map Value.object,
    parameterReceiver, nodeParams, record.snapshot, rfl, entry, (layout.recordsFound record member).keyBound⟩

theorem parsed_initial_satisfies {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (owner stamp methods : Nat)
    (inputs : MethodsLoop.Inputs origin owner stamp methods collector rows method)
    (layout : Layout origin rows method collector keyBound records parameterReceiver nodeParams initial) :
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock (rows.length + keyBound + 103) source origin) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract origin after rows method collector :=
  MethodsLoop.parsed_loop_satisfies keyBound origin owner stamp methods collector rows method inputs (layout_normalPrefixes layout)

/-- info: 'HonoLean.Upstream.MethodsLoopInitial.layout_normalPrefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layout_normalPrefixes

/-- info: 'HonoLean.Upstream.MethodsLoopInitial.parsed_initial_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_initial_satisfies

end HonoLean.Upstream.MethodsLoopInitial
