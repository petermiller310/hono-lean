import HonoLean.Upstream.NodeIterationSetup.Contract

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset ECMA2025 MethodsLoopInitial

theorem old_array_append {before after : State} (extra : List (List Value))
    (heap : after.heap = before.heap ++ extra) (reference : Nat) (values : List Value)
    (found : before.heap[reference]? = some values) : after.heap[reference]? = some values := by
  rw [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Fresh setup arrays preserve initial helper admission. This transports
initial cells and reads only; it assumes no later Entry or successful call. -/
theorem layout_heap_append {before after : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List Record} {parameterReceiver : Value}
    {nodeParams : Nat} {initial : List Value}
    (layout : Layout before rows method collector keyBound records parameterReceiver nodeParams initial)
    (environment : after.environment = before.environment)
    (objects : after.objects = before.objects) (functions : after.functions = before.functions)
    (extra : List (List Value)) (heap : after.heap = before.heap ++ extra) :
    Layout after rows method collector keyBound records parameterReceiver nodeParams initial := by
  refine {
    collectorBinding := by simpa [environment] using layout.collectorBinding
    parameterBinding := by simpa [environment] using layout.parameterBinding
    nodeBinding := by simpa [environment] using layout.nodeBinding
    allBinding := by simpa [SearchEntry.AllImportBinding, environment] using layout.allBinding
    helper := ?_
    collectorFound := old_array_append extra heap collector initial layout.collectorFound
    capacity := layout.capacity
    closed := by simpa [objects] using layout.closed
    protectedParents := by simpa [Protected, objects] using layout.protectedParents
    nodeProtected := by simpa [Protected, objects] using layout.nodeProtected
    parameterProtected := by simpa [Protected, objects] using layout.parameterProtected
    recordsFound := ?_
    handlerParents := by simpa [Protected, objects] using layout.handlerParents
    rowChoices := by simpa [Protected, SearchEntry.Choice, environment, objects] using layout.rowChoices }
  · obtain ⟨reference, helperEnvironment, binding, found, standard⟩ := layout.helper
    exact ⟨reference, helperEnvironment, by simpa [environment] using binding,
      by simpa [functions] using found, standard⟩
  · intro record member
    have facts := layout.recordsFound record member
    refine {
      found := by simpa [objects] using facts.found
      possibleKeys := facts.possibleKeys
      keysFound := old_array_append extra heap record.keysArray _ facts.keysFound
      separate := facts.separate
      resettable := by simpa [objects] using facts.resettable
      unique := facts.unique
      legalKeys := facts.legalKeys
      keyBound := facts.keyBound
      reads := ?_ }
    intro key used
    obtain ⟨parameter, node⟩ := facts.reads key used
    exact ⟨NodePrivateWrite.parameterRead_frame objects parameter, by simpa [objects] using node⟩

theorem branch_heap (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) :
    (branchEntry before parts nodes i j).heap = before.heap ++ [[]] := rfl

theorem branch_objects (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) :
    (branchEntry before parts nodes i j).objects = before.objects := rfl

theorem branch_privates (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) :
    (branchEntry before parts nodes i j).privates = before.privates := rfl

theorem branch_lookup_other (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (name : String)
    (fresh : name ∉ ["node", "j", "tempNodes", "isLast", "part", "i", "partOffsets", "len"]) :
    (branchEntry before parts nodes i j).environment.lookup name = before.environment.lookup name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
  simp only [branchEntry, nodeState, innerActivation, outerState, outerActivation, lengthState,
    List.cons_append, List.nil_append, List.lookup_cons,
    beq_false_of_ne fresh.1, beq_false_of_ne fresh.2.1, beq_false_of_ne fresh.2.2.1,
    beq_false_of_ne fresh.2.2.2.1, beq_false_of_ne fresh.2.2.2.2.1,
    beq_false_of_ne fresh.2.2.2.2.2.1, beq_false_of_ne fresh.2.2.2.2.2.2.1,
    beq_false_of_ne fresh.2.2.2.2.2.2.2]

theorem branch_storage {before : State} (parts : List JSString) (nodes : List Nat) (i j : Nat)
    {closure : PrivateMethodClosure} {target stamp methods collector : Nat} {rows : List Value}
    (storage : NodePrivateCall.Storage before closure target stamp methods collector rows) :
    NodePrivateCall.Storage (branchEntry before parts nodes i j) closure target stamp methods collector rows :=
  ⟨storage.targetFound, storage.privateName, storage.privateSlot,
    old_array_append [[]] rfl methods rows storage.methodsFound, storage.separate, storage.legalLength⟩

theorem branch_callable {before : State} (parts : List JSString) (nodes : List Nat) (i j : Nat)
    {table : PrivateMethodTable} {closure : PrivateMethodClosure} {receiver handle : Nat}
    (callable : NodePrivateCall.Callable before table closure receiver handle) :
    NodePrivateCall.Callable (branchEntry before parts nodes i j) table closure receiver handle :=
  ⟨callable.sourceProgram, callable.tableSeparate, callable.handleBound, callable.closureFound, callable.privateRead⟩

theorem branch_layout {before : State} (parts : List JSString) (nodes : List Nat) (i j : Nat)
    {closure : PrivateMethodClosure} {receiver collector target keyBound nodeParams : Nat}
    {rows : List Value} {query : JSString} {records : List Record} {initial : List Value}
    (layout : Layout (NodePrivateCall.bodyState before closure (.object receiver) collector target query nodeParams .undefined)
      rows query collector keyBound records .undefined nodeParams initial) :
    Layout (NodePrivateCall.bodyState (branchEntry before parts nodes i j) closure (.object receiver)
      collector target query nodeParams .undefined) rows query collector keyBound records .undefined nodeParams initial :=
  layout_heap_append layout rfl rfl rfl [[]] rfl

theorem fresh_queue_separate {before : State} (collector : Nat) (initial : List Value)
    (found : before.heap[collector]? = some initial) : before.heap.length ≠ collector := by
  have := (List.getElem?_eq_some_iff.mp found).1
  omega

end HonoLean.Upstream.NodeIterationSetup
