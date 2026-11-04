import HonoLean.Upstream.RegistrationHistoryLoop.Facts
import HonoLean.Upstream.MethodsLoopInitial.Correctness

namespace HonoLean.Upstream.RegistrationHistoryLoop

open SourceSubset ECMA2025 RegistrationHistory

variable {before registered : State} {requests : List Request} {methods : Nat} {order : Int}
  {searchEnvironment context : List (String × Value)}

theorem objects_equal (contract : HistoryContract before registered methods order [] requests) :
    (activation registered searchEnvironment context).objects =
      before.objects ++ storedObjects before.objects.length before.heap.length order requests := contract.objects

theorem objects_length (contract : HistoryContract before registered methods order [] requests) :
    (activation registered searchEnvironment context).objects.length = before.objects.length + 2 * requests.length := by
  rw [objects_equal contract, List.length_append, stored_objects_length]

theorem heap_length (contract : HistoryContract before registered methods order [] requests) :
    registered.heap.length = before.heap.length + requests.length := by
  rw [contract.heap]
  simp [keySnapshots]

theorem outer_found (contract : HistoryContract before registered methods order [] requests)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (activation registered searchEnvironment context).objects[before.objects.length + 2 * index]? =
      some (HandlerRecord.outerRecord request.method (before.objects.length + 2 * index + 1)) := by
  rw [objects_equal contract, List.getElem?_append_right (by omega)]
  simpa using stored_objects_outer before.objects.length before.heap.length order requests index request atRequest

theorem inner_found (contract : HistoryContract before registered methods order [] requests)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (activation registered searchEnvironment context).objects[before.objects.length + 2 * index + 1]? =
      some (HandlerRecord.innerRecord request.handler (before.heap.length + index) (order + index + 1)) := by
  rw [objects_equal contract, List.getElem?_append_right (by omega)]
  simpa [Nat.add_assoc] using stored_objects_inner before.objects.length before.heap.length order requests index request atRequest

theorem keys_found (contract : HistoryContract before registered methods order [] requests)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (activation registered searchEnvironment context).heap[before.heap.length + index]? =
      some (request.keys.map Value.string) := by
  have inside := (List.getElem?_eq_some_iff.mp atRequest).1
  rw [activation_heap, List.getElem?_append_left (by rw [heap_length contract]; omega), contract.heap,
    List.getElem?_append_right (by simp)]
  simpa [keySnapshots] using congrArg (Option.map (fun item : Request => item.keys.map Value.string)) atRequest

theorem collector_found : (activation registered searchEnvironment context).heap[registered.heap.length]? = some [] := by
  simp [activation_heap]

theorem methods_found (contract : HistoryContract before registered methods order [] requests)
    (found : ∃ prior, before.heap[methods]? = some prior) :
    (activation registered searchEnvironment context).heap[methods]? = some (storedRows before.objects.length requests) := by
  obtain ⟨prior, found⟩ := found
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have regBound : methods < registered.heap.length := by rw [heap_length contract]; omega
  rw [activation_heap, List.getElem?_append_left regBound, contract.heap,
    List.getElem?_append_left (by simpa), List.getElem?_set_self inside]
  rfl

theorem old_protected (contract : HistoryContract before registered methods order [] requests)
    (parameter node : JSString → Value) (reference : Nat) (inside : reference < before.objects.length) :
    MethodsLoopInitial.Protected (activation registered searchEnvironment context)
      (storedRecords before.objects.length before.heap.length order requests parameter node) reference := by
  refine ⟨?_, ?_⟩
  · rw [objects_length contract]; omega
  · intro candidate member
    obtain ⟨index, request, _, equal⟩ := records_index member
    rw [equal]
    change reference ≠ before.objects.length + 2 * index + 1
    omega

theorem row_protected (contract : HistoryContract before registered methods order [] requests)
    (parameter node : JSString → Value) (index : Nat) (inside : index < requests.length) :
    MethodsLoopInitial.Protected (activation registered searchEnvironment context)
      (storedRecords before.objects.length before.heap.length order requests parameter node)
        (before.objects.length + 2 * index) := by
  refine ⟨?_, ?_⟩
  · rw [objects_length contract]; omega
  · intro candidate member
    obtain ⟨other, request, _, equal⟩ := records_index member
    rw [equal]
    change before.objects.length + 2 * index ≠ before.objects.length + 2 * other + 1
    omega

theorem protected_parents (contract : HistoryContract before registered methods order [] requests)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (rootBound : 0 < before.objects.length) (parameter node : JSString → Value) :
    ∀ reference, MethodsLoopInitial.Protected (activation registered searchEnvironment context)
      (storedRecords before.objects.length before.heap.length order requests parameter node) reference →
    ∀ object, (activation registered searchEnvironment context).objects[reference]? = some object →
    ∀ parent, object.prototype = some parent → MethodsLoopInitial.Protected
      (activation registered searchEnvironment context)
      (storedRecords before.objects.length before.heap.length order requests parameter node) parent := by
  intro reference _ object found parent prototype
  by_cases old : reference < before.objects.length
  · rw [objects_equal contract, List.getElem?_append_left old] at found
    exact old_protected contract parameter node parent (closed reference old object found parent prototype)
  · have root := appended_parent before (activation registered searchEnvironment context)
      (storedObjects before.objects.length before.heap.length order requests) (objects_equal contract)
      (stored_objects_parents _ _ _ _) reference (by omega) object found
    have equal : parent = 0 := Option.some.inj (prototype.symm.trans root)
    subst parent
    exact old_protected contract parameter node 0 rootBound

theorem own_read (contract : HistoryContract before registered methods order [] requests)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    getProperty propertyFuel (activation registered searchEnvironment context).objects
      (before.objects.length + 2 * index) request.method =
        .ok (.object (before.objects.length + 2 * index + 1)) :=
  getProperty_data _ _ 31 _ _ _ true true true (outer_found contract index request atRequest)
    (HandlerRecord.outer_method request.method _).1

theorem missing_read (contract : HistoryContract before registered methods order [] requests)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (rootBound : 0 < before.objects.length)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request)
    (query : JSString) (different : query ≠ request.method)
    (rootMiss : lookupProperty 31 before.objects 0 query = .ok none) :
    getProperty propertyFuel (activation registered searchEnvironment context).objects
      (before.objects.length + 2 * index) query = .ok .undefined := by
  have lookup : lookupProperty propertyFuel (activation registered searchEnvironment context).objects
      (before.objects.length + 2 * index) query =
      lookupProperty 31 (activation registered searchEnvironment context).objects 0 query := by
    rw [show propertyFuel = 32 from rfl, lookupProperty, outer_found contract index request atRequest]
    simp [HandlerRecord.outerRecord, List.lookup_cons, beq_false_of_ne different]
  rw [old_lookup_frame before (activation registered searchEnvironment context) _ (objects_equal contract)
    closed 31 0 rootBound query] at lookup
  simp [getProperty, lookup, rootMiss, bind, pure, Except.bind, Except.pure]

/-- All source-produced rows and records enter the one-state protected layout.
The only read witnesses concern old inputs, before any registration allocates
the fresh pairs; no desired row/handler choice or future readiness is supplied. -/
theorem initial_layout (contract : HistoryContract before registered methods order [] requests)
    (rootBound : 0 < before.objects.length) (owner : Nat) (query : JSString)
    (parameterReceiver : Value) (nodeParams keyBound : Nat) (parameter node : JSString → Value)
    (domain : Context before requests context owner query parameterReceiver nodeParams keyBound parameter node) :
    MethodsLoopInitial.Layout (activation registered searchEnvironment context)
      (storedRows before.objects.length requests) query registered.heap.length keyBound
      (storedRecords before.objects.length before.heap.length order requests parameter node)
      parameterReceiver nodeParams [] := by
  have rootProtected := old_protected (searchEnvironment := searchEnvironment) (context := context)
    contract parameter node 0 rootBound
  refine {
    collectorBinding := ?_, parameterBinding := ?_, nodeBinding := ?_, allBinding := ?_, helper := ?_
    collectorFound := collector_found
    capacity := by simpa [stored_rows_length] using domain.capacity
    closed := appended_closed before (activation registered searchEnvironment context) _ (objects_equal contract)
      (stored_objects_parents _ _ _ _) rootBound domain.closed
    protectedParents := protected_parents contract domain.closed rootBound parameter node
    nodeProtected := old_protected contract parameter node nodeParams domain.nodeBound
    parameterProtected := ?_, recordsFound := ?_, handlerParents := ?_, rowChoices := ?_}
  · rfl
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact domain.parameterBinding
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact domain.nodeBinding
  · change (activation registered searchEnvironment context).environment.lookup "METHOD_NAME_ALL" = _
    rw [activation_lookup _ _ _ _ (by decide)]
    exact domain.allBinding
  · obtain ⟨reference, environment, binding, found, standard⟩ := domain.helper
    refine ⟨reference, environment, ?_, ?_, standard⟩
    · rw [activation_lookup _ _ _ _ (by decide)]
      exact binding
    · change registered.functions[reference]? = _
      rw [contract.functions]
      exact found
  · intro reference equal
    exact old_protected contract parameter node reference (domain.parameterBound reference equal)
  · intro candidate member
    obtain ⟨index, request, atRequest, equal⟩ := records_index member
    subst candidate
    have inside := (List.getElem?_eq_some_iff.mp atRequest).1
    have requestMember : request ∈ requests := List.mem_of_getElem? atRequest
    have found := inner_found (searchEnvironment := searchEnvironment) (context := context) contract index request atRequest
    refine {
      found := found
      possibleKeys := (HandlerRecord.inner_fields request.handler (before.heap.length + index) (order + index + 1)).2.1
      keysFound := keys_found contract index request atRequest
      separate := ?_
      resettable := ?_
      unique := StringSet.fromTrace_nodup request.events
      legalKeys := (domain.keyBounds request requestMember).2
      keyBound := (domain.keyBounds request requestMember).1
      reads := ?_}
    · change registered.heap.length ≠ before.heap.length + index
      rw [heap_length contract]
      omega
    · constructor
      · have lookup : lookupProperty propertyFuel (activation registered searchEnvironment context).objects
            (before.objects.length + 2 * index + 1) NodeParamAssignment.paramsKey =
            lookupProperty 31 (activation registered searchEnvironment context).objects 0 HandlerRecord.paramsKey := by
          rw [show propertyFuel = 32 from rfl, lookupProperty, found]
          rfl
        change lookupProperty propertyFuel _ (before.objects.length + 2 * index + 1) NodeParamAssignment.paramsKey = .ok none ∨
          ∃ value enumerable configurable, lookupProperty propertyFuel _ (before.objects.length + 2 * index + 1) NodeParamAssignment.paramsKey =
            .ok (some (.data value true enumerable configurable))
        rw [lookup, old_lookup_frame before (activation registered searchEnvironment context) _ (objects_equal contract)
          domain.closed 31 0 rootBound HandlerRecord.paramsKey]
        exact domain.rootDispatch
      · exact Or.inl ⟨(HandlerRecord.inner_fields request.handler (before.heap.length + index) (order + index + 1)).2.2.2, rfl⟩
    · intro key member
      obtain ⟨parameterRead, nodeRead⟩ := domain.reads request requestMember key member
      constructor
      · exact old_parameter_read before (activation registered searchEnvironment context) _ (objects_equal contract)
          domain.closed parameterReceiver (parameter key) key domain.parameterBound parameterRead
      · rw [old_get_frame before (activation registered searchEnvironment context) _ (objects_equal contract)
          domain.closed nodeParams domain.nodeBound key]
        exact nodeRead
  · intro candidate member parent prototype
    obtain ⟨index, request, _, equal⟩ := records_index member
    subst candidate
    have same : parent = 0 := by simpa [recordAt, HandlerRecord.innerRecord] using prototype.symm
    subst parent
    exact rootProtected
  · intro index inside
    rw [stored_rows_length] at inside
    let request := requests[index]'inside
    have atRequest : requests[index]? = some request := by simp [request]
    have requestMember : request ∈ requests := List.mem_of_getElem? atRequest
    have atRow := stored_rows_index before.objects.length requests index inside
    have safe := row_protected (searchEnvironment := searchEnvironment) (context := context)
      contract parameter node index inside
    have direct := own_read (searchEnvironment := searchEnvironment) (context := context) contract index request atRequest
    have chooseRecord (choice : SearchEntry.Choice (activation registered searchEnvironment context)
          (before.objects.length + 2 * index) query (.object (before.objects.length + 2 * index + 1))) :
        ∃ row chosen, (storedRows before.objects.length requests)[index]? = some (.object row) ∧
          MethodsLoopInitial.Protected (activation registered searchEnvironment context)
            (storedRecords before.objects.length before.heap.length order requests parameter node) row ∧
          SearchEntry.Choice (activation registered searchEnvironment context) row query chosen ∧
          (NodeParamAssignment.Truthy chosen → ∃ candidate ∈
            storedRecords before.objects.length before.heap.length order requests parameter node, chosen = .object candidate.reference) := by
      refine ⟨_, _, atRow, safe, choice, ?_⟩
      intro _
      refine ⟨recordAt (before.objects.length + 2 * index) (before.heap.length + index) (order + index)
        request parameter node, ?_, rfl⟩
      exact record_mem _ _ _ _ parameter node index request atRequest
    rcases domain.queries request requestMember with same | ⟨all, different, rootMiss⟩ | ⟨different, notAll, rootMiss, rootAllMiss⟩
    · subst query
      apply chooseRecord
      exact ⟨_, direct, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
    · have missing := missing_read (searchEnvironment := searchEnvironment) (context := context)
        contract domain.closed rootBound index request atRequest query different rootMiss
      apply chooseRecord
      refine ⟨.undefined, missing, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, ?_, ?_⟩⟩
      · rw [activation_lookup _ _ _ _ (by decide)]
        exact domain.allBinding
      · simpa only [all] using direct
    · have missing := missing_read (searchEnvironment := searchEnvironment) (context := context)
        contract domain.closed rootBound index request atRequest query different rootMiss
      have missingAll := missing_read (searchEnvironment := searchEnvironment) (context := context)
        contract domain.closed rootBound index request atRequest SearchEntry.allKey notAll rootAllMiss
      refine ⟨_, .undefined, atRow, safe,
        ⟨.undefined, missing, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, ?_, missingAll⟩⟩, ?_⟩
      · rw [activation_lookup _ _ _ _ (by decide)]
        exact domain.allBinding
      · intro impossible
        simp [NodeParamAssignment.Truthy] at impossible

end HonoLean.Upstream.RegistrationHistoryLoop
