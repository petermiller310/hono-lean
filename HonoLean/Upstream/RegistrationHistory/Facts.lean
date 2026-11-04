import HonoLean.Upstream.RegistrationHistory.Contract

namespace HonoLean.Upstream.RegistrationHistory

open SourceSubset ECMA2025

theorem stage_order (before : State) (owner : Nat) (request : Request) :
    (stage before owner request).environment.lookup "order" = before.environment.lookup "order" := by
  simpa [stage, List.lookup_cons] using lookup_withoutBindings before.environment
    ["curNode", "method", "handler", "possibleKeys"] "order" (by decide)

theorem stage_inputs (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (request : Request) (seed : Seed before owner stamp methods order prior) :
    NodeMethodsPush.Inputs (stage before owner request) request.method request.handler before.sets.length
      request.keys order owner stamp methods prior := by
  refine {
    methodBinding := rfl
    handlerBinding := rfl
    setBinding := rfl
    setFound := by simp [stage]
    orderBinding := (stage_order before owner request).trans seed.orderBinding
    rootFound := seed.rootFound
    ownerBinding := by simp [stage]
    ownerFound := seed.ownerFound
    privateName := seed.privateName
    privateSlot := seed.privateSlot
    methodsFound := seed.methodsFound }

theorem step_objects (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (request : Request) :
    (step before owner methods order prior request).objects = before.objects ++
      [HandlerRecord.outerRecord request.method (before.objects.length + 1),
       HandlerRecord.innerRecord request.handler before.heap.length (order + 1)] := rfl

theorem step_objects_length (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (request : Request) :
    (step before owner methods order prior request).objects.length = before.objects.length + 2 := by
  simp [step_objects]

theorem step_heap_length (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (request : Request) :
    (step before owner methods order prior request).heap.length = before.heap.length + 1 := by
  simp [step, NodeMethodsPush.pushedState, HandlerRecord.constructedState, stage]

theorem step_seed (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (request : Request) (seed : Seed before owner stamp methods order prior) :
    Seed (step before owner methods order prior request) owner stamp methods (order + 1)
      (prior ++ [.object before.objects.length]) := by
  refine ⟨?_, ?_, ?_, seed.privateName, seed.privateSlot, ?_⟩
  · exact HandlerRecord.replaceOrder_order (stage before owner request).environment order (order + 1)
      ((stage_order before owner request).trans seed.orderBinding)
  · obtain ⟨root, found⟩ := seed.rootFound
    refine ⟨root, ?_⟩
    rw [step_objects, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · obtain ⟨object, found⟩ := seed.ownerFound
    refine ⟨object, ?_⟩
    rw [step_objects, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · exact NodeMethodsPush.pushed_methods_found (stage before owner request) request.method request.handler
      request.keys order methods prior seed.methodsFound

theorem storedRows_length (objectBase : Nat) (requests : List Request) :
    (storedRows objectBase requests).length = requests.length := by
  induction requests generalizing objectBase with
  | nil => rfl
  | cons request rest ih => simp [storedRows, ih]

theorem storedObjects_length (objectBase arrayBase : Nat) (order : Int) (requests : List Request) :
    (storedObjects objectBase arrayBase order requests).length = 2 * requests.length := by
  induction requests generalizing objectBase arrayBase order with
  | nil => rfl
  | cons request rest ih => simp [storedObjects, ih]; omega

theorem end_objects (before : State) (owner methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) :
    (endState before owner methods order prior requests).objects =
      before.objects ++ storedObjects before.objects.length before.heap.length order requests := by
  induction requests generalizing before order prior with
  | nil => simp [endState, storedObjects]
  | cons request rest ih =>
    rw [endState, ih, step_objects_length, step_heap_length, step_objects]
    simp [storedObjects, List.append_assoc]

theorem end_heap (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    (endState before owner methods order prior requests).heap =
      (before.heap.set methods (prior ++ storedRows before.objects.length requests)) ++ keySnapshots requests := by
  induction requests generalizing before order prior with
  | nil =>
    have inside := (List.getElem?_eq_some_iff.mp seed.methodsFound).1
    have same : before.heap.set methods prior = before.heap := by
      obtain ⟨_, equal⟩ := List.getElem?_eq_some_iff.mp seed.methodsFound
      rw [← equal, List.set_getElem_self inside]
    simp [endState, storedRows, keySnapshots, same]
  | cons request rest ih =>
    rw [endState, ih _ _ _ (step_seed before owner stamp methods order prior request seed), step_objects_length]
    have inside := (List.getElem?_eq_some_iff.mp seed.methodsFound).1
    simp only [step, NodeMethodsPush.pushedState, HandlerRecord.constructedState, stage]
    rw [List.set_append_left _ _ (by simpa using inside), List.set_set]
    simp [storedRows, keySnapshots, List.append_assoc]

theorem end_sets (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (requests : List Request) :
    (endState before owner methods order prior requests).sets = before.sets ++ requests.map Request.keys := by
  induction requests generalizing before order prior with
  | nil => simp [endState]
  | cons request rest ih => simp [endState, ih, step, NodeMethodsPush.pushedState,
      HandlerRecord.constructedState, stage, List.append_assoc]

theorem end_functions (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (requests : List Request) :
    (endState before owner methods order prior requests).functions = before.functions := by
  induction requests generalizing before order prior with
  | nil => rfl
  | cons request rest ih => exact ih _ _ _

theorem end_privates (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (requests : List Request) :
    (endState before owner methods order prior requests).privates = before.privates := by
  induction requests generalizing before order prior with
  | nil => rfl
  | cons request rest ih => exact ih _ _ _

theorem end_order (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    (endState before owner methods order prior requests).environment.lookup "order" =
      some (.number (order + requests.length)) := by
  induction requests generalizing before order prior with
  | nil => simpa [endState] using seed.orderBinding
  | cons request rest ih =>
    rw [endState, ih _ _ _ (step_seed before owner stamp methods order prior request seed)]
    congr 2
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

theorem end_objects_length (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (requests : List Request) :
    (endState before owner methods order prior requests).objects.length = before.objects.length + 2 * requests.length := by
  simp [end_objects, storedObjects_length]

theorem end_heap_length (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    (endState before owner methods order prior requests).heap.length = before.heap.length + requests.length := by
  simp [end_heap before owner stamp methods order prior requests seed, keySnapshots]

theorem end_methods (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    (endState before owner methods order prior requests).heap[methods]? =
      some (prior ++ storedRows before.objects.length requests) := by
  have inside := (List.getElem?_eq_some_iff.mp seed.methodsFound).1
  rw [end_heap before owner stamp methods order prior requests seed,
    List.getElem?_append_left (by simpa using inside), List.getElem?_set_self inside]

theorem end_old_object (before : State) (owner methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (reference : Nat) (inside : reference < before.objects.length) :
    (endState before owner methods order prior requests).objects[reference]? = before.objects[reference]? := by
  rw [end_objects, List.getElem?_append_left inside]

theorem end_old_array (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior)
    (reference : Nat) (inside : reference < before.heap.length) (different : reference ≠ methods) :
    (endState before owner methods order prior requests).heap[reference]? = before.heap[reference]? := by
  rw [end_heap before owner stamp methods order prior requests seed,
    List.getElem?_append_left (by simpa using inside), List.getElem?_set_ne (Ne.symm different)]

theorem storedRows_at (objectBase : Nat) (requests : List Request) (index : Nat) (request : Request)
    (atRequest : requests[index]? = some request) :
    (storedRows objectBase requests)[index]? = some (.object (objectBase + 2 * index)) := by
  induction requests generalizing objectBase index with
  | nil => simp at atRequest
  | cons head rest ih =>
    cases index with
    | zero => simp [storedRows]
    | succ index =>
      have restAt : rest[index]? = some request := by simpa using atRequest
      simpa [storedRows, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (objectBase + 2) index restAt

theorem storedObjects_outer_at (objectBase arrayBase : Nat) (order : Int) (requests : List Request)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (storedObjects objectBase arrayBase order requests)[2 * index]? =
      some (HandlerRecord.outerRecord request.method (objectBase + 2 * index + 1)) := by
  induction requests generalizing objectBase arrayBase order index with
  | nil => simp at atRequest
  | cons head rest ih =>
    cases index with
    | zero =>
      have equal : head = request := by simpa using atRequest
      subst head
      simp [storedObjects]
    | succ index =>
      have restAt : rest[index]? = some request := by simpa using atRequest
      simp only [storedObjects]
      rw [show 2 * (index + 1) = (2 * index + 1) + 1 by omega]
      simp only [List.getElem?_cons_succ]
      rw [show objectBase + (2 * index + 1 + 1) + 1 = (objectBase + 2) + 2 * index + 1 by omega]
      exact ih (objectBase + 2) (arrayBase + 1) (order + 1) index restAt

theorem storedObjects_inner_at (objectBase arrayBase : Nat) (order : Int) (requests : List Request)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (storedObjects objectBase arrayBase order requests)[2 * index + 1]? =
      some (HandlerRecord.innerRecord request.handler (arrayBase + index) (order + index + 1)) := by
  induction requests generalizing objectBase arrayBase order index with
  | nil => simp at atRequest
  | cons head rest ih =>
    cases index with
    | zero =>
      have equal : head = request := by simpa using atRequest
      subst head
      simp [storedObjects]
    | succ index =>
      have restAt : rest[index]? = some request := by simpa using atRequest
      simp only [storedObjects]
      rw [show 2 * (index + 1) + 1 = ((2 * index + 1) + 1) + 1 by omega]
      simp only [List.getElem?_cons_succ]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm] using
        ih (objectBase + 2) (arrayBase + 1) (order + 1) index restAt

theorem end_outer (before : State) (owner methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (endState before owner methods order prior requests).objects[before.objects.length + 2 * index]? =
      some (HandlerRecord.outerRecord request.method (before.objects.length + 2 * index + 1)) := by
  rw [end_objects, List.getElem?_append_right (by omega)]
  simpa using storedObjects_outer_at before.objects.length before.heap.length order requests index request atRequest

theorem end_inner (before : State) (owner methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (endState before owner methods order prior requests).objects[before.objects.length + 2 * index + 1]? =
      some (HandlerRecord.innerRecord request.handler (before.heap.length + index) (order + index + 1)) := by
  rw [end_objects, List.getElem?_append_right (by omega)]
  rw [show before.objects.length + 2 * index + 1 - before.objects.length = 2 * index + 1 by omega]
  exact storedObjects_inner_at before.objects.length before.heap.length order requests index request atRequest

theorem end_keys (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value)
    (requests : List Request) (seed : Seed before owner stamp methods order prior)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (endState before owner methods order prior requests).heap[before.heap.length + index]? =
      some (request.keys.map Value.string) := by
  rw [end_heap before owner stamp methods order prior requests seed,
    List.getElem?_append_right (by simp)]
  simp [keySnapshots, atRequest]

end HonoLean.Upstream.RegistrationHistory
