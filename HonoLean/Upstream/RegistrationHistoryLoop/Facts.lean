import HonoLean.Upstream.RegistrationHistory.Contract
import HonoLean.Upstream.RegistrationHistoryLoop.Heap
import HonoLean.Upstream.MethodsLoopInitial.Contract

namespace HonoLean.Upstream.RegistrationHistoryLoop

open SourceSubset ECMA2025 RegistrationHistory

def activation (registered : State) (searchEnvironment context : List (String × Value)) : State :=
  SearchEntry.pushActivation registered searchEnvironment context

def snapshot (request : Request) (parameter node : JSString → Value) : NodeParamLoop.Snapshot :=
  ⟨request.keys, parameter, node⟩

def recordAt (objectBase arrayBase : Nat) (order : Int) (request : Request)
    (parameter node : JSString → Value) : MethodsLoopInitial.Record :=
  ⟨objectBase + 1, HandlerRecord.innerRecord request.handler arrayBase (order + 1), arrayBase,
    snapshot request parameter node⟩

def storedRecords : Nat → Nat → Int → List Request → (JSString → Value) → (JSString → Value) → List MethodsLoopInitial.Record
  | _, _, _, [], _, _ => []
  | objectBase, arrayBase, order, request :: rest, parameter, node =>
    recordAt objectBase arrayBase order request parameter node ::
      storedRecords (objectBase + 2) (arrayBase + 1) (order + 1) rest parameter node

/-- Only old context, reads, bounds and inherited-root conditions remain.
Every method map, handler cell, copied key array and later collector is derived
from the actual source-history storage contract. -/
structure Context (before : State) (requests : List Request) (context : List (String × Value))
    (owner : Nat) (query : JSString) (parameterReceiver : Value) (nodeParams keyBound : Nat)
    (parameter node : JSString → Value) : Prop where
  ownerBinding : context.lookup "node" = some (.object owner)
  queryBinding : context.lookup "method" = some (.string query)
  allBinding : context.lookup "METHOD_NAME_ALL" = some (.string SearchEntry.allKey)
  parameterBinding : context.lookup "params" = some parameterReceiver
  nodeBinding : context.lookup "nodeParams" = some (.object nodeParams)
  helper : ∃ reference environment,
    context.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  rootDispatch : lookupProperty 31 before.objects 0 HandlerRecord.paramsKey = .ok none ∨
    ∃ value enumerable configurable, lookupProperty 31 before.objects 0 HandlerRecord.paramsKey =
      .ok (some (.data value true enumerable configurable))
  nodeBound : nodeParams < before.objects.length
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < before.objects.length
  capacity : requests.length ≤ 4294967295
  keyBounds : ∀ request ∈ requests, request.keys.length ≤ keyBound ∧ request.keys.length ≤ 4294967295
  reads : ∀ request ∈ requests, ∀ key ∈ request.keys,
    NodeParamAssignment.ParameterRead before key parameterReceiver (parameter key) ∧
    getProperty propertyFuel before.objects nodeParams key = .ok (node key)
  queries : ∀ request ∈ requests, MethodsLoopRegistration.QueryDomain before request.method query

theorem records_index {objectBase arrayBase : Nat} {order : Int} {requests : List Request}
    {parameter node : JSString → Value} {candidate : MethodsLoopInitial.Record}
    (member : candidate ∈ storedRecords objectBase arrayBase order requests parameter node) :
    ∃ index request, requests[index]? = some request ∧
      candidate = recordAt (objectBase + 2 * index) (arrayBase + index) (order + index) request parameter node := by
  induction requests generalizing objectBase arrayBase order with
  | nil => cases member
  | cons request rest ih =>
    simp only [storedRecords, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨0, request, rfl, by simp⟩
    · obtain ⟨index, item, atItem, equal⟩ := ih member
      refine ⟨index + 1, item, by simpa using atItem, ?_⟩
      simpa [Nat.mul_add, Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using equal

theorem record_mem (objectBase arrayBase : Nat) (order : Int) (requests : List Request)
    (parameter node : JSString → Value) (index : Nat) (request : Request)
    (atRequest : requests[index]? = some request) :
    recordAt (objectBase + 2 * index) (arrayBase + index) (order + index) request parameter node ∈
      storedRecords objectBase arrayBase order requests parameter node := by
  induction requests generalizing objectBase arrayBase order index with
  | nil => simp at atRequest
  | cons first rest ih =>
    cases index with
    | zero =>
      have same : first = request := by simpa using atRequest
      subst first
      simp [storedRecords]
    | succ index =>
      apply List.mem_cons_of_mem
      simpa [Nat.mul_add, Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (objectBase + 2) (arrayBase + 1) (order + 1) index (by simpa using atRequest)

theorem stored_rows_length (objectBase : Nat) (requests : List Request) :
    (storedRows objectBase requests).length = requests.length := by
  induction requests generalizing objectBase with
  | nil => rfl
  | cons request rest ih => simp [storedRows, ih]

theorem stored_objects_length (objectBase arrayBase : Nat) (order : Int) (requests : List Request) :
    (storedObjects objectBase arrayBase order requests).length = 2 * requests.length := by
  induction requests generalizing objectBase arrayBase order with
  | nil => rfl
  | cons request rest ih => simp [storedObjects, ih]; omega

theorem stored_rows_index (objectBase : Nat) (requests : List Request) (index : Nat)
    (inside : index < requests.length) :
    (storedRows objectBase requests)[index]? = some (.object (objectBase + 2 * index)) := by
  induction requests generalizing objectBase index with
  | nil => simp at inside
  | cons request rest ih =>
    cases index with
    | zero => simp [storedRows]
    | succ index =>
      simpa [storedRows, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (objectBase + 2) index (by simpa using inside)

theorem stored_objects_outer (objectBase arrayBase : Nat) (order : Int) (requests : List Request)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (storedObjects objectBase arrayBase order requests)[2 * index]? =
      some (HandlerRecord.outerRecord request.method (objectBase + 2 * index + 1)) := by
  induction requests generalizing objectBase arrayBase order index with
  | nil => simp at atRequest
  | cons item rest ih =>
    cases index with
    | zero =>
      have equal : item = request := by simpa using atRequest
      subst item
      simp [storedObjects]
    | succ index =>
      rw [show 2 * (index + 1) = (2 * index + 1) + 1 by omega]
      simp only [storedObjects, List.getElem?_cons_succ]
      have run := ih (objectBase + 2) (arrayBase + 1) (order + 1) index (by simpa using atRequest)
      rw [show objectBase + (2 * index + 1 + 1) + 1 = objectBase + 2 + 2 * index + 1 by omega]
      exact run

theorem stored_objects_inner (objectBase arrayBase : Nat) (order : Int) (requests : List Request)
    (index : Nat) (request : Request) (atRequest : requests[index]? = some request) :
    (storedObjects objectBase arrayBase order requests)[2 * index + 1]? =
      some (HandlerRecord.innerRecord request.handler (arrayBase + index) (order + index + 1)) := by
  induction requests generalizing objectBase arrayBase order index with
  | nil => simp at atRequest
  | cons item rest ih =>
    cases index with
    | zero =>
      have equal : item = request := by simpa using atRequest
      subst item
      simp [storedObjects]
    | succ index =>
      rw [show 2 * (index + 1) + 1 = ((2 * index + 1) + 1) + 1 by omega]
      simp only [storedObjects, List.getElem?_cons_succ]
      simpa [Nat.mul_add, Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (objectBase + 2) (arrayBase + 1) (order + 1) index (by simpa using atRequest)

theorem stored_objects_parents (objectBase arrayBase : Nat) (order : Int) (requests : List Request) :
    ∀ object ∈ storedObjects objectBase arrayBase order requests, object.prototype = some 0 := by
  induction requests generalizing objectBase arrayBase order with
  | nil => simp [storedObjects]
  | cons request rest ih =>
    intro object member
    simp only [storedObjects, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · rfl
    · rfl
    · exact ih _ _ _ object member

theorem activation_objects (registered : State) (searchEnvironment context : List (String × Value)) :
    (activation registered searchEnvironment context).objects = registered.objects := rfl

theorem activation_heap (registered : State) (searchEnvironment context : List (String × Value)) :
    (activation registered searchEnvironment context).heap = registered.heap ++ [[]] := rfl

theorem activation_lookup (registered : State) (searchEnvironment context : List (String × Value))
    (name : String) (different : name ≠ "handlerSets") :
    (activation registered searchEnvironment context).environment.lookup name = context.lookup name :=
  SearchEntry.activation_lookup registered searchEnvironment context name different

end HonoLean.Upstream.RegistrationHistoryLoop
