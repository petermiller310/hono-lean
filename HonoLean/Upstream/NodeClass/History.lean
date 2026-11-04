import HonoLean.Upstream.NodeClass.Correctness
import HonoLean.Upstream.NodePrivateWrite.Transport
import HonoLean.Upstream.NodePrivateCall.Correctness
import HonoLean.Upstream.RegistrationHistoryLoop.Correctness

namespace HonoLean.Upstream.NodeClass

open SourceSubset ECMA2025 RegistrationHistory

def callEntry (registered : State) (caller : List (String × Value)) : State :=
  SearchEntry.collectorState (SearchEntry.searchActivation registered caller)

def methodContext (methodClosure : PrivateMethodClosure) (owner : Nat) (query : JSString)
    (nodeParams : Nat) (parameterReceiver : Value) : List (String × Value) :=
  [("node", .object owner), ("method", .string query), ("nodeParams", .object nodeParams),
    ("params", parameterReceiver)] ++ methodClosure.environment

theorem callable_after_history (before : State) (table : PrivateMethodTable) (methodClosure : PrivateMethodClosure)
    (owner receiver handle methods : Nat) (order : Int) (prior : List Value) (requests : List Request)
    (receiverFound : ∃ object, before.objects[receiver]? = some object)
    (callable : NodePrivateCall.Callable before table methodClosure receiver handle) :
    NodePrivateCall.Callable (endState before owner methods order prior requests)
      table methodClosure receiver handle := by
  obtain ⟨object, ownerFound⟩ := receiverFound
  have inside := (List.getElem?_eq_some_iff.mp ownerFound).1
  refine ⟨callable.sourceProgram, ?_, callable.handleBound, callable.closureFound, ?_⟩
  · simpa [end_functions] using callable.tableSeparate
  · simpa only [privateGet, end_privates, end_old_object before owner methods order prior requests receiver inside]
      using callable.privateRead

theorem callable_at_entry (registered : State) (caller : List (String × Value))
    (table : PrivateMethodTable) (methodClosure : PrivateMethodClosure) (owner handle : Nat)
    (callable : NodePrivateCall.Callable registered table methodClosure owner handle) :
    NodePrivateCall.Callable (callEntry registered caller) table methodClosure owner handle := by
  refine ⟨callable.sourceProgram, callable.tableSeparate, callable.handleBound, callable.closureFound, ?_⟩
  simpa only [callEntry, SearchEntry.collectorState, SearchEntry.searchActivation, SearchEntry.boundState,
    privateGet] using callable.privateRead

theorem body_entry (registered : State) (caller : List (String × Value)) (methodClosure : PrivateMethodClosure)
    (owner receiver : Nat) (query : JSString) (nodeParams : Nat) (parameterReceiver : Value)
    (scope : methodClosure.privateNames = registered.privates.names) :
    NodePrivateCall.bodyState (callEntry registered caller) methodClosure (.object receiver) registered.heap.length owner query
      nodeParams parameterReceiver =
    {RegistrationHistoryLoop.activation registered caller
      (methodContext methodClosure owner query nodeParams parameterReceiver) with thisValue := .object receiver} := by
  cases registered
  simp [NodePrivateCall.bodyState, callEntry, methodContext, RegistrationHistoryLoop.activation,
    SearchEntry.pushActivation, SearchEntry.collectorState, SearchEntry.searchActivation,
    SearchEntry.boundState, scope]

theorem entry_storage (before : State) (owner stamp methods : Nat) (order : Int) (requests : List Request)
    (caller : List (String × Value)) (methodClosure : PrivateMethodClosure)
    (seed : Seed before owner stamp methods order [])
    (privateName : methodClosure.privateNames.lookup "methods" = some stamp)
    (capacity : requests.length ≤ 4294967295) :
    NodePrivateCall.Storage (callEntry (endState before owner methods order [] requests) caller) methodClosure
      owner stamp methods (endState before owner methods order [] requests).heap.length
      (storedRows before.objects.length requests) := by
  let registered := endState before owner methods order [] requests
  have contract := history_contract before owner stamp methods order [] requests seed
  obtain ⟨object, found⟩ := seed.ownerFound
  have oldBound := (List.getElem?_eq_some_iff.mp found).1
  have methodsInside := (List.getElem?_eq_some_iff.mp seed.methodsFound).1
  refine ⟨⟨object, ?_⟩, privateName, ?_, ?_, ?_, ?_⟩
  · exact (end_old_object before owner methods order [] requests owner oldBound).trans found
  · change ∃ fields, registered.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
    simpa [registered, end_privates] using seed.privateSlot
  · change (registered.heap ++ [[]])[methods]? = some (storedRows before.objects.length requests)
    have methodBound : methods < registered.heap.length := by
      change _ < (endState before owner methods order [] requests).heap.length
      rw [end_heap_length before owner stamp methods order [] requests seed]
      omega
    rw [List.getElem?_append_left methodBound]
    simpa [registered] using end_methods before owner stamp methods order [] requests seed
  · change (endState before owner methods order [] requests).heap.length ≠ methods
    rw [end_heap_length before owner stamp methods order [] requests seed]
    omega
  · simpa [storedRows_length] using capacity

/-- Actual source push histories preserve the installed handle, then the real
collector declaration and selected five-argument call execute. The old Context
contains only caller/import/realm/read conditions; the source history derives
records, snapshots, protected Layout and all subsequent capture-loop readiness. -/
theorem parsed_history_five_satisfies (before : State) (table : PrivateMethodTable)
    (methodClosure : PrivateMethodClosure) (owner receiver handle stamp methods keyBound : Nat)
    (order : Int) (requests : List Request) (caller : List (String × Value))
    (query : JSString) (parameterReceiver : Value) (nodeParams : Nat) (parameter node : JSString → Value)
    (seed : Seed before owner stamp methods order [])
    (callable : NodePrivateCall.Callable before table methodClosure receiver handle)
    (receiverFound : ∃ object, before.objects[receiver]? = some object)
    (scope : methodClosure.privateNames = before.privates.names)
    (reads : NodePrivateCall.FiveReads (callEntry (endState before owner methods order [] requests) caller)
      (endState before owner methods order [] requests).heap.length owner query nodeParams parameterReceiver)
    (domain : RegistrationHistoryLoop.Context before requests
      (methodContext methodClosure owner query nodeParams parameterReceiver)
      owner query parameterReceiver nodeParams keyBound parameter node) :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source owner requests before) =
        some (.ok (endState before owner methods order [] requests)) ∧
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation (endState before owner methods order [] requests) caller with
        environment := withoutBindings caller ["handlerSets"]}) =
          some (.ok (.normal (callEntry (endState before owner methods order [] requests) caller))) ∧
    ∃ after,
      (parsePrivateMethodCall NodePrivateCall.pinnedFiveSource NodePrivateCall.fiveBindings
        NodePrivateCall.classPrivateNames).map
        (fun call => runPrivateMethodCall (requests.length + keyBound + 103) defaultSplitLimit table
          ⟨.object receiver⟩ call (callEntry (endState before owner methods order [] requests) caller)) =
            some (.ok (.undefined, after)) ∧
      NodePrivateCall.CallContract (callEntry (endState before owner methods order [] requests) caller)
        (NodePrivateCall.bodyState (callEntry (endState before owner methods order [] requests) caller)
          methodClosure (.object receiver) (endState before owner methods order [] requests).heap.length owner query nodeParams parameterReceiver)
        (storedRows before.objects.length requests) query
        (endState before owner methods order [] requests).heap.length .undefined after := by
  let registered := endState before owner methods order [] requests
  have stored := history_contract before owner stamp methods order [] requests seed
  have scopeAfter : methodClosure.privateNames = registered.privates.names := by
    simpa [registered, end_privates] using scope
  have layout := RegistrationHistoryLoop.parsed_history_layout before owner stamp methods order requests
    caller (methodContext methodClosure owner query nodeParams parameterReceiver) query parameterReceiver
    nodeParams keyBound parameter node seed domain
  have bodyLayout := NodePrivateWrite.layout_with_this layout (.object receiver)
  rw [← body_entry registered caller methodClosure owner receiver query nodeParams parameterReceiver scopeAfter] at bodyLayout
  have callableNow := callable_at_entry registered caller table methodClosure receiver handle
    (callable_after_history before table methodClosure owner receiver handle methods order [] requests receiverFound callable)
  have privateName : methodClosure.privateNames.lookup "methods" = some stamp := by rw [scope]; exact seed.privateName
  have result := NodePrivateCall.parsed_five_satisfies (callEntry registered caller) table methodClosure
    receiver handle owner stamp methods registered.heap.length keyBound (storedRows before.objects.length requests)
    query nodeParams parameterReceiver
    (RegistrationHistoryLoop.storedRecords before.objects.length before.heap.length order requests parameter node) []
    callableNow reads (entry_storage before owner stamp methods order requests caller methodClosure seed privateName domain.capacity) bodyLayout
  refine ⟨run_parsed_history before owner stamp methods order [] requests seed,
    RegistrationHistoryLoop.collector_execution registered caller, ?_⟩
  simpa [storedRows_length] using result.2

/-- info: 'HonoLean.Upstream.NodeClass.parsed_history_five_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_history_five_satisfies

end HonoLean.Upstream.NodeClass
