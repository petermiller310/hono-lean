import HonoLean.Upstream.NodeMethodsPush.Correctness
import HonoLean.Upstream.HandlerRecord.LoopBridge

namespace HonoLean.Upstream.NodeMethodsPush

open SourceSubset ECMA2025

/-- Explicit caller-side choice of the newly stored handler. No source method
selection/fallback expression is claimed; no heap cell is manufactured here. -/
def selectedState (after : State) (handlerSet : Nat) : State :=
  {after with environment := ("handlerSet", .object handlerSet) :: after.environment}

/-- Only non-storage consumer facts remain. The selected binding, record/key
cells, key-field/params shape, unique list, old handler-array contents and its
separation from fresh keys are derived, not assumed here. This immediate
composition requires the collector to be allocated before registration push.
Actual Node.search allocates its collector later; that allocation/lifecycle
frame and method selection still need their own source connection. -/
structure ConsumerRemainder (before after : State) (handler : Value) (order : Int)
    (methods handlerSets : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : NodeParamLoop.Snapshot) : Prop where
  handlersBinding : before.environment.lookup "handlerSets" = some (.array handlerSets)
  handlersOld : before.heap[handlerSets]? = some priorHandlers
  handlersSeparate : methods ≠ handlerSets
  helper : ∃ reference environment,
    before.environment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  rootDispatch : lookupProperty 31 after.objects 0 HandlerRecord.paramsKey = .ok none ∨
    ∃ value enumerable configurable, lookupProperty 31 after.objects 0 HandlerRecord.paramsKey =
      .ok (some (.data value true enumerable configurable))
  closed : NodeParamLoop.PrototypeClosed after.objects after.objects.length
  parameterBinding : before.environment.lookup "params" = some parameterReceiver
  nodeBinding : before.environment.lookup "nodeParams" = some (.object nodeParams)
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < before.objects.length
  nodeBound : nodeParams < before.objects.length
  legalKeys : snapshot.keys.length ≤ 4294967295
  pushCapacity : priorHandlers.length < 4294967295
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead
        (NodeParamLoop.setupState (selectedState after (before.objects.length + 1)) (before.objects.length + 1)
          (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets priorHandlers)
        key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel
        (NodeParamLoop.setupState (selectedState after (before.objects.length + 1)) (before.objects.length + 1)
          (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets priorHandlers).objects
        nodeParams key = .ok (snapshot.node key)

theorem selected_lookup_other (after : State) (handlerSet : Nat) (name : String)
    (different : name ≠ "handlerSet") :
    (selectedState after handlerSet).environment.lookup name = after.environment.lookup name := by
  simp [selectedState, List.lookup_cons, beq_false_of_ne different]

theorem contract_entry (events : List JSString) (before after : State)
    (method : JSString) (handler : Value) (reference methods handlerSets : Nat) (order : Int)
    (prior : List Value) (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (recordInputs : HandlerRecord.Inputs before method handler reference snapshot.keys order)
    (trace : NodeKeySet.TraceContract events reference before)
    (contract : PushContract before method handler snapshot.keys order methods prior
      (.number (Int.ofNat (prior.length + 1))) after)
    (domain : ConsumerRemainder before after handler order methods handlerSets priorHandlers parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry (selectedState after (before.objects.length + 1)) (before.objects.length + 1)
      (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets before.heap.length
      priorHandlers parameterReceiver nodeParams snapshot := by
  have otherBinding (name : String) (notHandler : name ≠ "handlerSet") (notOrder : name ≠ "order") :
      (selectedState after (before.objects.length + 1)).environment.lookup name = before.environment.lookup name := by
    rw [selected_lookup_other _ _ _ notHandler, contract.2]
    exact HandlerRecord.replaceOrder_other before.environment (order + 1) name notOrder
  have objectTransport :
      (selectedState after (before.objects.length + 1)).objects[before.objects.length + 1]? =
        (HandlerRecord.constructedState before method handler snapshot.keys order).objects[before.objects.length + 1]? := by
    rw [contract.2]
    rfl
  have arrayTransport :
      (selectedState after (before.objects.length + 1)).heap[before.heap.length]? =
        (HandlerRecord.constructedState before method handler snapshot.keys order).heap[before.heap.length]? := by
    rw [contract.2]
    exact (pushed_keys_found before method handler snapshot.keys order methods prior).trans
      (HandlerRecord.constructed_keys_found before method handler snapshot.keys order).symm
  have fields : HandlerRecord.ConsumerDomain (selectedState after (before.objects.length + 1))
      (before.objects.length + 1) handlerSets before.heap.length
      (HandlerRecord.innerRecord handler before.heap.length (order + 1)) priorHandlers parameterReceiver nodeParams snapshot := by
    refine {
      handlerBinding := by simp [selectedState]
      handlersBinding := ?_
      helper := ?_
      rootDispatch := domain.rootDispatch
      closed := domain.closed
      handlersFound := ?_
      arraysSeparate := Nat.ne_of_lt (List.getElem?_eq_some_iff.mp domain.handlersOld).1
      parameterBinding := ?_
      nodeBinding := ?_
      parameterBound := ?_
      nodeBound := ?_
      legalKeys := domain.legalKeys
      pushCapacity := domain.pushCapacity
      reads := domain.reads}
    · rw [otherBinding "handlerSets" (by decide) (by decide)]
      exact domain.handlersBinding
    · obtain ⟨ref, environment, binding, found, standard⟩ := domain.helper
      refine ⟨ref, environment, ?_, ?_, ?_⟩
      · rw [otherBinding "createNullObject" (by decide) (by decide)]
        exact binding
      · rw [contract.2]
        exact found
      · exact standard
    · rw [show (selectedState after (before.objects.length + 1)).heap = after.heap from rfl, contract.2,
        pushed_other_array before method handler snapshot.keys order methods prior handlerSets
          (List.getElem?_eq_some_iff.mp domain.handlersOld).1 domain.handlersSeparate]
      exact domain.handlersOld
    · rw [otherBinding "params" (by decide) (by decide)]
      exact domain.parameterBinding
    · rw [otherBinding "nodeParams" (by decide) (by decide)]
      exact domain.nodeBinding
    · intro ref equal
      have bound := domain.parameterBound ref equal
      rw [show (selectedState after (before.objects.length + 1)).objects = after.objects from rfl, contract.2]
      change ref < (before.objects ++ [_, _]).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    ·
      rw [show (selectedState after (before.objects.length + 1)).objects = after.objects from rfl, contract.2]
      change nodeParams < (before.objects ++ [_, _]).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      exact Nat.lt_trans domain.nodeBound (by omega)
  exact HandlerRecord.contract_entry events before (HandlerRecord.constructedState before method handler snapshot.keys order)
    (selectedState after (before.objects.length + 1)) method handler reference handlerSets order priorHandlers
    parameterReceiver nodeParams snapshot recordInputs trace ⟨rfl, rfl⟩ objectTransport arrayTransport fields

/-- Storage facts are consequences of actual parsed execution, including the
appended-map index, own method-to-handler edge and copied key cell. -/
theorem parsed_source_storage (before after : State) (returned : Value)
    (method : JSString) (handler : Value) (reference : Nat) (keys : List JSString) (order : Int)
    (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior)
    (execution : (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) = some (.ok (returned, after))) :
    (after.heap[methods]?).bind (fun elements => elements[prior.length]?) = some (.object before.objects.length) ∧
    (after.objects[before.objects.length]?).bind (fun object => object.own.lookup method) =
      some (.data (.object (before.objects.length + 1)) true true true) ∧
    after.objects[before.objects.length + 1]? =
      some (HandlerRecord.innerRecord handler before.heap.length (order + 1)) ∧
    after.heap[before.heap.length]? = some (keys.map Value.string) := by
  have contract := (parsed_source_correct before after returned method handler reference keys order owner stamp methods prior inputs).mp execution
  rw [contract.2]
  exact ⟨(pushed_stored_map before method handler keys order methods prior inputs.methodsFound).1,
    pushed_method_handler before method handler keys order methods prior,
    pushed_inner_found before method handler keys order methods prior,
    pushed_keys_found before method handler keys order methods prior⟩

theorem parsed_source_entry (events : List JSString) (before after : State)
    (method : JSString) (handler : Value) (reference : Nat) (order : Int)
    (owner stamp methods handlerSets : Nat) (prior priorHandlers : List Value)
    (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : NodeParamLoop.Snapshot)
    (inputs : Inputs before method handler reference snapshot.keys order owner stamp methods prior)
    (trace : NodeKeySet.TraceContract events reference before)
    (execution : (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) =
        some (.ok (.number (Int.ofNat (prior.length + 1)), after)))
    (domain : ConsumerRemainder before after handler order methods handlerSets priorHandlers parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry (selectedState after (before.objects.length + 1)) (before.objects.length + 1)
      (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets before.heap.length
      priorHandlers parameterReceiver nodeParams snapshot :=
  contract_entry events before after method handler reference methods handlerSets order prior priorHandlers
    parameterReceiver nodeParams snapshot inputs.toInputs trace
    ((parsed_source_correct before after (.number (Int.ofNat (prior.length + 1))) method handler reference
      snapshot.keys order owner stamp methods prior inputs).mp execution) domain

/-- From supplied duplicate-capable events through actual private push/storage
to the checked consumer. selectedState explicitly stages the caller's choice;
the collector is preallocated, and actual later search allocation, method/ALL
selection and traversal remain unparsed. -/
theorem parsed_source_loop (events : List JSString) (before after : State)
    (method : JSString) (handler : Value) (reference : Nat) (order : Int)
    (owner stamp methods handlerSets : Nat) (prior priorHandlers : List Value)
    (parameterReceiver : Value) (nodeParams : ObjectRef) (snapshot : NodeParamLoop.Snapshot)
    (inputs : Inputs before method handler reference snapshot.keys order owner stamp methods prior)
    (trace : NodeKeySet.TraceContract events reference before)
    (execution : (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) =
        some (.ok (.number (Int.ofNat (prior.length + 1)), after)))
    (domain : ConsumerRemainder before after handler order methods handlerSets priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ completed,
      (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
        (fun source => runBlock (snapshot.keys.length + 64) source (selectedState after (before.objects.length + 1))) =
          some (.ok (.normal completed)) ∧
      NodeParamLoop.BlockContract (selectedState after (before.objects.length + 1)) completed (before.objects.length + 1)
        (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets priorHandlers snapshot :=
  NodeParamLoop.parsed_source_satisfies (selectedState after (before.objects.length + 1)) (before.objects.length + 1)
    (HandlerRecord.innerRecord handler before.heap.length (order + 1)) handlerSets before.heap.length priorHandlers
    parameterReceiver nodeParams snapshot
    (parsed_source_entry events before after method handler reference order owner stamp methods handlerSets
      prior priorHandlers parameterReceiver nodeParams snapshot inputs trace execution domain)

/-- info: 'HonoLean.Upstream.NodeMethodsPush.parsed_source_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_loop

end HonoLean.Upstream.NodeMethodsPush
