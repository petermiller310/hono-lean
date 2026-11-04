import HonoLean.Upstream.HandlerRecord.Correctness
import HonoLean.Upstream.NodeKeySet.Correctness
import HonoLean.Upstream.NodeParamLoop.Correctness

namespace HonoLean.Upstream.HandlerRecord

open SourceSubset ECMA2025

/-- Remaining selected-consumer domain. It contains no handler object/cell,
possibleKeys descriptor, own-params absence/resettable fact, unique-key proof
or keys-array contents. Those will come from executed construction. The root
dispatch condition is essential: an absent own params field still uses Set. -/
structure ConsumerDomain (before : State) (handlerSet handlerSets keysArray : Nat)
    (handler : OrdinaryObject) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : NodeParamLoop.Snapshot) : Prop where
  handlerBinding : before.environment.lookup "handlerSet" = some (.object handlerSet)
  handlersBinding : before.environment.lookup "handlerSets" = some (.array handlerSets)
  helper : ∃ reference environment,
    before.environment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  rootDispatch : lookupProperty 31 before.objects 0 paramsKey = .ok none ∨
    ∃ value enumerable configurable, lookupProperty 31 before.objects 0 paramsKey =
      .ok (some (.data value true enumerable configurable))
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  handlersFound : before.heap[handlerSets]? = some priorHandlers
  arraysSeparate : handlerSets ≠ keysArray
  parameterBinding : before.environment.lookup "params" = some parameterReceiver
  nodeBinding : before.environment.lookup "nodeParams" = some (.object nodeParams)
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < before.objects.length
  nodeBound : nodeParams < before.objects.length
  legalKeys : snapshot.keys.length ≤ 4294967295
  pushCapacity : priorHandlers.length < 4294967295
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead (NodeParamLoop.setupState before handlerSet handler handlerSets priorHandlers)
        key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel (NodeParamLoop.setupState before handlerSet handler handlerSets priorHandlers).objects
        nodeParams key = .ok (snapshot.node key)

/-- Structural composition helper. The public parsed-source bridge below
derives this contract; it does not ask callers to fabricate a handler record. -/
theorem contract_entry (events : List JSString) (sourceBefore sourceAfter before : State)
    (method : JSString) (handler : Value) (reference handlerSets : Nat) (order : Int)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : Inputs sourceBefore method handler reference snapshot.keys order)
    (trace : NodeKeySet.TraceContract events reference sourceBefore)
    (contract : RecordContract sourceBefore method handler snapshot.keys order
      (.object sourceBefore.objects.length) sourceAfter)
    (objectTransport : before.objects[sourceBefore.objects.length + 1]? =
      sourceAfter.objects[sourceBefore.objects.length + 1]?)
    (arrayTransport : before.heap[sourceBefore.heap.length]? = sourceAfter.heap[sourceBefore.heap.length]?)
    (domain : ConsumerDomain before (sourceBefore.objects.length + 1) handlerSets sourceBefore.heap.length
      (innerRecord handler sourceBefore.heap.length (order + 1)) priorHandlers parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry before (sourceBefore.objects.length + 1)
      (innerRecord handler sourceBefore.heap.length (order + 1)) handlerSets sourceBefore.heap.length
      priorHandlers parameterReceiver nodeParams snapshot := by
  have handlerFound : before.objects[sourceBefore.objects.length + 1]? =
      some (innerRecord handler sourceBefore.heap.length (order + 1)) := by
    rw [objectTransport, contract.2]
    exact constructed_inner_found sourceBefore method handler snapshot.keys order
  have keysFound : before.heap[sourceBefore.heap.length]? = some (snapshot.keys.map Value.string) := by
    rw [arrayTransport, contract.2]
    exact constructed_keys_found sourceBefore method handler snapshot.keys order
  obtain ⟨keys, found, ordered⟩ := trace
  have sameKeys : keys = snapshot.keys := Option.some.inj (found.symm.trans inputs.setFound)
  subst keys
  have lookup : lookupProperty propertyFuel before.objects (sourceBefore.objects.length + 1)
      NodeParamAssignment.paramsKey = lookupProperty 31 before.objects 0 paramsKey := by
    rw [show propertyFuel = 32 from rfl, lookupProperty, handlerFound]
    rfl
  have resettable : NodeParamLoop.Resettable before.objects (sourceBefore.objects.length + 1)
      (innerRecord handler sourceBefore.heap.length (order + 1)) := by
    constructor
    · rw [lookup]
      exact domain.rootDispatch
    · exact Or.inl ⟨(inner_fields handler sourceBefore.heap.length (order + 1)).2.2.2, rfl⟩
  exact {
    toSetupFacts := ⟨domain.handlerBinding, domain.handlersBinding, domain.helper, handlerFound,
      resettable, domain.closed, domain.handlersFound⟩
    possibleKeys := (inner_fields handler sourceBefore.heap.length (order + 1)).2.1
    keysFound := keysFound
    arraysSeparate := domain.arraysSeparate
    parameterBinding := domain.parameterBinding
    nodeBinding := domain.nodeBinding
    parameterBound := domain.parameterBound
    nodeBound := domain.nodeBound
    unique := ordered.1
    legalKeys := domain.legalKeys
    pushCapacity := domain.pushCapacity
    reads := domain.reads}

/-- The actual parsed object argument creates the record used by this Entry.
Only explicit transport of its actual cells and the remaining consumer domain
are external; handler/key fields and resettable own shape are derived. -/
theorem parsed_source_entry (events : List JSString) (sourceBefore sourceAfter before : State)
    (method : JSString) (handler : Value) (reference handlerSets : Nat) (order : Int)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : Inputs sourceBefore method handler reference snapshot.keys order)
    (trace : NodeKeySet.TraceContract events reference sourceBefore)
    (execution : (parseExpression pinnedSource bindings).map
      (fun source => evalExpression 32 defaultSplitLimit source sourceBefore) =
        some (.ok (.object sourceBefore.objects.length, sourceAfter)))
    (objectTransport : before.objects[sourceBefore.objects.length + 1]? =
      sourceAfter.objects[sourceBefore.objects.length + 1]?)
    (arrayTransport : before.heap[sourceBefore.heap.length]? = sourceAfter.heap[sourceBefore.heap.length]?)
    (domain : ConsumerDomain before (sourceBefore.objects.length + 1) handlerSets sourceBefore.heap.length
      (innerRecord handler sourceBefore.heap.length (order + 1)) priorHandlers parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry before (sourceBefore.objects.length + 1)
      (innerRecord handler sourceBefore.heap.length (order + 1)) handlerSets sourceBefore.heap.length
      priorHandlers parameterReceiver nodeParams snapshot :=
  contract_entry events sourceBefore sourceAfter before method handler reference handlerSets order priorHandlers
    parameterReceiver nodeParams snapshot inputs trace
    ((parsed_source_correct sourceBefore sourceAfter (.object sourceBefore.objects.length) method handler reference
      snapshot.keys order inputs).mp execution) objectTransport arrayTransport domain

/-- Producer-to-record-to-consumer composition. Supplied string events and
caller selection/transport remain explicit. This is not a proof of the private
push, method selection, full insert or search traversal. -/
theorem parsed_source_loop (events : List JSString) (sourceBefore sourceAfter before : State)
    (method : JSString) (handler : Value) (reference handlerSets : Nat) (order : Int)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : Inputs sourceBefore method handler reference snapshot.keys order)
    (trace : NodeKeySet.TraceContract events reference sourceBefore)
    (execution : (parseExpression pinnedSource bindings).map
      (fun source => evalExpression 32 defaultSplitLimit source sourceBefore) =
        some (.ok (.object sourceBefore.objects.length, sourceAfter)))
    (objectTransport : before.objects[sourceBefore.objects.length + 1]? =
      sourceAfter.objects[sourceBefore.objects.length + 1]?)
    (arrayTransport : before.heap[sourceBefore.heap.length]? = sourceAfter.heap[sourceBefore.heap.length]?)
    (domain : ConsumerDomain before (sourceBefore.objects.length + 1) handlerSets sourceBefore.heap.length
      (innerRecord handler sourceBefore.heap.length (order + 1)) priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ after,
      (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
        (fun source => runBlock (snapshot.keys.length + 64) source before) = some (.ok (.normal after)) ∧
      NodeParamLoop.BlockContract before after (sourceBefore.objects.length + 1)
        (innerRecord handler sourceBefore.heap.length (order + 1)) handlerSets priorHandlers snapshot :=
  NodeParamLoop.parsed_source_satisfies before (sourceBefore.objects.length + 1)
    (innerRecord handler sourceBefore.heap.length (order + 1)) handlerSets sourceBefore.heap.length
    priorHandlers parameterReceiver nodeParams snapshot
    (parsed_source_entry events sourceBefore sourceAfter before method handler reference handlerSets order
      priorHandlers parameterReceiver nodeParams snapshot inputs trace execution objectTransport arrayTransport domain)

/-- info: 'HonoLean.Upstream.HandlerRecord.parsed_source_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_loop

end HonoLean.Upstream.HandlerRecord
