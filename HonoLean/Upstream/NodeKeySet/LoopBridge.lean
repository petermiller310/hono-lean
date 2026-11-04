import HonoLean.Upstream.NodeKeySet.Correctness
import HonoLean.Upstream.NodeParamLoop.Correctness

namespace HonoLean.Upstream.NodeKeySet

open SourceSubset ECMA2025

/-- Remaining consumer-entry obligations, deliberately without keysFound or
unique. Handler storage, selected-entry reachability, caller transport and the
read/realm domain still need their surrounding-source proofs. -/
structure ConsumerFields (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : NodeParamLoop.Snapshot) : Prop
    extends NodeParamLoop.SetupFacts before handlerSet handler handlerSets priorHandlers where
  possibleKeys : handler.own.lookup NodeParamLoop.possibleKeysKey = some (.data (.array keysArray) true true true)
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

/-- The checked producer's order contract and the actual checked spread result
establish the loop's previously assumed unique-array premise. Transport of that
array to handler storage is explicit; no Node.insert traversal is inferred. -/
theorem producer_snapshot_entry (events : List JSString) (sourceBefore sourceAfter before : State)
    (reference handlerSet : Nat) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (sourceBinding : sourceBefore.environment.lookup "possibleKeys" = some (.set reference))
    (sourceKeys : sourceBefore.sets[reference]? = some snapshot.keys)
    (trace : TraceContract events reference sourceBefore)
    (spread : (parseExpression pinnedSpreadSource bindings).map
      (fun source => evalExpression 32 defaultSplitLimit source sourceBefore) =
        some (.ok (.array keysArray, sourceAfter)))
    (transport : before.heap[keysArray]? = sourceAfter.heap[keysArray]?)
    (fields : ConsumerFields before handlerSet handler handlerSets keysArray priorHandlers
      parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot := by
  obtain ⟨keys, found, ordered⟩ := trace
  have sameKeys : keys = snapshot.keys := Option.some.inj (found.symm.trans sourceKeys)
  subst keys
  have materialized := (parsed_spread_correct sourceBefore sourceAfter (.array keysArray) reference
    snapshot.keys sourceBinding sourceKeys).mp spread
  have address : keysArray = sourceBefore.heap.length := Value.array.inj materialized.1
  have keysFound : before.heap[keysArray]? = some (snapshot.keys.map Value.string) := by
    rw [transport, materialized.2, address]
    simp
  exact {
    toSetupFacts := fields.toSetupFacts
    possibleKeys := fields.possibleKeys
    keysFound := keysFound
    arraysSeparate := fields.arraysSeparate
    parameterBinding := fields.parameterBinding
    nodeBinding := fields.nodeBinding
    parameterBound := fields.parameterBound
    nodeBound := fields.nodeBound
    unique := ordered.1
    legalKeys := fields.legalKeys
    pushCapacity := fields.pushCapacity
    reads := fields.reads}

/-- Composition with the consumer theorem. The successful source spread and
producer contract are prior checked results, never a desired consumer outcome.
This still leaves transport/registration/selection facts in ConsumerFields. -/
theorem producer_snapshot_loop (events : List JSString) (sourceBefore sourceAfter before : State)
    (reference handlerSet : Nat) (handler : OrdinaryObject) (handlerSets keysArray : Nat)
    (priorHandlers : List Value) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (sourceBinding : sourceBefore.environment.lookup "possibleKeys" = some (.set reference))
    (sourceKeys : sourceBefore.sets[reference]? = some snapshot.keys)
    (trace : TraceContract events reference sourceBefore)
    (spread : (parseExpression pinnedSpreadSource bindings).map
      (fun source => evalExpression 32 defaultSplitLimit source sourceBefore) =
        some (.ok (.array keysArray, sourceAfter)))
    (transport : before.heap[keysArray]? = sourceAfter.heap[keysArray]?)
    (fields : ConsumerFields before handlerSet handler handlerSets keysArray priorHandlers
      parameterReceiver nodeParams snapshot) :
    ∃ after,
      (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
        (fun source => runBlock (snapshot.keys.length + 64) source before) = some (.ok (.normal after)) ∧
      NodeParamLoop.BlockContract before after handlerSet handler handlerSets priorHandlers snapshot :=
  NodeParamLoop.parsed_source_satisfies before handlerSet handler handlerSets keysArray priorHandlers
    parameterReceiver nodeParams snapshot
    (producer_snapshot_entry events sourceBefore sourceAfter before reference handlerSet handler handlerSets keysArray
      priorHandlers parameterReceiver nodeParams snapshot sourceBinding sourceKeys trace spread transport fields)

/-- info: 'HonoLean.Upstream.NodeKeySet.producer_snapshot_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms producer_snapshot_loop

end HonoLean.Upstream.NodeKeySet
