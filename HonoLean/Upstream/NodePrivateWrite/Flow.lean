import HonoLean.Upstream.NodePrivateWrite.Correctness
import HonoLean.Upstream.NodePrivateWrite.Transport
import HonoLean.Upstream.SourceSubset.PrivateWrite
import HonoLean.Upstream.NodePrivateCall.Correctness

namespace HonoLean.Upstream.NodePrivateWrite

open SourceSubset ECMA2025

theorem callable_after_params (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target receiver firstIdentity handle : Nat) (old value : Value)
    (scope : before.privates.names = NodeClass.names firstIdentity)
    (writable : Writable before target (firstIdentity + 4) old)
    (callable : NodePrivateCall.Callable before table closure receiver handle) :
    NodePrivateCall.Callable (writePrivateDataState before target (firstIdentity + 4) value)
      table closure receiver handle := by
  refine ⟨callable.sourceProgram, callable.tableSeparate, callable.handleBound, callable.closureFound, ?_⟩
  by_cases same : receiver = target
  · subst receiver
    obtain ⟨fields, brand, _⟩ := writable.data
    rw [privateGet_write_other_identity before target (firstIdentity + 4) (firstIdentity + 5)
      value "pushHandlerSets" fields ?_ brand (by omega)]
    · exact callable.privateRead
    · simp [scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]
  · rw [privateGet_write_other_owner before target (firstIdentity + 4) receiver value "pushHandlerSets" same]
    exact callable.privateRead

theorem storage_after_params (before : State) (closure : PrivateMethodClosure)
    (target firstIdentity methods collector : Nat) (rows : List Value) (old value : Value)
    (writable : Writable before target (firstIdentity + 4) old)
    (storage : NodePrivateCall.Storage before closure target firstIdentity methods collector rows) :
    NodePrivateCall.Storage (writePrivateDataState before target (firstIdentity + 4) value)
      closure target firstIdentity methods collector rows := by
  obtain ⟨raw, rawFound, _⟩ := writable.data
  obtain ⟨observed, observedFound, methodFound⟩ := storage.privateSlot
  have view : observed = raw.map (fun (identity, element) => (identity, element.value)) := by
    apply Option.some.inj
    rw [← observedFound, PrivateStore.slots_lookup, rawFound]
    rfl
  refine ⟨storage.targetFound, storage.privateName, ?_, storage.methodsFound, storage.separate, storage.legalLength⟩
  refine ⟨(replacePrivateData (firstIdentity + 4) value raw).map (fun (identity, element) => (identity, element.value)), ?_, ?_⟩
  · rw [PrivateStore.slots_lookup]
    change ((replacePrivateOwner target (firstIdentity + 4) value before.privates.elements).lookup target).map _ = _
    rw [replacePrivateOwner_found before.privates.elements target (firstIdentity + 4) value raw rawFound]
    rfl
  · rw [lookup_map_values, replacePrivateData_other raw (firstIdentity + 4) firstIdentity value (by omega)]
    simpa only [view, lookup_map_values] using methodFound

theorem parent_read_after_propagation (before : State) (target parent identity : Nat)
    (old value : Value) (writable : Writable before target identity old)
    (read : privateGet (.object parent) "params" before = .ok value) :
    privateGet (.object parent) "params" (writePrivateDataState before target identity value) = .ok value := by
  by_cases same : parent = target
  · subst parent
    obtain ⟨object, allocated⟩ := writable.allocated
    obtain ⟨fields, brand, field⟩ := writable.data
    exact privateGet_write_same before target identity "params" value old object fields
      writable.scope allocated brand field
  · rw [privateGet_write_other_owner before target identity parent value "params" same]
    exact read

/-- The literal-child propagation and selected four-argument call occur in the
same branch. This theorem composes their entries; reaching the branch and any
intervening wildcard call remain explicit outer-control-flow obligations. -/
theorem parsed_propagation_four_satisfies (before : State) (table : PrivateMethodTable)
    (closure : PrivateMethodClosure) (target parent receiver firstIdentity handle methods collector keyBound : Nat)
    (rows : List Value) (query : JSString) (nodeParams : Nat) (old : Value)
    (records : List MethodsLoopInitial.Record) (initial : List Value)
    (scope : before.privates.names = NodeClass.names firstIdentity)
    (writable : Writable before target (firstIdentity + 4) old)
    (callable : NodePrivateCall.Callable before table closure receiver handle)
    (storage : NodePrivateCall.Storage before closure target firstIdentity methods collector rows)
    (collectorBinding : before.environment.lookup "handlerSets" = some (.array collector))
    (targetBinding : before.environment.lookup "nextNode" = some (.object target))
    (parentBinding : before.environment.lookup "node" = some (.object parent))
    (queryBinding : before.environment.lookup "method" = some (.string query))
    (parentRead : privateGet (.object parent) "params" before = .ok (.object nodeParams))
    (layout : MethodsLoopInitial.Layout (NodePrivateCall.bodyState before closure (.object receiver)
      collector target query nodeParams .undefined) rows query collector keyBound records .undefined nodeParams initial) :
    (parseAssignment pinnedPropagationSource propagationBindings NodePrivateCall.classPrivateNames).map
      (fun assignment => executeAssignment 32 defaultSplitLimit assignment before) =
        some (.ok (.object nodeParams, writePrivateDataState before target (firstIdentity + 4) (.object nodeParams))) ∧
    ∃ after,
      (parsePrivateMethodCall NodePrivateCall.pinnedFourSource NodePrivateCall.fourBindings NodePrivateCall.classPrivateNames).map
        (fun call => runPrivateMethodCall (rows.length + keyBound + 103) defaultSplitLimit table ⟨.object receiver⟩ call
          (writePrivateDataState before target (firstIdentity + 4) (.object nodeParams))) =
            some (.ok (.undefined, after)) ∧
      NodePrivateCall.CallContract (writePrivateDataState before target (firstIdentity + 4) (.object nodeParams))
        (NodePrivateCall.bodyState (writePrivateDataState before target (firstIdentity + 4) (.object nodeParams)) closure
          (.object receiver) collector target query nodeParams .undefined) rows query collector .undefined after := by
  have reads : PropagationReads before target (.object nodeParams) :=
    ⟨targetBinding, .object parent, parentBinding, parentRead⟩
  refine ⟨?_, ?_⟩
  · rw [parses_propagation, Option.map_some, run_propagation before target (firstIdentity + 4) old (.object nodeParams) writable reads]
  · let written := writePrivateDataState before target (firstIdentity + 4) (.object nodeParams)
    have readsAfter : NodePrivateCall.FourReads written collector target query nodeParams :=
      ⟨collectorBinding, targetBinding, queryBinding, .object parent, parentBinding,
        parent_read_after_propagation before target parent (firstIdentity + 4) old (.object nodeParams) writable parentRead⟩
    have layoutAfter : MethodsLoopInitial.Layout
        (NodePrivateCall.bodyState written closure (.object receiver) collector target query nodeParams .undefined)
        rows query collector keyBound records .undefined nodeParams initial :=
      layout_frame layout rfl rfl rfl rfl
    exact (NodePrivateCall.parsed_four_satisfies written table closure receiver handle target firstIdentity
      methods collector keyBound rows query nodeParams records initial
      (callable_after_params before table closure target receiver firstIdentity handle old (.object nodeParams) scope writable callable)
      readsAfter (storage_after_params before closure target firstIdentity methods collector rows old (.object nodeParams) writable storage)
      layoutAfter).2

/-- info: 'HonoLean.Upstream.NodePrivateWrite.parsed_propagation_four_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_propagation_four_satisfies

end HonoLean.Upstream.NodePrivateWrite
