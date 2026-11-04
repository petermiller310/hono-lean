import HonoLean.Upstream.SearchEntry.Row
import HonoLean.Upstream.SearchEntry.MethodChoice
import HonoLean.Upstream.NodeMethodsPush.StorageBridge

namespace HonoLean.Upstream.SearchEntry

open SourceSubset ECMA2025

/-- Explicit activation handoffs, not a parsed combined lexical block or
verified invocation/traversal. Search gets a caller environment; the later
#pushHandlerSets activation receives the actually allocated collector as its
argument, plus caller-supplied node/index/request/helper/import context.
All heaps/tables are retained here; actual intervening source effects remain
an open transport obligation when interpreting this composition natively. -/
def searchActivation (registered : State) (environment : List (String × Value)) : State :=
  {registered with environment}
def pushActivation (registered : State) (searchEnvironment context : List (String × Value)) : State :=
  {collectorState (searchActivation registered searchEnvironment) with
    environment := ("handlerSets", .array registered.heap.length) :: context}
def loadedState (registered : State) (searchEnvironment context : List (String × Value)) (outer : Nat) : State :=
  boundState (pushActivation registered searchEnvironment context) "m" (.object outer)
def entryState (registered : State) (searchEnvironment context : List (String × Value)) (outer inner : Nat) : State :=
  boundState (loadedState registered searchEnvironment context outer) "handlerSet" (.object inner)

structure CallerContext (context : List (String × Value)) (owner index : Nat) (request : JSString) : Prop where
  nodeBinding : context.lookup "node" = some (.object owner)
  indexBinding : context.lookup "i" = some (.number (Int.ofNat index))
  methodBinding : context.lookup "method" = some (.string request)

theorem activation_lookup (registered : State) (searchEnvironment context : List (String × Value))
    (name : String) (different : name ≠ "handlerSets") :
    (pushActivation registered searchEnvironment context).environment.lookup name = context.lookup name := by
  simp [pushActivation, List.lookup_cons, beq_false_of_ne different]

theorem entry_lookup (registered : State) (searchEnvironment context : List (String × Value))
    (outer inner : Nat) (name : String) (notChosen : name ≠ "handlerSet") (notRow : name ≠ "m")
    (notCollector : name ≠ "handlerSets") :
    (entryState registered searchEnvironment context outer inner).environment.lookup name = context.lookup name := by
  rw [entryState, bound_lookup_other _ _ _ _ notChosen, loadedState, bound_lookup_other _ _ _ _ notRow,
    activation_lookup _ _ _ _ notCollector]

theorem registered_row_inputs (before registered : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (searchEnvironment context : List (String × Value))
    (inputs : NodeMethodsPush.Inputs before method handler reference keys order owner stamp methods prior)
    (contract : NodeMethodsPush.PushContract before method handler keys order methods prior
      (.number (Int.ofNat (prior.length + 1))) registered)
    (caller : CallerContext context owner prior.length method) :
    RowInputs (pushActivation registered searchEnvironment context) owner stamp methods prior.length
      (prior ++ [.object before.objects.length]) (.object before.objects.length) := by
  have methodsFound : registered.heap[methods]? = some (prior ++ [.object before.objects.length]) := by
    rw [contract.2]
    exact NodeMethodsPush.pushed_methods_found before method handler keys order methods prior inputs.methodsFound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact caller.nodeBinding
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact caller.indexBinding
  · obtain ⟨object, found⟩ := inputs.ownerFound
    refine ⟨object, ?_⟩
    change registered.objects[owner]? = some object
    rw [contract.2]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · change registered.privates.names.lookup "methods" = some stamp
    rw [contract.2]
    exact inputs.privateName
  · change ∃ fields, registered.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
    rw [contract.2]
    exact inputs.privateSlot
  · change (registered.heap ++ [[]])[methods]? = _
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp methodsFound).1]
    exact methodsFound

/-- Own exact registered-method selection needs no ALL binding/read assumption.
Even special names are own data in the source-created map; arbitrary queries
against an ALL registration require the separate generic ChoiceDomain. -/
theorem registered_direct_read (before registered : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value)
    (searchEnvironment context : List (String × Value))
    (contract : NodeMethodsPush.PushContract before method handler keys order methods prior
      (.number (Int.ofNat (prior.length + 1))) registered) :
    getProperty propertyFuel (loadedState registered searchEnvironment context before.objects.length).objects
      before.objects.length method = .ok (.object (before.objects.length + 1)) := by
  have found : registered.objects[before.objects.length]? =
      some (HandlerRecord.outerRecord method (before.objects.length + 1)) := by
    rw [contract.2]
    exact NodeMethodsPush.pushed_outer_found before method handler keys order methods prior
  exact getProperty_data _ _ 31 _ _ _ true true true found (HandlerRecord.outer_method _ _).1

theorem run_registered_selection (before registered : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (owner methods : Nat) (prior : List Value)
    (searchEnvironment context : List (String × Value))
    (contract : NodeMethodsPush.PushContract before method handler keys order methods prior
      (.number (Int.ofNat (prior.length + 1))) registered)
    (caller : CallerContext context owner prior.length method) :
    execute 32 defaultSplitLimit selectionProgram
      {loadedState registered searchEnvironment context before.objects.length with
        environment := withoutBindings (loadedState registered searchEnvironment context before.objects.length).environment ["handlerSet"]} =
      .ok (.normal (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))) := by
  apply run_choice_direct _ before.objects.length method (.object (before.objects.length + 1))
  · constructor
    · exact bound_lookup_self _ _ _
    · rw [loadedState, bound_lookup_other _ _ _ _ (by decide), activation_lookup _ _ _ _ (by decide)]
      exact caller.methodBinding
  · exact registered_direct_read before registered method handler keys order methods prior searchEnvironment context contract
  · trivial

/-- Only caller/import/helper/read/realm facts remain. Collector allocation,
argument binding, row/handler selection and all record/key shape/uniqueness
facts are absent. Read witnesses describe the post-reset state, not a desired
capture result or a future successful iteration. -/
structure Remainder (before registered : State) (searchEnvironment context : List (String × Value))
    (handler : Value) (order : Int) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot) : Prop where
  helper : ∃ reference environment,
    context.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  rootDispatch : lookupProperty 31 registered.objects 0 HandlerRecord.paramsKey = .ok none ∨
    ∃ value enumerable configurable, lookupProperty 31 registered.objects 0 HandlerRecord.paramsKey =
      .ok (some (.data value true enumerable configurable))
  closed : NodeParamLoop.PrototypeClosed registered.objects registered.objects.length
  parameterBinding : context.lookup "params" = some parameterReceiver
  nodeBinding : context.lookup "nodeParams" = some (.object nodeParams)
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < registered.objects.length
  nodeBound : nodeParams < registered.objects.length
  legalKeys : snapshot.keys.length ≤ 4294967295
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead
      (NodeParamLoop.setupState (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
        (before.objects.length + 1) (HandlerRecord.innerRecord handler before.heap.length (order + 1)) registered.heap.length [])
      key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel
      (NodeParamLoop.setupState (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
        (before.objects.length + 1) (HandlerRecord.innerRecord handler before.heap.length (order + 1)) registered.heap.length []).objects
      nodeParams key = .ok (snapshot.node key)

theorem registered_entry (events : List JSString) (before registered : State) (method : JSString) (handler : Value)
    (reference : Nat) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (searchEnvironment context : List (String × Value)) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : NodeMethodsPush.Inputs before method handler reference snapshot.keys order owner stamp methods prior)
    (contract : NodeMethodsPush.PushContract before method handler snapshot.keys order methods prior
      (.number (Int.ofNat (prior.length + 1))) registered)
    (trace : NodeKeySet.TraceContract events reference before)
    (domain : Remainder before registered searchEnvironment context handler order parameterReceiver nodeParams snapshot) :
    NodeParamLoop.Entry (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
      (before.objects.length + 1) (HandlerRecord.innerRecord handler before.heap.length (order + 1))
      registered.heap.length before.heap.length [] parameterReceiver nodeParams snapshot := by
  have keysFound : registered.heap[before.heap.length]? = some (snapshot.keys.map Value.string) := by
    rw [contract.2]
    exact NodeMethodsPush.pushed_keys_found before method handler snapshot.keys order methods prior
  have objectTransport :
      (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1)).objects[before.objects.length + 1]? =
        (HandlerRecord.constructedState before method handler snapshot.keys order).objects[before.objects.length + 1]? := by
    change registered.objects[_]? = _
    rw [contract.2]
    rfl
  have arrayTransport :
      (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1)).heap[before.heap.length]? =
        (HandlerRecord.constructedState before method handler snapshot.keys order).heap[before.heap.length]? := by
    change (registered.heap ++ [[]])[before.heap.length]? = _
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp keysFound).1, keysFound,
      HandlerRecord.constructed_keys_found]
  have fields : HandlerRecord.ConsumerDomain
      (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
      (before.objects.length + 1) registered.heap.length before.heap.length
      (HandlerRecord.innerRecord handler before.heap.length (order + 1)) [] parameterReceiver nodeParams snapshot := by
    refine {
      handlerBinding := bound_lookup_self _ _ _
      handlersBinding := ?_
      helper := ?_
      rootDispatch := domain.rootDispatch
      closed := domain.closed
      handlersFound := ?_
      arraysSeparate := (Nat.ne_of_lt (List.getElem?_eq_some_iff.mp keysFound).1).symm
      parameterBinding := ?_
      nodeBinding := ?_
      parameterBound := domain.parameterBound
      nodeBound := domain.nodeBound
      legalKeys := domain.legalKeys
      pushCapacity := by decide
      reads := domain.reads}
    · rw [entryState, bound_lookup_other _ _ _ _ (by decide), loadedState, bound_lookup_other _ _ _ _ (by decide)]
      simp [pushActivation]
    · obtain ⟨ref, environment, binding, found, standard⟩ := domain.helper
      refine ⟨ref, environment, ?_, ?_, standard⟩
      · rw [entry_lookup _ _ _ _ _ _ (by decide) (by decide) (by decide)]
        exact binding
      · change registered.functions[ref]? = _
        rw [contract.2]
        exact found
    · change (registered.heap ++ [[]])[registered.heap.length]? = some []
      simp
    · rw [entry_lookup _ _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact domain.parameterBinding
    · rw [entry_lookup _ _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact domain.nodeBinding
  exact HandlerRecord.contract_entry events before (HandlerRecord.constructedState before method handler snapshot.keys order)
    (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
    method handler reference registered.heap.length order [] parameterReceiver nodeParams snapshot inputs.toInputs trace
    ⟨rfl, rfl⟩ objectTransport arrayTransport fields

/-- Noncontiguous source composition with explicit activation/argument handoff.
Actual registration, later collector allocation, private row load and typed
lazy selection feed the capture loop. No handlerSet binding is staged. The
outer method loop/trie traversal/call site and intervening real code remain open. -/
theorem parsed_pipeline_satisfies (events : List JSString) (before registered : State)
    (method : JSString) (handler : Value) (reference : Nat) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (searchEnvironment context : List (String × Value)) (parameterReceiver : Value) (nodeParams : ObjectRef)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : NodeMethodsPush.Inputs before method handler reference snapshot.keys order owner stamp methods prior)
    (registration : (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) =
        some (.ok (.number (Int.ofNat (prior.length + 1)), registered)))
    (trace : NodeKeySet.TraceContract events reference before)
    (caller : CallerContext context owner prior.length method)
    (domain : Remainder before registered searchEnvironment context handler order parameterReceiver nodeParams snapshot) :
    (parseBlock pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {searchActivation registered searchEnvironment with environment := withoutBindings searchEnvironment ["handlerSets"]}) =
        some (.ok (.normal (collectorState (searchActivation registered searchEnvironment)))) ∧
    (parseBlock pinnedRowSource rowBindings ["methods"]).map (fun source => execute 32 defaultSplitLimit source
      {pushActivation registered searchEnvironment context with
        environment := withoutBindings (pushActivation registered searchEnvironment context).environment ["m"]}) =
        some (.ok (.normal (loadedState registered searchEnvironment context before.objects.length))) ∧
    (parseBlock pinnedSelectionSource selectionBindings).map (fun source => execute 32 defaultSplitLimit source
      {loadedState registered searchEnvironment context before.objects.length with
        environment := withoutBindings (loadedState registered searchEnvironment context before.objects.length).environment ["handlerSet"]}) =
        some (.ok (.normal (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1)))) ∧
    ∃ completed,
      (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
        (fun source => runBlock (snapshot.keys.length + 64) source
          (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))) =
            some (.ok (.normal completed)) ∧
      NodeParamLoop.BlockContract (entryState registered searchEnvironment context before.objects.length (before.objects.length + 1))
        completed (before.objects.length + 1) (HandlerRecord.innerRecord handler before.heap.length (order + 1)) registered.heap.length [] snapshot := by
  have contract := (NodeMethodsPush.parsed_source_correct before registered (.number (Int.ofNat (prior.length + 1)))
    method handler reference snapshot.keys order owner stamp methods prior inputs).mp registration
  have rowInputs := registered_row_inputs before registered method handler reference snapshot.keys order owner stamp methods prior
    searchEnvironment context inputs contract caller
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [parses_collector, Option.map_some]
    exact congrArg some (run_collector (searchActivation registered searchEnvironment))
  · rw [parses_row, Option.map_some, run_row _ owner stamp methods prior.length _ _ rowInputs]
    rfl
  · rw [parses_selection, Option.map_some, run_registered_selection before registered method handler snapshot.keys order
      owner methods prior searchEnvironment context contract caller]
  · exact NodeParamLoop.parsed_source_satisfies _ _ _ registered.heap.length before.heap.length [] parameterReceiver nodeParams snapshot
      (registered_entry events before registered method handler reference order owner stamp methods prior searchEnvironment context
        parameterReceiver nodeParams snapshot inputs contract trace domain)

/-- info: 'HonoLean.Upstream.SearchEntry.parsed_pipeline_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_pipeline_satisfies

end HonoLean.Upstream.SearchEntry
