import HonoLean.Upstream.SearchEntry.Bridge

namespace HonoLean.Upstream.SearchEntry.Examples

open SourceSubset ECMA2025
set_option maxRecDepth 65536

private def method : JSString := [71, 69, 84]
private def node : OrdinaryObject := newDataObject {prototype := some 0} idKey (.string [110])
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def owner : OrdinaryObject := {prototype := some 0}
private def prior : List Value := [.object 1]
private def handler : Value := .array 0
private def base : State :=
  {environment := [("curNode", .object 3), ("method", .string method), ("handler", handler), ("order", .number 7)]
   heap := [prior]
   objects := [objectPrototypeProjection [], node, parameter, owner]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   privates := PrivateStore.ofData [("methods", 7)] [(3, [(7, .array 0)])]}
private def events : List JSString := [idKey, idKey]
private def supplied : State :=
  {base with
    environment := [("pattern", .array 2), ("possibleKeys", .set 0)] ++ base.environment
    heap := [prior, [.undefined, .string idKey], [.undefined, .string idKey]]
    sets := [[idKey]]}
private def registered : State := NodeMethodsPush.pushedState supplied method handler [idKey] 7 0 prior
private def record : OrdinaryObject := HandlerRecord.innerRecord handler 3 8

-- The search and #pushHandlerSets activations are explicitly distinct. No
-- collector existed at registration. Argument transport/call-site execution
-- and intervening real search code remain outside this modeled handoff.
private def searchEnv : List (String × Value) := [("searchLocal", .number 55), ("handlerSets", .array 0)]
private def context : List (String × Value) :=
  [("node", .object 3), ("i", .number 1), ("method", .string method),
   ("METHOD_NAME_ALL", .string allKey), ("createNullObject", .function 0),
   ("params", .object 2), ("nodeParams", .object 1), ("Object", .null),
   ("m", .null), ("handlerSet", .boolean false)]
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨[idKey], fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else .undefined⟩
private def consumer : State := entryState registered searchEnv context 4 5

private theorem inputs : NodeMethodsPush.Inputs supplied method handler 0 [idKey] 7 3 7 0 prior :=
  {toInputs := ⟨rfl, rfl, rfl, rfl, rfl, objectPrototypeProjection [], rfl⟩
   ownerBinding := rfl
   ownerFound := ⟨owner, rfl⟩
   privateName := rfl
   privateSlot := ⟨[(7, .array 0)], rfl, rfl⟩
   methodsFound := rfl}
private theorem registration :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source supplied) = some (.ok (.number 2, registered)) := by
  rw [NodeMethodsPush.parses_pinned_source, Option.map_some]
  exact congrArg some (NodeMethodsPush.run_push supplied method handler 0 [idKey] 7 3 7 0 prior inputs)
private theorem trace : NodeKeySet.TraceContract events 0 supplied := by
  obtain ⟨after, execution, _, contract, _⟩ := NodeKeySet.created_trace_satisfies base events
  have observed : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
  have equal : after = supplied := Except.ok.inj (execution.symm.trans observed)
  simpa only [equal, base, List.length_nil] using contract
private theorem caller : CallerContext context 3 1 method := ⟨rfl, rfl, rfl⟩

private theorem remainder : Remainder supplied registered searchEnv context handler 7 (.object 2) 1 snapshot := by
  refine {
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    rootDispatch := Or.inl rfl
    closed := ?_
    parameterBinding := rfl
    nodeBinding := rfl
    parameterBound := ?_
    nodeBound := by change (1 : Nat) < 6; decide
    legalKeys := by decide
    reads := ?_}
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [objectPrototypeProjection [], node, parameter, owner, HandlerRecord.outerRecord method 5, record] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [node, parameter, owner, record, HandlerRecord.innerRecord, HandlerRecord.outerRecord,
        newDataObject, emptyNullObject, objectPrototypeProjection] at prototype <;>
      subst parent <;> change (0 : Nat) < 6 <;> decide
  · intro reference equal
    cases Value.object.inj equal
    change (2 : Nat) < 6
    decide
  · intro key member
    have equal : key = idKey := by simpa [snapshot] using member
    subst key
    exact ⟨.object 2 _ rfl, rfl⟩

-- Positive universal composition witness: duplicate supplied events, actual
-- registration, later source collector, actual row and lazy const selection,
-- then capture loop. No collector/m/handlerSet outcome is an input premise.
example : (parseBlock NodeKeySet.pinnedCreateSource NodeKeySet.bindings).map
    (fun source => execute 32 defaultSplitLimit source
      {base with environment := withoutBindings base.environment ["possibleKeys"]}) =
        some (.ok (.normal (NodeKeySet.createState base))) := by
  rw [NodeKeySet.parses_create, Option.map_some, NodeKeySet.create_execution base (Or.inl rfl)]
example : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
example : ∃ completed,
    (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
      (fun source => runBlock 65 source consumer) = some (.ok (.normal completed)) ∧
    NodeParamLoop.BlockContract consumer completed 5 record 4 [] snapshot := by
  obtain ⟨_, _, _, completed, execution, contract⟩ := parsed_pipeline_satisfies events supplied registered method handler 0 7 3 7 0 prior
    searchEnv context (.object 2) 1 snapshot inputs registration trace caller remainder
  exact ⟨completed, execution, contract⟩

-- Collector4 is fresh AFTER registration's key array3. The old false/null
-- local names are shadowed by the checked declarations, not caller selection.
example : (parseBlock pinnedCollectorSource []).map
    (fun source => execute 32 defaultSplitLimit source
      {searchActivation registered searchEnv with environment := withoutBindings searchEnv ["handlerSets"]}) =
      some (.ok (.normal (collectorState (searchActivation registered searchEnv)))) := by cbv
example : (parseBlock pinnedRowSource rowBindings ["methods"]).map
    (fun source => execute 32 defaultSplitLimit source
      {pushActivation registered searchEnv context with
        environment := withoutBindings (pushActivation registered searchEnv context).environment ["m"]}) =
      some (.ok (.normal (loadedState registered searchEnv context 4))) := by cbv
example : (parseBlock pinnedSelectionSource selectionBindings).map
    (fun source => execute 32 defaultSplitLimit source
      {loadedState registered searchEnv context 4 with
        environment := withoutBindings (loadedState registered searchEnv context 4).environment ["handlerSet"]}) =
      some (.ok (.normal consumer)) := by cbv
example : consumer.environment.lookup "handlerSets" = some (.array 4) ∧ consumer.heap[4]? = some [] ∧
    consumer.environment.lookup "m" = some (.object 4) ∧ consumer.environment.lookup "handlerSet" = some (.object 5) ∧
    consumer.heap[3]? = some [.string idKey] := by cbv

-- ALL comes from the actual retained `as const` initializer. Its import into
-- the callee context is explicit; module linking has not been verified.
example : (parseExpression pinnedAllSource []).map (fun source => evalExpression 32 defaultSplitLimit source {}) =
    some (.ok (.string [65, 76, 76], {})) := parsed_all_value {}
example : AllImportBinding (pushActivation registered searchEnv context) := by cbv

private def falseyValues : List Value := [.undefined, .null, .boolean false, .number 0, .string []]
private def choiceState (direct : Value) : State :=
  {environment := [("m", .object 1), ("method", .string method), ("METHOD_NAME_ALL", .string allKey)]
   heap := [[]]
   objects := [objectPrototypeProjection [],
     newDataObject (newDataObject {prototype := some 0} allKey (.object 2)) method direct, emptyNullObject]}
private def selectedValue (state : State) : Option Value :=
  ((parseBlock pinnedSelectionSource selectionBindings).bind fun source =>
    match execute 32 defaultSplitLimit source {state with environment := withoutBindings state.environment ["handlerSet"]} with
    | .ok (.normal after) => some after
    | _ => none).bind (fun after => after.environment.lookup "handlerSet")

-- The generic conditional fallback theorem also has an inhabited normal
-- domain, with explicit correspondence to the source-derived ALL initializer.
example : ∃ chosen after,
    (parseBlock pinnedSelectionSource selectionBindings).map (fun source => execute 32 defaultSplitLimit source
      {choiceState (.number 0) with environment := withoutBindings (choiceState (.number 0)).environment ["handlerSet"]}) =
        some (.ok (.normal after)) ∧ ChoiceContract (choiceState (.number 0)) after 1 method chosen := by
  exact parsed_choice_from_all_satisfies (choiceState (.number 0)) 1 method (.number 0)
    ⟨rfl, rfl⟩ rfl (fun _ => ⟨rfl, .object 2, rfl⟩)

example : falseyValues.all (fun value => selectedValue (choiceState value) == some (.object 2)) = true := by cbv
example : selectedValue (choiceState (.array 0)) = some (.array 0) := by cbv
example : selectedValue (choiceState (.number 1)) = some (.number 1) := by cbv

-- A truthy direct result does not require even the ALL import binding.
example : selectedValue {choiceState (.object 2) with
    environment := [("m", .object 1), ("method", .string method)]} = some (.object 2) := by cbv
-- An unsupported fallback getter also stays unread on that path.
example : selectedValue {choiceState (.object 2) with
    objects := [objectPrototypeProjection [],
      {own := [(method, .data (.object 2) true true true),
        (allKey, .accessor .unsupported .missing true true)], prototype := some 0}, emptyNullObject]} = some (.object 2) := by cbv

-- Ordinary inherited direct values can win over an own ALL record. Type
-- assertion erasure is not a guarantee that the value has handler-record shape.
private def inherited (request : JSString) : State :=
  {environment := [("m", .object 1), ("method", .string request), ("METHOD_NAME_ALL", .string allKey)]
   objects := [objectPrototypeProjection [], newDataObject {prototype := some 0} allKey (.object 2), emptyNullObject]}
example : selectedValue (inherited constructorKey) = some .objectConstructor := by cbv
example : selectedValue (inherited protoKey) = some (.object 0) := by cbv
example : selectedValue (inherited method) = some (.object 2) := by cbv
-- Equal direct/fallback keys are read twice on a falsy path in the source;
-- pure supported descriptors make those two values equal in this model.
example : selectedValue {choiceState (.number 0) with
    environment := [("m", .object 1), ("method", .string method), ("METHOD_NAME_ALL", .string method)]} = some (.number 0) := by cbv

-- Wrong logical operator is observable, including empty-string/zero cases.
example : (parseBlock "const handlerSet = (m[method] ?? m[METHOD_NAME_ALL]) as HandlerParamsSet<T>" selectionBindings).map
    (fun source => (execute 32 defaultSplitLimit source (choiceState (.number 0))).map
      (fun completion => match completion with
        | .normal state => state.environment.lookup "handlerSet"
        | _ => none)) = some (.ok (some (.number 0))) := by cbv

end HonoLean.Upstream.SearchEntry.Examples
