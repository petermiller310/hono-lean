import HonoLean.Upstream.HandlerRecord.LoopBridge

namespace HonoLean.Upstream.HandlerRecord.Examples

open SourceSubset ECMA2025

set_option maxRecDepth 65536

private def node : OrdinaryObject := newDataObject {prototype := some 0} idKey (.string [110])
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def handlerValue : Value := .string [104]
private def method : JSString := [71, 69, 84]
private def base : State :=
  {environment := [("method", .string method), ("handler", handlerValue), ("order", .number 7),
      ("handlerSets", .array 0), ("params", .object 2), ("nodeParams", .object 1),
      ("createNullObject", .function 0)]
   heap := [[]]
   objects := [objectPrototypeProjection [], node, parameter]
   functions := [⟨CreateNullObject.createProgram, []⟩]}

private def events : List JSString := [idKey, idKey]
private def supplied : State :=
  {base with
    environment := [("pattern", .array 2), ("possibleKeys", .set 0)] ++ base.environment
    heap := [[], [.undefined, .string idKey], [.undefined, .string idKey]]
    sets := [[idKey]]}
private def recordState : State := constructedState supplied method handlerValue [idKey] 7
private def record : OrdinaryObject := innerRecord handlerValue 3 8

/-- Only caller selection/binding is staged here. All handler properties and
the keys array are retained from actual object-expression construction. -/
private def consumer : State :=
  {recordState with environment := ("handlerSet", .object 4) :: recordState.environment}
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨[idKey], fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else .undefined⟩

private theorem supplied_contract : NodeKeySet.TraceContract events 0 supplied := by
  obtain ⟨after, execution, _, contract, _⟩ := NodeKeySet.created_trace_satisfies base events
  have observed : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
  have equal : after = supplied := Except.ok.inj (execution.symm.trans observed)
  simpa only [equal, base, List.length_nil] using contract

private theorem inputs : Inputs supplied method handlerValue 0 [idKey] 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, objectPrototypeProjection [], rfl⟩

private theorem domain : ConsumerDomain consumer 4 0 3 record [] (.object 2) 1 snapshot := by
  refine {
    handlerBinding := rfl
    handlersBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    rootDispatch := Or.inl rfl
    closed := ?_
    handlersFound := rfl
    arraysSeparate := by decide
    parameterBinding := rfl
    nodeBinding := rfl
    parameterBound := ?_
    nodeBound := by change (1 : Nat) < 5; decide
    legalKeys := by decide
    pushCapacity := by decide
    reads := ?_}
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [objectPrototypeProjection [], node, parameter, outerRecord method 4, record] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [node, parameter, record, innerRecord, outerRecord, newDataObject,
        emptyNullObject, objectPrototypeProjection] at prototype <;>
      subst parent <;> change (0 : Nat) < 5 <;> decide
  · intro reference equal
    cases Value.object.inj equal
    change (2 : Nat) < 5
    decide
  · intro key member
    have equal : key = idKey := by simpa [snapshot] using member
    subst key
    exact ⟨.object 2 _ rfl, rfl⟩

private theorem record_execution :
    (parseExpression pinnedSource bindings).map
      (fun source => evalExpression 32 defaultSplitLimit source supplied) =
        some (.ok (.object 3, recordState)) := by
  rw [parses_pinned_source, Option.map_some]
  exact congrArg some (run_record supplied method handlerValue 0 [idKey] 7 inputs)

-- All three links execute actual checked expressions: typed Set creation,
-- duplicate successful adds, then the complete object argument. Only later
-- selection/transport is caller scaffolding; it creates no record fields.
example : (parseBlock NodeKeySet.pinnedCreateSource NodeKeySet.bindings).map
    (fun source => execute 32 defaultSplitLimit source
      {base with environment := withoutBindings base.environment ["possibleKeys"]}) =
        some (.ok (.normal (NodeKeySet.createState base))) := by
  rw [NodeKeySet.parses_create, Option.map_some, NodeKeySet.create_execution base (Or.inl rfl)]
example : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
example : ∃ after,
    (parseExpression pinnedSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source supplied) =
      some (.ok (.object supplied.objects.length, after)) ∧
    RecordContract supplied method handlerValue [idKey] 7 (.object supplied.objects.length) after :=
  parsed_source_satisfies supplied method handlerValue 0 [idKey] 7 inputs

/-- Nonempty inhabited producer/record/consumer composition: the duplicate
event is collapsed by the proved producer, the source creates the handler key
field/absent params, and the bridge supplies the complete consumer Entry. -/
example : ∃ after,
    (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
      (fun source => runBlock 65 source consumer) = some (.ok (.normal after)) ∧
    NodeParamLoop.BlockContract consumer after 4 record 0 [] snapshot := by
  exact parsed_source_loop events supplied recordState consumer method handlerValue 0 0 7 [] (.object 2) 1 snapshot
    inputs supplied_contract record_execution rfl rfl domain

-- These descriptor observations are consequences of construction, not fields
-- assumed in ConsumerDomain. Ordinary objects retain intrinsic prototype0.
example : recordState.objects[3]? = some (outerRecord method 4) ∧
    recordState.objects[4]? = some record ∧ recordState.heap[3]? = some [.string idKey] := by cbv
example : record.own.lookup possibleKeysKey = some (.data (.array 3) true true true) ∧
    record.own.lookup paramsKey = none ∧ record.prototype = some 0 := by cbv
example : recordState.environment.lookup "order" = some (.number 8) := by cbv

-- The zero-event context creates both ordinary objects and a fresh empty key
-- snapshot; allocation is not conditional on having a captured parameter.
example : (parseExpression pinnedSource bindings).map
    (fun source => (evalExpression 32 defaultSplitLimit source (NodeKeySet.createState base)).map
      (fun (_, state) => (state.objects.length, state.heap[1]?))) =
        some (.ok (5, some [])) := by cbv

-- Computed special names create own data; they never call the legacy setter.
example : (outerRecord protoKey 4).own.lookup protoKey = some (.data (.object 4) true true true) ∧
    (outerRecord protoKey 4).prototype = some 0 := outer_method protoKey 4
example : (outerRecord constructorKey 4).own.lookup constructorKey =
    some (.data (.object 4) true true true) := (outer_method constructorKey 4).1

-- The actual computed-name source path also produces own __proto__ data.
example : (parseExpression pinnedSource bindings).map
    (fun source => (evalExpression 32 defaultSplitLimit source
      {supplied with environment := ("method", .string protoKey) :: supplied.environment}).map
        (fun (_, state) => state.objects[3]?.bind (fun object => object.own.lookup protoKey))) =
      some (.ok (some (.data (.object 4) true true true))) := by cbv

-- The contract distinguishes prefix increment from merely reading order.
example : (parseExpression "{ [method]: { handler, possibleKeys: [...possibleKeys], score: order, }, }" bindings).map
    (fun source => (evalExpression 32 defaultSplitLimit source supplied).map
      (fun (_, state) => state.objects[4]?.bind (fun object => object.own.lookup scoreKey))) =
        some (.ok (some (.data (.number 7) true true true))) := by cbv
example : (parseExpression pinnedSource bindings).map
    (fun source => (evalExpression 32 defaultSplitLimit source supplied).map
      (fun (_, state) => state.objects[4]?.bind (fun object => object.own.lookup scoreKey))) =
        some (.ok (some (.data (.number 8) true true true))) := by cbv

-- A shadowed later order binding is retained in its original slot.
example : replaceOrder [("x", .boolean true), ("order", .number (-2)), ("order", .number 99)] (-1) =
    [("x", .boolean true), ("order", .number (-1)), ("order", .number 99)] := by cbv
example : SafeOrder 9007199254740990 ∧ ¬ SafeOrder 9007199254740991 := by unfold SafeOrder; decide

end HonoLean.Upstream.HandlerRecord.Examples
