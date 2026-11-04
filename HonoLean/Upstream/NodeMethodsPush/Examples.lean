import HonoLean.Upstream.NodeMethodsPush.StorageBridge

namespace HonoLean.Upstream.NodeMethodsPush.Examples

open SourceSubset ECMA2025

set_option maxRecDepth 65536

private def node : OrdinaryObject := newDataObject {prototype := some 0} idKey (.string [110])
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def owner : OrdinaryObject := {prototype := some 0}
private def method : JSString := [71, 69, 84]
private def prior : List Value := [.object 1]
/-- Deliberate handler-to-methods alias. Appending a map creates a reference
cycle through map→handlerRecord→handler→methods; no deep JSON frame is claimed. -/
private def handlerValue : Value := .array 0
private def base : State :=
  {environment := [("curNode", .object 3), ("method", .string method), ("handler", handlerValue),
      ("order", .number 7), ("handlerSets", .array 1), ("params", .object 2),
      ("nodeParams", .object 1), ("createNullObject", .function 0)]
   heap := [prior, []]
   objects := [objectPrototypeProjection [], node, parameter, owner]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   privates := PrivateStore.ofData [("methods", 7)] [(3, [(7, .array 0)]), (1, [(7, .array 0)])]}

-- Array1 is a caller-preallocated consumer collector. Actual Node.search
-- allocates its collector later; this immediate composition does not prove
-- that later allocation/transport lifecycle or the method-selection source.

private def events : List JSString := [idKey, idKey]
private def supplied : State :=
  {base with
    environment := [("pattern", .array 3), ("possibleKeys", .set 0)] ++ base.environment
    heap := [prior, [], [.undefined, .string idKey], [.undefined, .string idKey]]
    sets := [[idKey]]}
private def afterPush : State := pushedState supplied method handlerValue [idKey] 7 0 prior
private def record : OrdinaryObject := HandlerRecord.innerRecord handlerValue 4 8
private def consumer : State := selectedState afterPush 5
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨[idKey], fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else .undefined⟩

private theorem inputs : Inputs supplied method handlerValue 0 [idKey] 7 3 7 0 prior :=
  {toInputs := ⟨rfl, rfl, rfl, rfl, rfl, objectPrototypeProjection [], rfl⟩
   ownerBinding := rfl
   ownerFound := ⟨owner, rfl⟩
   privateName := rfl
   privateSlot := ⟨[(7, .array 0)], rfl, rfl⟩
   methodsFound := rfl}

private theorem supplied_contract : NodeKeySet.TraceContract events 0 supplied := by
  obtain ⟨after, execution, _, contract, _⟩ := NodeKeySet.created_trace_satisfies base events
  have observed : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
  have equal : after = supplied := Except.ok.inj (execution.symm.trans observed)
  simpa only [equal, base, List.length_nil] using contract

private theorem execution :
    (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source supplied) =
        some (.ok (.number 2, afterPush)) := by
  rw [parses_pinned_source, Option.map_some]
  exact congrArg some (run_push supplied method handlerValue 0 [idKey] 7 3 7 0 prior inputs)

private theorem domain : ConsumerRemainder supplied afterPush handlerValue 7 0 1 [] (.object 2) 1 snapshot := by
  refine {
    handlersBinding := rfl
    handlersOld := rfl
    handlersSeparate := by decide
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    rootDispatch := Or.inl rfl
    closed := ?_
    parameterBinding := rfl
    nodeBinding := rfl
    parameterBound := ?_
    nodeBound := by change (1 : Nat) < 4; decide
    legalKeys := by decide
    pushCapacity := by decide
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
    change (2 : Nat) < 4
    decide
  · intro key member
    have equal : key = idKey := by simpa [snapshot] using member
    subst key
    exact ⟨.object 2 _ rfl, rfl⟩

-- Real typed Set creation plus two supplied successful string events. Private
-- owner/brand initialization is explicitly staged and remains unproved source.
example : (parseBlock NodeKeySet.pinnedCreateSource NodeKeySet.bindings).map
    (fun source => execute 32 defaultSplitLimit source
      {base with environment := withoutBindings base.environment ["possibleKeys"]}) =
        some (.ok (.normal (NodeKeySet.createState base))) := by
  rw [NodeKeySet.parses_create, Option.map_some, NodeKeySet.create_execution base (Or.inl rfl)]
example : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv

-- Inhabited universal full private-call contract, including returned length.
example : ∃ after,
    (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source supplied) =
        some (.ok (.number (Int.ofNat (prior.length + 1)), after)) ∧
    PushContract supplied method handlerValue [idKey] 7 0 prior (.number (Int.ofNat (prior.length + 1))) after :=
  parsed_source_satisfies supplied method handlerValue 0 [idKey] 7 3 7 0 prior inputs

-- Stored prefix/index and requested own method are derived from actual source.
example : (afterPush.heap[0]?).bind (fun elements => elements[1]?) = some (.object 4) ∧
    (afterPush.objects[4]?).bind (fun object => object.own.lookup method) =
      some (.data (.object 5) true true true) ∧
    afterPush.objects[5]? = some record ∧ afterPush.heap[4]? = some [.string idKey] :=
  parsed_source_storage supplied afterPush (.number 2) method handlerValue 0 [idKey] 7 3 7 0 prior inputs execution

/-- Duplicate events→actual private push→stored handler/key cells→consumer.
Only the caller's later choice of the stored handler is staged; neither append,
record fields nor key-array transport/uniqueness are assumed. The collector is
preallocated; this is not a source proof of actual later Node.search setup. -/
example : ∃ completed,
    (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
      (fun source => runBlock 65 source consumer) = some (.ok (.normal completed)) ∧
    NodeParamLoop.BlockContract consumer completed 5 record 1 [] snapshot := by
  exact parsed_source_loop events supplied afterPush method handlerValue 0 7 3 7 0 1 prior [] (.object 2) 1 snapshot
    inputs supplied_contract execution domain

-- Statement observation keeps the updated state but discards push's expression
-- value. It does not use runBlock, which would restore the incoming value env.
example : (parseBlock pinnedSource bindings privateNames).map
    (fun source => execute 35 defaultSplitLimit source supplied) = some (.ok (.normal afterPush)) := by
  rw [parses_pinned_statement, Option.map_some]
  exact congrArg some (run_statement supplied method handlerValue 0 [idKey] 7 3 7 0 prior inputs)
example : afterPush.environment.lookup "order" = some (.number 8) ∧
    afterPush.heap[0]? = some [.object 1, .object 4] ∧
    (record.own.lookup HandlerRecord.handlerKey) = some (.data (.array 0) true true true) := by cbv

-- With no add events, the full source still appends a new record and allocates
-- its fresh empty key snapshot; the old methods prefix already has one item.
example : (parseExpression pinnedSource bindings privateNames).map
    (fun source => (evalExpression 34 defaultSplitLimit source (NodeKeySet.createState base)).map
      (fun (value, state) => (value, state.objects.length, state.heap[2]?))) =
        some (.ok (.number 2, 6, some [])) := by cbv

-- Both private owners retain the same addressed mutable array after the push.
example : privateGet (.object 3) "methods" afterPush = .ok (.array 0) ∧
    privateGet (.object 1) "methods" afterPush = .ok (.array 0) := by cbv

-- Ordinary public same-spelling properties cannot forge lexical private brand.
private def publicShadow : State :=
  {supplied with
    objects := supplied.objects.set 3 (newDataObject owner [35, 109, 101, 116, 104, 111, 100, 115] (.array 0))
    privates := {names := [("methods", 7)], elements := []}}
example : (parseExpression pinnedSource bindings privateNames).map
    (fun source => evalExpression 34 defaultSplitLimit source publicShadow) = some (.error .privateBrand) := by cbv
example : (parseExpression pinnedSource bindings []).isNone = true := by cbv
example : (parseExpression pinnedSource bindings privateNames).map
    (fun source => evalExpression 34 defaultSplitLimit source {supplied with privates := {}}) =
      some (.error .privateScope) := by cbv
example : (parseExpression pinnedSource bindings privateNames).map
    (fun source => evalExpression 34 defaultSplitLimit source
      {supplied with privates := {supplied.privates with names := [("methods", 8)]}}) =
        some (.error .privateBrand) := by cbv

-- A parsed, supported source mutation appends no new map.
example : (parseExpression "curNode.#methods.push()" bindings privateNames).map
    (fun source => (evalExpression 34 defaultSplitLimit source supplied).map
      (fun (value, state) => (value, state.heap[0]?))) =
        some (.ok (.number 1, some prior)) := by cbv

end HonoLean.Upstream.NodeMethodsPush.Examples
