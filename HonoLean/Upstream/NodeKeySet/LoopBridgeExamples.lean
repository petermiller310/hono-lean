import HonoLean.Upstream.NodeKeySet.LoopBridge

namespace HonoLean.Upstream.NodeKeySet

open SourceSubset ECMA2025

private def node : OrdinaryObject := newDataObject {prototype := some 0} idKey (.string [110])
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def base : State :=
  {environment := [("handlerSet", .object 3), ("handlerSets", .array 0),
      ("params", .object 2), ("nodeParams", .object 1), ("createNullObject", .function 0)],
   heap := [[]], objects := [objectPrototypeProjection [], node, parameter, {prototype := some 0}],
   functions := [⟨CreateNullObject.createProgram, []⟩]}

private def events : List JSString := [idKey, idKey]
private def supplied : State :=
  {base with
    environment := [("pattern", .array 2), ("possibleKeys", .set 0)] ++ base.environment
    heap := [[], [.undefined, .string idKey], [.undefined, .string idKey]]
    sets := [[idKey]]}
private def materialized : State := {supplied with heap := supplied.heap ++ [[.string idKey]]}
private def handler : OrdinaryObject :=
  newDataObject {prototype := some 0} NodeParamLoop.possibleKeysKey (.array 3)

/-- Caller storage is explicit scaffolding, not a proof of the unparsed
handler-object field in Node.insert. It transports the actual produced array. -/
private def consumer : State := {materialized with objects := materialized.objects.set 3 handler}
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨[idKey], fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else .undefined⟩

private theorem supplied_contract : TraceContract events 0 supplied := by
  obtain ⟨after, execution, _, contract, _⟩ := created_trace_satisfies base events
  have observed : runSuppliedTrace events (createState base) = .ok supplied := by cbv
  have equal : after = supplied := Except.ok.inj (execution.symm.trans observed)
  simpa only [equal, base, List.length_nil] using contract

private theorem fields : ConsumerFields consumer 3 handler 0 3 [] (.object 2) 1 snapshot := by
  refine {
    toSetupFacts := ?_
    possibleKeys := putOwn_self _ _ _
    arraysSeparate := by decide
    parameterBinding := rfl
    nodeBinding := rfl
    parameterBound := ?_
    nodeBound := by change (1 : Nat) < 4; decide
    legalKeys := by decide
    pushCapacity := by decide
    reads := ?_}
  · refine ⟨rfl, rfl, ⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl, ?_, ?_, rfl⟩
    · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
    · intro reference _ object found parent prototype
      have member := List.mem_of_getElem? found
      change object ∈ [objectPrototypeProjection [], node, parameter, handler] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [node, parameter, handler, newDataObject, emptyNullObject, objectPrototypeProjection] at prototype <;>
        subst parent <;> change (0 : Nat) < 4 <;> decide
  · intro reference equal
    cases Value.object.inj equal
    change (2 : Nat) < 4
    decide
  · intro key member
    have equal : key = idKey := by simpa [snapshot] using member
    subst key
    exact ⟨.object 2 _ rfl, rfl⟩

private theorem spread_observation :
    (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source supplied) =
      some (.ok (.array 3, materialized)) := by
  rw [parses_spread]
  cbv

-- Both actual source edges are present: typed creation and the checked spread.
example : (parseBlock pinnedCreateSource bindings).map (fun source => execute 32 defaultSplitLimit source
    {base with environment := withoutBindings base.environment ["possibleKeys"]}) =
      some (.ok (.normal (createState base))) := by
  rw [parses_create, Option.map_some, create_execution base (Or.inl rfl)]

/-- This nonempty composition obtains the consumer's unique-key proof from
the producer. ConsumerFields contains no unique or keysFound assumption. -/
example : ∃ after,
    (parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings).map
      (fun source => runBlock 65 source consumer) = some (.ok (.normal after)) ∧
    NodeParamLoop.BlockContract consumer after 3 handler 0 [] snapshot := by
  exact producer_snapshot_loop events supplied materialized consumer 0 3 handler 0 3 [] (.object 2) 1 snapshot
    rfl rfl supplied_contract spread_observation rfl fields

end HonoLean.Upstream.NodeKeySet
