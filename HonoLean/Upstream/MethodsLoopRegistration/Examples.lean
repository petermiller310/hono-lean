import HonoLean.Upstream.MethodsLoopRegistration.Correctness

namespace HonoLean.Upstream.MethodsLoopRegistration.Examples

open SourceSubset ECMA2025
set_option maxRecDepth 65536

private def idKey : JSString := [105, 100]
private def nameKey : JSString := [110, 97, 109, 101]
private def getMethod : JSString := [71, 69, 84]
private def keys : List JSString := [idKey, nameKey]
private def events : List JSString := [idKey, nameKey, idKey]
private def handler : Value := .string [104]
private def node : OrdinaryObject :=
  newDataObject (newDataObject emptyNullObject idKey (.string [110])) nameKey (.number 0)
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def owner : OrdinaryObject := {prototype := some 0}
private def base : State :=
  {environment := [("curNode", .object 3), ("method", .string SearchEntry.allKey), ("handler", handler), ("order", .number 7)]
   heap := [[]], objects := [objectPrototypeProjection [], node, parameter, owner]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   privates := PrivateStore.ofData ([("methods", 7)]) ([(3, [(7, .array 0)])])}
private def supplied : State :=
  {base with
    environment := [("pattern", .array 3), ("possibleKeys", .set 0)] ++ base.environment
    heap := [[], [.undefined, .string idKey], [.undefined, .string nameKey], [.undefined, .string idKey]]
    sets := [keys]}
private def searchEnvironment : List (String × Value) := [("searchLocal", .number 55)]
private def context : List (String × Value) :=
  [("node", .object 3), ("method", .string getMethod), ("METHOD_NAME_ALL", .string SearchEntry.allKey),
   ("createNullObject", .function 0), ("params", .object 2), ("nodeParams", .object 1),
   ("m", .null), ("handlerSet", .boolean false), ("i", .number 71), ("len", .number 83)]
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨keys, fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else if key = nameKey then .number 0 else .undefined⟩
private def origin : State :=
  activation supplied SearchEntry.allKey handler keys 7 0 searchEnvironment context

private theorem inputs : NodeMethodsPush.Inputs supplied SearchEntry.allKey handler 0 keys 7 3 7 0 [] :=
  {toInputs := ⟨rfl, rfl, rfl, rfl, rfl, objectPrototypeProjection [], rfl⟩
   ownerBinding := rfl, ownerFound := ⟨owner, rfl⟩, privateName := rfl,
   privateSlot := ⟨[(7, .array 0)], rfl, rfl⟩, methodsFound := rfl}

private theorem trace : NodeKeySet.TraceContract events 0 supplied := by
  obtain ⟨after, execution, _, contract, _⟩ := NodeKeySet.created_trace_satisfies base events
  have observed : NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied := by cbv
  have equal : after = supplied := Except.ok.inj (execution.symm.trans observed)
  simpa only [equal, base, List.length_nil] using contract

private theorem domain : Context supplied context 3 getMethod (.object 2) 1 snapshot := by
  refine {
    ownerBinding := rfl, queryBinding := rfl, allBinding := rfl, parameterBinding := rfl, nodeBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    closed := ?_, rootDispatch := Or.inl rfl, nodeBound := by decide,
    parameterBound := ?_, legalKeys := by decide, reads := ?_}
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [objectPrototypeProjection [], node, parameter, owner] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [node, parameter, owner, newDataObject, emptyNullObject, objectPrototypeProjection] at prototype
    subst parent
    decide
  · intro reference equal
    cases Value.object.inj equal
    decide
  · intro key member
    have cases : key = idKey ∨ key = nameKey := by simpa [snapshot, keys] using member
    rcases cases with rfl | rfl
    · exact ⟨.object 2 _ rfl, rfl⟩
    · exact ⟨.object 2 _ rfl, rfl⟩

private theorem queryDomain : QueryDomain supplied SearchEntry.allKey getMethod :=
  Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)

/-- The initial Layout is established from actual registration fields and old
protected reads, not assumed as an input and not checked only by execution. -/
theorem actual_all_two_key_layout :
    MethodsLoopInitial.Layout origin (rows supplied) getMethod 5 2
      [record supplied handler 7 snapshot] (.object 2) 1 [] :=
  initial_layout events supplied SearchEntry.allKey getMethod handler 0 7 3 7 0 searchEnvironment context
    (.object 2) 1 snapshot inputs trace domain queryDomain

/-- Checked Set creation and duplicate supplied add events precede actual
registration, later source collector allocation and complete source loop.
The handoffs are explicit; the insertion branch producing events is not proved. -/
theorem created_all_two_key_pipeline :
    (parseBlock NodeKeySet.pinnedCreateSource NodeKeySet.bindings).map
      (fun source => execute 32 defaultSplitLimit source
        {base with environment := withoutBindings base.environment ["possibleKeys"]}) =
      some (.ok (.normal (NodeKeySet.createState base))) ∧
    NodeKeySet.runSuppliedTrace events (NodeKeySet.createState base) = .ok supplied ∧
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source supplied) =
        some (.ok (.number 1, registered supplied SearchEntry.allKey handler keys 7 0)) ∧
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation (registered supplied SearchEntry.allKey handler keys 7 0) searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState
        (SearchEntry.searchActivation (registered supplied SearchEntry.allKey handler keys 7 0) searchEnvironment)))) ∧
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock 106 source origin) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract origin after (rows supplied) getMethod 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [NodeKeySet.parses_create, Option.map_some, NodeKeySet.create_execution base (Or.inl rfl)]
  · cbv
  · exact parsed_pipeline_satisfies events supplied SearchEntry.allKey getMethod
      handler 0 7 3 7 0 searchEnvironment context (.object 2) 1 snapshot inputs trace domain queryDomain

private def observations : Except EvalError (List Value × Value × Value × Nat) := do
  match ← runBlock 106 MethodsLoop.program origin with
  | .returned _ _ => throw .unsupported
  | .normal after =>
    let params ← (getProperty propertyFuel after.objects 5 NodeParamAssignment.paramsKey).mapError EvalError.objectError
    let id ← readProperty params (.string idKey) after
    let name ← readProperty params (.string nameKey) after
    pure (after.heap[5]?.getD [], id, name, after.objects.length)

-- Query GET obtains the source-created ALL handler (inner5), preserving its
-- optional first id and the node's zero for the second key. No binding chooses it.
example : observations = .ok ([.object 5], .string [112], .number 0, 7) := by cbv

end HonoLean.Upstream.MethodsLoopRegistration.Examples
