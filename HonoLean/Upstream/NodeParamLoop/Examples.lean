import HonoLean.Upstream.NodeParamLoop.Correctness

namespace HonoLean.Upstream.NodeParamLoop

open SourceSubset ECMA2025

set_option maxRecDepth 32768

private def nodeRecord : OrdinaryObject :=
  newDataObject (newDataObject {prototype := some 0} idKey (.string [110])) constructorKey (.string [103])
private def parameterRecord : OrdinaryObject := newDataObject emptyNullObject idKey (.string [111])
private def handlerRecord : OrdinaryObject := newDataObject {prototype := some 0} possibleKeysKey (.array 0)
private def priorHandlers : List Value := [.object 3, .object 3]

private def fixture (keys : List JSString) : State :=
  {environment := [("handlerSet", .object 3), ("handlerSets", .array 1),
      ("params", .object 2), ("nodeParams", .object 1), ("createNullObject", .function 0),
      ("i", .number 55), ("len", .number 66), ("key", .string [120]), ("Object", .null)],
   heap := [keys.map Value.string, priorHandlers],
   objects := [objectPrototypeProjection [], nodeRecord, parameterRecord, handlerRecord],
   functions := [⟨CreateNullObject.createProgram, []⟩]}

private def snapshot (keys : List JSString) : Snapshot :=
  ⟨keys, fun key => if key = idKey then .string [111] else .undefined,
    fun key => if key = idKey then .string [110]
      else if key = constructorKey then .string [103] else .object 0⟩

/-- Explicit, inhabited premises for the public universal theorem. The existing
handler array intentionally aliases the selected handler twice; the caller
also shadows i/len/key and Object. The helper's captured lexical environment
still uses its standard builtin, and all caller bindings are restored. -/
private theorem fixture_entry (keys : List JSString)
    (only : ∀ key ∈ keys, key = idKey ∨ key = constructorKey ∨ key = protoKey)
    (unique : keys.Nodup) (legal : keys.length ≤ 4294967295) :
    Entry (fixture keys) 3 handlerRecord 1 0 priorHandlers (.object 2) 1 (snapshot keys) := by
  refine {
    toSetupFacts := ?_
    possibleKeys := putOwn_self _ _ _
    keysFound := rfl
    arraysSeparate := by decide
    parameterBinding := rfl
    nodeBinding := rfl
    parameterBound := ?_
    nodeBound := by change (1 : Nat) < 4; decide
    unique := unique
    legalKeys := legal
    pushCapacity := by decide
    reads := ?_}
  · refine ⟨rfl, rfl, ⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl, ?_, ?_, rfl⟩
    · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
    · intro reference _ object found parent prototype
      have member := List.mem_of_getElem? found
      change object ∈ [objectPrototypeProjection [], nodeRecord, parameterRecord, handlerRecord] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [nodeRecord, parameterRecord, handlerRecord, newDataObject, emptyNullObject,
          objectPrototypeProjection] at prototype <;>
        subst parent <;> change (0 : Nat) < 4 <;> decide
  · intro reference equal
    cases Value.object.inj equal
    change (2 : Nat) < 4
    decide
  · intro key member
    rcases only key member with rfl | rfl | rfl <;>
      exact ⟨.object 2 _ rfl, rfl⟩

private def threeKeys : List JSString := [idKey, constructorKey, protoKey]

private theorem three_entry :
    Entry (fixture threeKeys) 3 handlerRecord 1 0 priorHandlers (.object 2) 1 (snapshot threeKeys) := by
  apply fixture_entry threeKeys
  · intro key member
    simpa [threeKeys] using member
  · decide
  · decide

private theorem zero_entry :
    Entry (fixture []) 3 handlerRecord 1 0 priorHandlers (.object 2) 1 (snapshot []) := by
  apply fixture_entry []
  · intro key impossible
    cases impossible
  · decide
  · decide

/-- A nonempty universal-theorem witness, beyond closed evaluator reduction. -/
example : ∃ after,
    (parseBlock pinnedSource bindings).map (fun source => runBlock (threeKeys.length + 64) source (fixture threeKeys)) =
      some (.ok (.normal after)) ∧
    BlockContract (fixture threeKeys) after 3 handlerRecord 1 priorHandlers (snapshot threeKeys) :=
  parsed_source_satisfies _ 3 handlerRecord 1 0 priorHandlers (.object 2) 1 _ three_entry

example : ∃ after,
    (parseBlock pinnedSource bindings).map (fun source => runBlock 64 source (fixture [])) =
      some (.ok (.normal after)) ∧
    BlockContract (fixture []) after 3 handlerRecord 1 priorHandlers (snapshot []) :=
  parsed_source_satisfies _ 3 handlerRecord 1 0 priorHandlers (.object 2) 1 _ zero_entry

private structure Observation where
  prototype : Option (Option ObjectRef)
  descriptors : List (Option PropertyDescriptor)
  handlerParams : Except ObjectError Value
  handlers : Option (List Value)
  keys : Option (List Value)
  environment : List (String × Value)

private def observe (keys : List JSString) : Option (Except EvalError Observation) :=
  (parseBlock pinnedSource bindings).map fun source => do
    match ← runBlock (keys.length + 64) source (fixture keys) with
    | .returned _ _ => throw .unsupported
    | .normal after => pure ⟨after.objects[4]?.map OrdinaryObject.prototype,
       keys.map (fun key => after.objects[4]?.bind (fun object => object.own.lookup key)),
       getProperty 32 after.objects 3 NodeParamAssignment.paramsKey,
       after.heap[1]?, after.heap[0]?, after.environment⟩

/-- Index zero uses the optional id, later constructor uses node data, and the
legacy inherited proto getter yields an own object reference on the output. -/
example : observe threeKeys = some (.ok
    ⟨some none,
      [some (.data (.string [111]) true true true), some (.data (.string [103]) true true true),
       some (.data (.object 0) true true true)],
      .ok (.object 4), some (priorHandlers ++ [.object 3]), some (threeKeys.map Value.string),
      (fixture threeKeys).environment⟩) := by
  rw [observe, parses_pinned_source]
  cbv

/-- Zero keys still allocate/reset/append, without leaking header bindings. -/
example : observe [] = some (.ok
    ⟨some none, [], .ok (.object 4), some (priorHandlers ++ [.object 3]), some [], (fixture []).environment⟩) := by
  rw [observe, parses_pinned_source]
  cbv

end HonoLean.Upstream.NodeParamLoop
