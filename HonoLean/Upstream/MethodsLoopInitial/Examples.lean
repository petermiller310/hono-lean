import HonoLean.Upstream.MethodsLoopInitial.Correctness

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

private def getKey : JSString := [71, 69, 84]
private def idKey : JSString := [105, 100]
private def otherKey : JSString := [120]
private def snapshot : NodeParamLoop.Snapshot :=
  ⟨[idKey, otherKey], fun key => if key = idKey then .string [112] else .undefined,
    fun key => if key = idKey then .string [110] else .string [120]⟩
private def handler : OrdinaryObject := newDataObject {prototype := some 0}
  NodeParamLoop.possibleKeysKey (.array 0)
private def record : Record := ⟨4, handler, 0, snapshot⟩
private def root : OrdinaryObject := objectPrototypeProjection []
private def missed : OrdinaryObject := {prototype := some 0}
private def hit : OrdinaryObject := newDataObject {prototype := some 0} getKey (.object 4)
private def every : OrdinaryObject := newDataObject {prototype := some 0} SearchEntry.allKey (.object 4)
private def node : OrdinaryObject := newDataObject (newDataObject emptyNullObject idKey (.string [110])) otherKey (.string [120])
private def parameter : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])

/-- Arbitrarily many mixed miss, exact-hit and ALL-fallback rows. Every hit may
alias the same ordinary handler, whose two keys are captured on each visit. -/
private def fixture (references : List Nat) (initial : List Value) : State :=
  {environment := [("node", .object 7), ("method", .string getKey),
      ("handlerSets", .array 2), ("params", .object 6), ("nodeParams", .object 5),
      ("METHOD_NAME_ALL", .string SearchEntry.allKey), ("createNullObject", .function 0)],
    heap := [[.string idKey, .string otherKey], references.map Value.object, initial],
    objects := [root, missed, hit, every, handler, node, parameter, {prototype := some 0}],
    functions := [⟨CreateNullObject.createProgram, []⟩],
    privates := PrivateStore.ofData ([("methods", 9)]) ([(7, [(9, .array 1)])])}

private theorem protected_iff (references : List Nat) (initial : List Value) (reference : Nat) :
    Protected (fixture references initial) [record] reference ↔ reference < 8 ∧ reference ≠ 4 := by
  simp [Protected, fixture, record]

private theorem fixture_record (references : List Nat) (initial : List Value) :
    RecordFacts (fixture references initial) 2 2 (.object 6) 5 record := by
  refine ⟨rfl, rfl, rfl, by decide, ?_, by decide, by decide, by decide, ?_⟩
  · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro key member
    change key ∈ [idKey, otherKey] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.object 6 _ rfl, rfl⟩
    · exact ⟨.object 6 _ rfl, rfl⟩

private theorem fixture_closed (references : List Nat) (initial : List Value) :
    NodeParamLoop.PrototypeClosed (fixture references initial).objects (fixture references initial).objects.length := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [root, missed, hit, every, handler, node, parameter, {prototype := some 0}] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [root, objectPrototypeProjection, missed, hit, every, handler, node, parameter,
      newDataObject, emptyNullObject] at prototype <;>
    subst parent <;> simp [fixture]

private theorem fixture_protected_parents (references : List Nat) (initial : List Value) :
    ∀ reference, Protected (fixture references initial) [record] reference → ∀ object,
      (fixture references initial).objects[reference]? = some object → ∀ parent,
      object.prototype = some parent → Protected (fixture references initial) [record] parent := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [root, missed, hit, every, handler, node, parameter, {prototype := some 0}] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [root, objectPrototypeProjection, missed, hit, every, handler, node, parameter,
      newDataObject, emptyNullObject] at prototype <;>
    subst parent <;> exact (protected_iff references initial 0).mpr (by decide)

private theorem fixture_layout (references : List Nat) (initial : List Value)
    (valid : ∀ reference ∈ references, reference = 1 ∨ reference = 2 ∨ reference = 3)
    (capacity : initial.length + references.length ≤ 4294967295) :
    Layout (fixture references initial) (references.map Value.object) getKey 2 2 [record] (.object 6) 5 initial := by
  refine {
    collectorBinding := rfl, parameterBinding := rfl, nodeBinding := rfl, allBinding := rfl,
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩,
    collectorFound := rfl, capacity := by simpa using capacity,
    closed := fixture_closed references initial,
    protectedParents := fixture_protected_parents references initial,
    nodeProtected := (protected_iff references initial 5).mpr (by decide),
    parameterProtected := ?_, recordsFound := ?_, handlerParents := ?_, rowChoices := ?_ }
  · intro reference equal
    have same : reference = 6 := (Value.object.inj equal).symm
    subst reference
    exact (protected_iff references initial 6).mpr (by decide)
  · intro other member
    have same : other = record := by simpa using member
    subst other
    exact fixture_record references initial
  · intro other member parent prototype
    have same : other = record := by simpa using member
    subst other
    have sameParent : parent = 0 := by simpa [record, handler, newDataObject] using prototype.symm
    subst parent
    exact (protected_iff references initial 0).mpr (by decide)
  · intro count inside
    have bound : count < references.length := by simpa using inside
    let reference := references[count]'bound
    have atRef : references[count]? = some reference := by simp [reference]
    have member : reference ∈ references := List.mem_of_getElem? atRef
    have atRow : (references.map Value.object)[count]? = some (.object reference) := by simp [atRef]
    rcases valid reference member with isMiss | isHit | isAll
    · rw [isMiss] at atRow
      refine ⟨1, .undefined, atRow, (protected_iff references initial 1).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro impossible
        simp [NodeParamAssignment.Truthy] at impossible
    · rw [isHit] at atRow
      refine ⟨2, .object 4, atRow, (protected_iff references initial 2).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 4, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨record, by simp, rfl⟩
    · rw [isAll] at atRow
      refine ⟨3, .object 4, atRow, (protected_iff references initial 3).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro _; exact ⟨record, by simp, rfl⟩

private theorem fixture_inputs (references : List Nat) (initial : List Value)
    (capacity : initial.length + references.length ≤ 4294967295) :
    MethodsLoop.Inputs (fixture references initial) 7 9 1 2 (references.map Value.object) getKey := by
  refine ⟨rfl, rfl, ⟨{prototype := some 0}, rfl⟩, rfl, ⟨[(9, .array 1)], rfl, rfl⟩, rfl, by decide, ?_⟩
  simp only [List.length_map]
  omega

/-- One initial layout suffices for arbitrary row count/order, repeated same
handler identity, two-key captures, exact hits, ALL fallback and misses. The
capacity bound concerns the actual initial collector plus at most one append
per stored row. No future readiness or source execution is an input. -/
theorem arbitrary_mixed_initial_satisfies (references : List Nat) (initial : List Value)
    (valid : ∀ reference ∈ references, reference = 1 ∨ reference = 2 ∨ reference = 3)
    (capacity : initial.length + references.length ≤ 4294967295) :
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock (references.length + 105) source (fixture references initial)) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract (fixture references initial) after (references.map Value.object) getKey 2 := by
  simpa using parsed_initial_satisfies 7 9 1 (fixture_inputs references initial capacity)
    (fixture_layout references initial valid capacity)

example : ∃ after,
    MethodsLoop.LoopContract (fixture [1, 2, 3, 2, 1, 3] []) after
      ([1, 2, 3, 2, 1, 3].map Value.object) getKey 2 := by
  obtain ⟨after, _, contract⟩ := arbitrary_mixed_initial_satisfies [1, 2, 3, 2, 1, 3] [] (by decide) (by decide)
  exact ⟨after, contract⟩

end HonoLean.Upstream.MethodsLoopInitial
