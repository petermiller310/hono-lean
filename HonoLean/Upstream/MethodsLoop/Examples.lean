import HonoLean.Upstream.MethodsLoop.Correctness

namespace HonoLean.Upstream.MethodsLoop

open SourceSubset ECMA2025

set_option maxRecDepth 32768

private def getKey : JSString := [71, 69, 84]
private def handler : OrdinaryObject := newDataObject emptyNullObject NodeParamLoop.possibleKeysKey (.array 0)
private def hitRow : OrdinaryObject := newDataObject emptyNullObject getKey (.object 3)
private def rows : List Value := [.object 2, .object 1, .object 1]
private def fixture : State :=
  {environment := [("node", .object 0), ("method", .string getKey),
      ("METHOD_NAME_ALL", .string SearchEntry.allKey), ("handlerSets", .array 2),
      ("params", .null), ("nodeParams", .object 4), ("createNullObject", .function 0),
      ("i", .number 17), ("len", .number 19), ("m", .boolean false), ("handlerSet", .null)],
   heap := [[], rows, []], objects := [emptyNullObject, hitRow, emptyNullObject, handler, emptyNullObject],
   functions := [⟨CreateNullObject.createProgram, []⟩],
   privates := PrivateStore.ofData ([("methods", 7)]) ([(0, [(7, .array 1)])])}

private def first : State := {fixture with environment := header fixture.environment 0 3}
private def missed : State := {fixture with environment := header fixture.environment 1 3}
private def captured : State :=
  {NodeParamLoop.setupState (selectedState missed 1 (.object 3)) 3 handler 2 [] with
    environment := header fixture.environment 2 3}
private def prefixState : Nat → State
  | 0 => first
  | 1 => missed
  | _ => captured

private theorem miss_choice : SearchEntry.Choice first 2 getKey .undefined := by
  exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩

private theorem hit_choice : SearchEntry.Choice missed 1 getKey (.object 3) := by
  exact ⟨.object 3, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩

/-- Proves all mathematically permitted prefixes, not just one evaluated trace,
have the three expected states. Structural Entry links prevent spurious captures.
The second hit reuses the exact same handler reference. -/
private theorem prefix_shape {count : Nat} {before : State} {selected : List ObjectRef}
    (trace : Processed fixture rows getKey 2 count before selected) :
    count ≤ 2 → before = prefixState count := by
  induction trace with
  | start => intro _; rfl
  | @skip count before selected row chosen prior atRow choice falsy ih =>
    intro bound
    have previous : count = 0 ∨ count = 1 := by omega
    rcases previous with rfl | rfl
    · have state := ih (by omega)
      change before = first at state
      subst before
      have rowEqual : row = 2 := by simpa [rows] using atRow.symm
      subst row
      rfl
    · have state := ih (by omega)
      change before = missed at state
      subst before
      have rowEqual : row = 1 := by simpa [rows] using atRow.symm
      subst row
      have equal := MethodsLoopSupport.choice_unique missed 1 getKey chosen (.object 3) choice hit_choice
      subst chosen
      exact False.elim (falsy (by simp [NodeParamAssignment.Truthy]))
  | @capture count before after selected row handlerRef handlerObject keysArray priorHandlers parameterReceiver nodeParams snapshot
      prior atRow choice entry contract ih =>
    intro bound
    have previous : count = 0 ∨ count = 1 := by omega
    rcases previous with rfl | rfl
    · have state := ih (by omega)
      change before = first at state
      subst before
      have rowEqual : row = 2 := by simpa [rows] using atRow.symm
      subst row
      have impossible := MethodsLoopSupport.choice_unique first 2 getKey (.object handlerRef) .undefined choice miss_choice
      cases impossible
    · have state := ih (by omega)
      change before = missed at state
      subst before
      have rowEqual : row = 1 := by simpa [rows] using atRow.symm
      subst row
      have selectedEqual := MethodsLoopSupport.choice_unique missed 1 getKey (.object handlerRef) (.object 3) choice hit_choice
      cases Value.object.inj selectedEqual
      have handlerEqual : handlerObject = handler := by
        simpa [selectedState, rowState, bodyEntry, missed, fixture] using entry.handlerFound.symm
      subst handlerObject
      have keysEqual : keysArray = 0 := by
        simpa [handler, newDataObject, putOwn] using entry.possibleKeys.symm
      subst keysArray
      have empty : snapshot.keys = [] := MethodsLoopSupport.entry_empty_keys _ _ _ _ _ _ _ _ _ entry rfl
      have afterEqual := MethodsLoopSupport.contract_empty_keys _ _ _ _ _ _ _ empty contract
      have priorEqual : priorHandlers = [] := by
        simpa [selectedState, rowState, bodyEntry, missed, fixture] using entry.handlersFound.symm
      subst priorHandlers
      rw [afterEqual]
      rfl

private def emptySnapshot : NodeParamLoop.Snapshot := ⟨[], fun _ => .undefined, fun _ => .undefined⟩

private theorem first_capture_entry :
    NodeParamLoop.Entry (selectedState missed 1 (.object 3)) 3 handler 2 0 [] .null 4 emptySnapshot := by
  refine {
    toSetupFacts := ⟨rfl, rfl, ⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl, ?_, ?_, rfl⟩
    possibleKeys := rfl, keysFound := rfl, arraysSeparate := by decide,
    parameterBinding := rfl, nodeBinding := rfl, parameterBound := ?_, nodeBound := by decide,
    unique := List.nodup_nil, legalKeys := by decide, pushCapacity := by decide, reads := ?_}
  · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [emptyNullObject, hitRow, emptyNullObject, handler, emptyNullObject] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [hitRow, handler, newDataObject, emptyNullObject] at prototype
  · intro reference impossible; cases impossible
  · intro key impossible; cases impossible

private theorem second_capture_entry :
    NodeParamLoop.Entry (selectedState captured 1 (.object 3)) 3
      (newDataObject handler NodeParamAssignment.paramsKey (.object 5)) 2 0 [.object 3] .null 4 emptySnapshot := by
  refine {
    toSetupFacts := ⟨rfl, rfl, ⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl, ?_, ?_, rfl⟩
    possibleKeys := rfl, keysFound := rfl, arraysSeparate := by decide,
    parameterBinding := rfl, nodeBinding := rfl, parameterBound := ?_, nodeBound := by decide,
    unique := List.nodup_nil, legalKeys := by decide, pushCapacity := by decide, reads := ?_}
  · exact ⟨Or.inr ⟨.object 5, true, true, rfl⟩, Or.inr ⟨.object 5, rfl⟩⟩
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [emptyNullObject, hitRow, emptyNullObject,
      newDataObject handler NodeParamAssignment.paramsKey (.object 5), emptyNullObject, emptyNullObject] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hitRow, handler, newDataObject, emptyNullObject] at prototype
  · intro reference impossible; cases impossible
  · intro key impossible; cases impossible

private theorem fixture_domain : NormalPrefixes fixture rows getKey 2 0 := by
  intro count before selected trace inside
  have small : count ≤ 2 := by change count < 3 at inside; omega
  have equal := prefix_shape trace small
  subst before
  have cases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · refine ⟨2, rfl, ⟨?_, ?_⟩⟩
    · exact ⟨.undefined, rfl, fun _ => ⟨SearchEntry.allKey, .undefined, rfl, rfl⟩⟩
    · intro chosen choice truth
      have equal := MethodsLoopSupport.choice_unique first 2 getKey chosen .undefined choice miss_choice
      subst chosen
      exact False.elim (by simp [NodeParamAssignment.Truthy] at truth)
  · refine ⟨1, rfl, ⟨?_, ?_⟩⟩
    · exact ⟨.object 3, rfl, fun impossible => False.elim (impossible (by simp [NodeParamAssignment.Truthy]))⟩
    · intro chosen choice _
      have equal := MethodsLoopSupport.choice_unique missed 1 getKey chosen (.object 3) choice hit_choice
      subst chosen
      exact ⟨3, handler, 0, [], .null, 4, emptySnapshot, rfl, first_capture_entry, by decide⟩
  · refine ⟨1, rfl, ⟨?_, ?_⟩⟩
    · exact ⟨.object 3, rfl, fun impossible => False.elim (impossible (by simp [NodeParamAssignment.Truthy]))⟩
    · intro chosen choice _
      have capturedChoice : SearchEntry.Choice captured 1 getKey (.object 3) :=
        ⟨.object 3, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      have equal := MethodsLoopSupport.choice_unique captured 1 getKey chosen (.object 3) choice capturedChoice
      subst chosen
      exact ⟨3, newDataObject handler NodeParamAssignment.paramsKey (.object 5), 0, [.object 3], .null, 4,
        emptySnapshot, rfl, second_capture_entry, by decide⟩

private theorem fixture_inputs : Inputs fixture 0 7 1 2 rows getKey := by
  refine ⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, rfl, ⟨[(7, .array 1)], rfl, rfl⟩, rfl, by decide, by decide⟩

/-- A mathematically inhabited mixed miss/two-hit/repeated-reference domain for
the universal parsed-loop theorem, rather than only a closed evaluator example. -/
theorem mixed_repeated_satisfies : ∃ after,
    (parseBlock pinnedSource bindings ["methods"]).map
      (fun source => runBlock 106 source fixture) = some (.ok (.normal after)) ∧
    LoopContract fixture after rows getKey 2 :=
  parsed_loop_satisfies 0 fixture 0 7 1 2 rows getKey fixture_inputs fixture_domain

private def id : JSString := [105, 100]
private def other : JSString := [120]
private def multiFixture : State :=
  {fixture with
    environment := [("node", .object 0), ("method", .string getKey),
      ("METHOD_NAME_ALL", .string SearchEntry.allKey), ("handlerSets", .array 2),
      ("params", .object 5), ("nodeParams", .object 4), ("createNullObject", .function 0),
      ("i", .number 17), ("len", .number 19), ("m", .boolean false), ("handlerSet", .null)],
    heap := [[.string id, .string other], rows, []],
    objects := [emptyNullObject, hitRow, emptyNullObject, handler,
      newDataObject (newDataObject emptyNullObject id (.string [110])) other (.string [120]),
      newDataObject emptyNullObject id (.string [111])]}

private def observations (source : String) (before : State) (budget : Nat) : Option (Except EvalError (List Value × Value × Value × Nat × Bool)) :=
  (parseBlock source bindings ["methods"]).map fun parsed => do
    match ← runBlock budget parsed before with
    | .returned _ _ => throw .unsupported
    | .normal after =>
      let selected := after.heap[2]?.getD []
      let params ← (getProperty propertyFuel after.objects 3 NodeParamAssignment.paramsKey).mapError EvalError.objectError
      let idValue ← readProperty params (.string id) after
      let otherValue ← readProperty params (.string other) after
      pure (selected, idValue, otherValue, after.objects.length, decide (after.environment = before.environment))

/-- Both hits append the same reference and reset it twice; the inner i starts
at zero each time despite the enclosing row index, retaining optional id. -/
example : observations pinnedSource multiFixture 108 = some (.ok
    ([.object 3, .object 3], .string [111], .string [120], 8, true)) := by
  rw [observations, parses_source]
  cbv

example : observations pinnedSource fixture 106 = some (.ok
    ([.object 3, .object 3], .undefined, .undefined, 7, true)) := by
  rw [observations, parses_source]
  cbv

private def allRows : List Value := [.object 1]
private def allFixture : State :=
  {multiFixture with
    heap := [[.string id, .string other], allRows, []],
    objects := [emptyNullObject, newDataObject emptyNullObject SearchEntry.allKey (.object 3),
      emptyNullObject, handler,
      newDataObject (newDataObject emptyNullObject id (.string [110])) other (.string [120]),
      newDataObject emptyNullObject id (.string [111])]}
private def allStart : State := {allFixture with environment := header allFixture.environment 0 1}
private def allSnapshot : NodeParamLoop.Snapshot :=
  ⟨[id, other], fun key => if key = id then .string [111] else .undefined,
    fun key => if key = id then .string [110] else .string [120]⟩

private theorem all_choice : SearchEntry.Choice allStart 1 getKey (.object 3) := by
  exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩

private theorem all_capture_entry :
    NodeParamLoop.Entry (selectedState allStart 1 (.object 3)) 3 handler 2 0 [] (.object 5) 4 allSnapshot := by
  refine {
    toSetupFacts := ⟨rfl, rfl, ⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl, ?_, ?_, rfl⟩
    possibleKeys := rfl, keysFound := rfl, arraysSeparate := by decide,
    parameterBinding := rfl, nodeBinding := rfl, parameterBound := ?_, nodeBound := by decide,
    unique := by decide, legalKeys := by decide, pushCapacity := by decide, reads := ?_}
  · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [emptyNullObject, newDataObject emptyNullObject SearchEntry.allKey (.object 3),
      emptyNullObject, handler,
      newDataObject (newDataObject emptyNullObject id (.string [110])) other (.string [120]),
      newDataObject emptyNullObject id (.string [111])] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [handler, newDataObject, emptyNullObject] at prototype
  · intro reference equal
    cases Value.object.inj equal
    decide
  · intro key member
    change key ∈ [id, other] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨.object 5 _ rfl, rfl⟩

private theorem all_domain : NormalPrefixes allFixture allRows getKey 2 2 := by
  intro count before selected trace inside
  have zero : count = 0 := by change count < 1 at inside; omega
  subst count
  cases trace
  refine ⟨1, rfl, ⟨?_, ?_⟩⟩
  · exact ⟨.undefined, rfl, fun _ => ⟨SearchEntry.allKey, .object 3, rfl, rfl⟩⟩
  · intro chosen choice _
    have equal := MethodsLoopSupport.choice_unique allStart 1 getKey chosen (.object 3) choice all_choice
    subst chosen
    exact ⟨3, handler, 0, [], .object 5, 4, allSnapshot, rfl, all_capture_entry, by decide⟩

private theorem all_inputs : Inputs allFixture 0 7 1 2 allRows getKey := by
  refine ⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, rfl, ⟨[(7, .array 1)], rfl, rfl⟩, rfl, by decide, by decide⟩

/-- Actual ALL fallback with two keys also inhabits the universal theorem.
Only the initial prefix precedes this single row, so its complete NormalPrefixes
domain follows from current structural reads rather than any source success. -/
theorem all_multikey_satisfies : ∃ after,
    (parseBlock pinnedSource bindings ["methods"]).map
      (fun source => runBlock 106 source allFixture) = some (.ok (.normal after)) ∧
    LoopContract allFixture after allRows getKey 2 :=
  parsed_loop_satisfies 2 allFixture 0 7 1 2 allRows getKey all_inputs all_domain

end HonoLean.Upstream.MethodsLoop
