import HonoLean.Upstream.RegistrationHistoryLoop.Correctness

namespace HonoLean.Upstream.RegistrationHistoryLoop.Examples

open SourceSubset ECMA2025 RegistrationHistory

set_option maxRecDepth 65536

private def getMethod : JSString := [71, 69, 84]
private def postMethod : JSString := [80, 79, 83, 84]
private def idKey : JSString := [105, 100]
private def nameKey : JSString := [110, 97, 109, 101]
private def first : Request := ⟨getMethod, .string [103], [idKey, nameKey, idKey]⟩
private def second : Request := ⟨postMethod, .string [112], [idKey]⟩
private def third : Request := ⟨SearchEntry.allKey, .string [97], [nameKey, idKey]⟩
private def requests : List Request := [first, second, third]
private def nodeObject : OrdinaryObject :=
  newDataObject (newDataObject emptyNullObject idKey (.string [110])) nameKey (.number 0)
private def parameterObject : OrdinaryObject := newDataObject emptyNullObject idKey (.string [112])
private def before : State :=
  {environment := [("order", .number 0)]
   heap := [[]]
   objects := [objectPrototypeProjection [], nodeObject, parameterObject, {prototype := some 0}]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   privates := PrivateStore.ofData ([("methods", 7)]) ([(3, [(7, .array 0)])])}
private def parameter (key : JSString) : Value := if key = idKey then .string [112] else .undefined
private def node (key : JSString) : Value :=
  if key = idKey then .string [110] else if key = nameKey then .number 0 else .undefined
private def searchEnvironment : List (String × Value) := [("searchLocal", .number 17)]
private def context : List (String × Value) :=
  [("node", .object 3), ("method", .string getMethod), ("METHOD_NAME_ALL", .string SearchEntry.allKey),
   ("params", .object 2), ("nodeParams", .object 1), ("createNullObject", .function 0),
   ("m", .null), ("handlerSet", .boolean false), ("i", .number 71), ("len", .number 83)]
private def registered : State := endState before 3 0 0 [] requests
private def origin : State := activation registered searchEnvironment context

private theorem seed : Seed before 3 7 0 0 [] :=
  ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨{prototype := some 0}, rfl⟩,
    rfl, ⟨[(7, .array 0)], rfl, rfl⟩, rfl⟩

private theorem first_keys : first.keys = [idKey, nameKey] := by cbv
private theorem second_keys : second.keys = [idKey] := by cbv
private theorem third_keys : third.keys = [nameKey, idKey] := by cbv

private theorem domain : Context before requests context 3 getMethod (.object 2) 1 2 parameter node := by
  refine {
    ownerBinding := rfl, queryBinding := rfl, allBinding := rfl, parameterBinding := rfl, nodeBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    closed := ?_, rootDispatch := Or.inl rfl, nodeBound := by decide
    parameterBound := ?_, capacity := by decide, keyBounds := ?_, reads := ?_, queries := ?_}
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [objectPrototypeProjection [], nodeObject, parameterObject, {prototype := some 0}] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [nodeObject, parameterObject, newDataObject, emptyNullObject, objectPrototypeProjection] at prototype
    subst parent
    decide
  · intro reference equal
    cases Value.object.inj equal
    decide
  · intro request member
    change request ∈ [first, second, third] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [first_keys, second_keys, third_keys]
  · intro request member key keyMember
    have keys : key = idKey ∨ key = nameKey := by
      change request ∈ [first, second, third] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [first_keys] using keyMember
      · exact Or.inl (by simpa [second_keys] using keyMember)
      · have either : key = nameKey ∨ key = idKey := by simpa [third_keys] using keyMember
        exact either.elim Or.inr Or.inl
    rcases keys with rfl | rfl
    · exact ⟨.object 2 _ rfl, rfl⟩
    · exact ⟨.object 2 _ rfl, rfl⟩
  · intro request member
    change request ∈ [first, second, third] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨by decide, by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)

/-- A genuine three-registration initial Layout: direct GET, genuine POST
miss, then own ALL fallback, with source-created distinct records/key cells. -/
theorem mixed_history_initial_layout :
    MethodsLoopInitial.Layout origin (storedRows before.objects.length requests) getMethod registered.heap.length 2
      (storedRecords before.objects.length before.heap.length 0 requests parameter node) (.object 2) 1 [] :=
  parsed_history_layout before 3 7 0 0 requests searchEnvironment context getMethod (.object 2) 1 2 parameter node seed domain

/-- Source history, actual later collector and complete parsed helper loop.
No selected-handler binding, final Layout or future capture fact is supplied. -/
theorem mixed_history_pipeline :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source 3 requests before) = some (.ok registered) ∧
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation registered searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState (SearchEntry.searchActivation registered searchEnvironment)))) ∧
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock 108 source origin) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract origin after (storedRows before.objects.length requests) getMethod registered.heap.length :=
  parsed_pipeline_satisfies before 3 7 0 0 requests searchEnvironment context getMethod (.object 2) 1 2 parameter node seed domain

private def observations : Except EvalError (List Value × Value × Value × Value × Value × Nat) := do
  match ← runBlock 108 MethodsLoop.program origin with
  | .returned _ _ => throw .unsupported
  | .normal after =>
    let firstParams ← (getProperty propertyFuel after.objects 5 NodeParamAssignment.paramsKey).mapError EvalError.objectError
    let allParams ← (getProperty propertyFuel after.objects 9 NodeParamAssignment.paramsKey).mapError EvalError.objectError
    let firstId ← readProperty firstParams (.string idKey) after
    let firstName ← readProperty firstParams (.string nameKey) after
    let allId ← readProperty allParams (.string idKey) after
    let allName ← readProperty allParams (.string nameKey) after
    pure (after.heap[4]?.getD [], firstId, firstName, allId, allName, after.objects.length)

-- The differing key order restarts first-key precedence separately per record.
example : observations = .ok ([.object 5, .object 9], .string [112], .number 0, .string [110], .number 0, 12) := by cbv

end HonoLean.Upstream.RegistrationHistoryLoop.Examples
