import HonoLean.Upstream.NodeInitialization.History

namespace HonoLean.Upstream.NodeInitialization.Examples

open SourceSubset ECMA2025 RegistrationHistory

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private def before : State :=
  {environment := [("createNullObject", .function 0), ("caller", .number 99)]
   heap := [[.number 9]]
   objects := [objectPrototypeProjection [], {prototype := some 0}]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   sets := [[[120]]]
   privates := PrivateStore.ofData [("old", 31)] [(1, [(31, .number 9)])]}

private def moduleState : State := preambleState before
private def firstClass : DataClass := definition moduleState.environment (initialNodeWorld before).nextIdentity
private def reservedWorld : PrivateWorld := ⟨(initialNodeWorld before).nextIdentity + 5⟩
private def secondClass : DataClass := definition moduleState.environment reservedWorld.nextIdentity
private def one : State := instanceState moduleState (some 1) firstClass.environment firstClass.baseIdentity (.object 2)
private def two : State := instanceState one (some 1) firstClass.environment firstClass.baseIdentity (.object 2)
private def lexicalTwo : State := classActivation two firstClass.baseIdentity

private theorem helper : HelperBinding before := ⟨0, [], rfl, rfl, Or.inl rfl⟩
private theorem rootFound : ∃ root, before.objects[0]? = some root := ⟨objectPrototypeProjection [], rfl⟩
private theorem fresh : moduleState.privates.slots.lookup moduleState.objects.length = none := by cbv
private theorem prototypeReady : PrototypeReady moduleState (some 1) := ⟨{prototype := some 0}, rfl⟩
private theorem firstBindings : InitializerBindings moduleState firstClass.environment (.object 2) :=
  preamble_initializer_bindings before helper
private theorem secondBindings : InitializerBindings one firstClass.environment (.object 2) :=
  ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩

/-- The cursor starts above an already represented identity, rather than
assuming an empty world. Both definitions are reserved before any instance. -/
theorem source_two_definitions :
    (initialNodeWorld before).nextIdentity = 32 ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
      (fun fields => defineDataClass fields moduleState (initialNodeWorld before)) = some (firstClass, reservedWorld) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
      (fun fields => defineDataClass fields moduleState reservedWorld) = some (secondClass, ⟨42⟩) ∧
    ∀ nameA nameB identityA identityB,
      (nameA, identityA) ∈ firstClass.names → (nameB, identityB) ∈ secondClass.names → identityA ≠ identityB := by
  refine ⟨by cbv, parsed_define_node moduleState (initialNodeWorld before),
    parsed_define_node moduleState reservedWorld, ?_⟩
  intro nameA nameB identityA identityB memberA memberB
  exact successive_definitions_disjoint fieldsProgram fieldsProgram moduleState moduleState
    (initialNodeWorld before) reservedWorld ⟨42⟩ firstClass secondClass
    (define_node moduleState (initialNodeWorld before)) (define_node moduleState reservedWorld)
    nameA nameB identityA identityB memberA memberB

/-- Actual parsed source creates the module singleton, then two instances of
the same lexical definition. Caller names and old stores remain present. -/
theorem source_two_instances :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) = some (.ok (.normal moduleState)) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
      (fun fields => instantiateDataClass 64 defaultSplitLimit
        ⟨fields, firstClass.baseIdentity, firstClass.environment⟩ (some 1) moduleState) = some (.ok (3, one)) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
      (fun fields => instantiateDataClass 64 defaultSplitLimit
        ⟨fields, firstClass.baseIdentity, firstClass.environment⟩ (some 1) one) = some (.ok (5, two)) ∧
    InstanceContract moduleState one (some 1) 32 3 (.object 2) ∧
    InstanceContract one two (some 1) 32 5 (.object 2) := by
  refine ⟨?_, ?_, ?_, instance_contract moduleState (some 1) firstClass.environment 32 (.object 2),
    instance_contract one (some 1) firstClass.environment 32 (.object 2)⟩
  · rw [parses_preamble, Option.map_some, run_preamble before helper]
    rfl
  · rw [parses_fields, Option.map_some]
    exact congrArg some (instantiate_node moduleState (some 1) firstClass.environment firstClass.baseIdentity
      (.object 2) fresh prototypeReady firstBindings)
  · rw [parses_fields, Option.map_some]
    exact congrArg some (instantiate_node one (some 1) firstClass.environment firstClass.baseIdentity
      (.object 2) (by cbv) ⟨{prototype := some 0}, rfl⟩ secondBindings)

private def getMethod : JSString := [71, 69, 84]
private def postMethod : JSString := [80, 79, 83, 84]
private def idKey : JSString := [105, 100]
private def firstRequest : Request := ⟨getMethod, .string [103], [idKey, idKey]⟩
private def secondRequest : Request := ⟨postMethod, .string [112], [idKey]⟩
private def thirdRequest : Request := ⟨SearchEntry.allKey, .string [97], [idKey]⟩
private def requests : List Request := [firstRequest, secondRequest, thirdRequest]
private def onFirst : State := endState lexicalTwo 3 1 0 [] [firstRequest]

private theorem twoSeed : Seed lexicalTwo 3 32 1 0 [] :=
  ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨{prototype := some 1}, rfl⟩,
    rfl, ⟨storedFields moduleState 32 (.object 2), rfl, rfl⟩, rfl⟩

/-- The first methods array becomes nonempty through the actual parsed push;
the second instance retains its separate empty methods array. -/
theorem source_registration_isolates_instances :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source 3 [firstRequest] lexicalTwo) = some (.ok onFirst) ∧
    onFirst.heap[1]? = some [.object 7] ∧ onFirst.heap[3]? = some [] ∧
    privateGet (.object 3) "methods" onFirst = .ok (.array 1) ∧
    privateGet (.object 5) "methods" onFirst = .ok (.array 3) ∧
    privateGet (.object 3) "children" onFirst = .ok (.object 4) ∧
    privateGet (.object 5) "children" onFirst = .ok (.object 6) ∧
    privateGet (.object 3) "patterns" onFirst = .ok (.array 2) ∧
    privateGet (.object 5) "patterns" onFirst = .ok (.array 4) ∧
    privateGet (.object 3) "params" onFirst = .ok (.object 2) ∧
    privateGet (.object 5) "params" onFirst = .ok (.object 2) ∧
    privateGet (.object 3) "pattern" onFirst = .ok .undefined ∧
    privateGet (.object 5) "pattern" onFirst = .ok .undefined ∧
    onFirst.heap[0]? = some [.number 9] ∧
    onFirst.privates.slots.lookup 1 = some [(31, .number 9)] := by
  refine ⟨run_parsed_history lexicalTwo 3 32 1 0 [] [firstRequest] twoSeed, ?_⟩
  cbv

/-- Same spelling in a different reserved class does not grant the first
instance's brand. Instances of one definition intentionally share names. -/
theorem distinct_definition_brand :
    privateGet (.object 3) "methods" (classActivation two secondClass.baseIdentity) = .error .privateBrand ∧
    firstClass.names = nodeNames 32 ∧ secondClass.names = nodeNames 37 ∧
    two.environment = moduleState.environment ∧ two.privates.names = before.privates.names := by cbv

private def fieldObservation (source spelling : String) : Option (Except EvalError Value) :=
  (parsePrivateFields source ["createNullObject", "emptyParams"]).map fun fields => do
    let (dataClass, _) ← match defineDataClass fields moduleState (initialNodeWorld before) with
      | some reserved => .ok reserved
      | none => .error .unsupported
    let (owner, after) ← instantiateDataClass 64 defaultSplitLimit dataClass (some 1) moduleState
    privateGet (.object owner) spelling {after with privates := {after.privates with names := dataClass.names}}

private def editedFields (children pattern params : String) : String :=
  "  #methods: Record<string, HandlerSet<T>>[] = []\n\n  #children: Record<string, Node<T>> = " ++ children ++
  "\n  #patterns: Node<T>[] = []\n" ++ pattern ++ "  #params: Record<string, string> = " ++ params ++ "\n"

theorem field_edit_template_matches_source :
    editedFields "createNullObject()" "  #pattern?: Pattern | string\n" "emptyParams" = pinnedFieldsSource := by decide

/-- Parseable edits can change allocation/aliasing, or remove a private declaration.
These are counterexamples to specific observations, not parser rejection tests. -/
theorem source_mutations_change_observations :
    fieldObservation (editedFields "createNullObject()" "  #pattern?: Pattern | string\n" "[]")
      "params" = some (.ok (.array 3)) ∧
    fieldObservation (editedFields "emptyParams" "  #pattern?: Pattern | string\n" "emptyParams")
      "children" = some (.ok (.object 2)) ∧
    fieldObservation (editedFields "createNullObject()" "" "emptyParams") "pattern" =
      some (.error .privateScope) := by cbv

/-- Type/optional metadata is retained by parsing but does not execute a
runtime initializer. Both controls still install the undefined data field. -/
theorem source_metadata_controls :
    fieldObservation (editedFields "createNullObject()" "  #pattern?: OtherType\n" "emptyParams")
      "pattern" = some (.ok .undefined) ∧
    fieldObservation (editedFields "createNullObject()" "  #pattern: Pattern | string\n" "emptyParams")
      "pattern" = some (.ok .undefined) := by cbv

/-- Inhabited source-facing initial-world theorem, including the derived Seed
and freshness relative to the old identity 31. No desired methods slot is an input. -/
theorem fresh_source_seed :
    ∃ owner after,
      (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
        (fun fields => instantiateDataClass 64 defaultSplitLimit
          ⟨fields, 32, moduleState.environment⟩ (some 1) moduleState) = some (.ok (owner, after)) ∧
      InstanceContract moduleState after (some 1) 32 owner (.object 2) ∧
      Seed (classActivation after 32) owner 32 1 0 [] :=
  (parsed_fresh_initialization_seed before (some 1) helper rootFound fresh prototypeReady).2.2.2

private def initialized : State := initializedState before (some 1)
private def searchEnvironment : List (String × Value) := [("searchLocal", .number 17)]
private def context : List (String × Value) :=
  [("node", .object 3), ("method", .string getMethod), ("METHOD_NAME_ALL", .string SearchEntry.allKey),
   ("params", .null), ("nodeParams", .object 2), ("createNullObject", .function 0),
   ("m", .null), ("handlerSet", .boolean false), ("i", .number 71), ("len", .number 83)]
private def missing (_ : JSString) : Value := .undefined

private theorem domain : RegistrationHistoryLoop.Context initialized requests context 3 getMethod .null 2 1 missing missing := by
  refine {
    ownerBinding := rfl, queryBinding := rfl, allBinding := rfl, parameterBinding := rfl, nodeBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    closed := ?_, rootDispatch := Or.inl rfl, nodeBound := by decide
    parameterBound := ?_, capacity := by decide, keyBounds := ?_, reads := ?_, queries := ?_}
  · intro reference _ object found parent prototype
    have member := List.mem_of_getElem? found
    change object ∈ [objectPrototypeProjection [], {prototype := some 0}, emptyNullObject,
      {prototype := some 1}, emptyNullObject] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [emptyNullObject, objectPrototypeProjection] at prototype
    · subst parent; decide
    · subst parent; decide
  · intro reference equal; cases equal
  · intro request member
    change request ∈ [firstRequest, secondRequest, thirdRequest] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro request member key keyMember
    have equal : key = idKey := by
      change request ∈ [firstRequest, secondRequest, thirdRequest] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · have keys : firstRequest.keys = [idKey] := by cbv
        simpa [keys] using keyMember
      · have keys : secondRequest.keys = [idKey] := by cbv
        simpa [keys] using keyMember
      · have keys : thirdRequest.keys = [idKey] := by cbv
        simpa [keys] using keyMember
    subst key
    exact ⟨.nullish .null (Or.inl rfl), rfl⟩
  · intro request member
    change request ∈ [firstRequest, secondRequest, thirdRequest] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨by decide, by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)

/-- Module declarations, data initialization, three source registrations and
the complete source capture loop compose on an inhabited domain. The sequence
includes a GET hit, POST miss, ALL fallback and duplicate input capture key. -/
theorem source_initialized_mixed_pipeline :
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock 107 source
          (RegistrationHistoryLoop.activation (endState initialized 3 1 0 [] requests) searchEnvironment context)) =
            some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract
        (RegistrationHistoryLoop.activation (endState initialized 3 1 0 [] requests) searchEnvironment context)
        after (storedRows initialized.objects.length requests) getMethod
        (endState initialized 3 1 0 [] requests).heap.length :=
  (parsed_initialized_pipeline before (some 1) requests searchEnvironment context getMethod .null 2 1 missing missing
    helper rootFound fresh prototypeReady domain).2.2.2

end HonoLean.Upstream.NodeInitialization.Examples
