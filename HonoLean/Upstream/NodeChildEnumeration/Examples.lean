import HonoLean.Upstream.NodeChildEnumeration.Composition

namespace HonoLean.Upstream.NodeChildEnumeration.Examples

open SourceSubset ECMA2025

private def hiddenKey : JSString := [104]
private def hidden : OrdinaryObject := ⟨[(hiddenKey, .accessor .unsupported .unsupported false true)], none, true⟩
private def entryObject (key : JSString) : OrdinaryObject := ⟨[(key, .data (.number 0) false true false)], none, false⟩
private def accessorObject : OrdinaryObject := ⟨[([], .accessor .unsupported .unsupported true false)], none, false⟩
private def many : OrdinaryObject :=
  ⟨[([], .data .undefined true true true), ([95], .data .null true true true),
    ([109], .data (.number 0) true true true), ([112, 97, 114, 97, 109, 115], .data (.boolean false) true true true),
    ([48], .data (.string []) true true true)], none, true⟩
private def path : JSString := [47, 120, 47]
private def cells (entries : List (Option Value)) : IndexedArray :=
  ⟨entries.length, fun index => entries[index]?.getD none⟩
private def slots (array : IndexedArray) : List (Option Value) := (List.range array.length).map array.own
private def heapSlots (state : IndexedState) : List (List (Option Value)) := state.heap.map slots
private def tempCells : List (Option Value) := [none, some .undefined]

private def initial (object : OrdinaryObject) (params : Value := .object 1) (input : JSString := path)
    (queue : Nat := 1) (queued : List (Option Value) := []) : ForInState :=
  {ambient :=
    {environment := [("ambientCache", .number 55)]
     objects := [emptyNullObject, object, newDataObject emptyNullObject [111, 108, 100] (.number 7)]
     functions := [⟨⟨"sample", .number 11⟩, []⟩]
     sets := [[[120]]]
     thisValue := .object 2
     privates := ⟨NodeClass.names 1,
       [(0, [(2, .data (.object 1)), (5, .data (.object 2)), (6, .method (.function 0))])]⟩}
   regexp :=
    {arrays :=
      {environment := [("child", .object 0), ("params", params), ("m", .array 0), ("curNodesQueue", .array queue),
        ("componentCount", .number 777), ("targetCurNodes", .number 888), ("_", .string [111, 117, 116, 101, 114])]
       heap := [ofList [.string input], cells queued, cells tempCells]}
     regexps := [⟨120, 37⟩]}}

private def minimal : ForInState :=
  {initial hidden with
    ambient := { (initial hidden).ambient with privates := ⟨NodeClass.names 1,
      [(0, [(2, .data (.object 1)), (5, .method (.function 0)), (6, .method (.function 0))])]⟩}
    regexp := {arrays := {environment := [("child", .object 0)], heap := []}, regexps := [⟨120, 37⟩]}}

private def normalState : ForInCompletion → Except EvalError ForInState
  | .normal state => .ok state
  | _ => .error .unsupported
private abbrev Observation := Bool × Option PrivateElement × Value × List (List (Option Value)) ×
  List UnitRegExpCell × List (List Nat) × Bool × Option PrivateElement
private def observe (before after : ForInState) (owner : Nat := 0) : Except EvalError Observation := do
  let children ← privateGet (.object owner) "children" (forInStateView after)
  pure (decide (after.regexp.arrays.environment = before.regexp.arrays.environment),
    (after.ambient.privates.elements.lookup owner).bind (List.lookup 5), children, heapSlots after.regexp.arrays,
    after.regexp.regexps, after.regexp.executions.map UnitExecution.positions,
    decide (after.ambient.objects = before.ambient.objects), (after.ambient.privates.elements.lookup owner).bind (List.lookup 6))
private def sourceObserved (before : ForInState) : Option (Except EvalError Observation) :=
  (sourceLoop 120 before).map fun result => do
    let after ← normalState (← result)
    observe before after

theorem empty_without_body_bindings_returns_unchanged :
    sourceLoop 120 minimal = some (.ok (.normal minimal)) := by
  simp only [sourceLoop, parses_source]
  cbv

theorem enumerable_empty_name_and_falsy_data_enter :
    sourceObserved (initial (entryObject [])) = some (.ok
      (true, some (.data (.object 1)), .object 1,
        [[some (.string path)], [none, none, some (.array 4)], tempCells,
         [some (.string [47]), some (.string [47])], [some (.object 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0, 2]], true, some (.method (.function 0)))) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem unused_names_and_numeric_keys_have_identical_effects :
    ([[], [95], [109], [112, 97, 114, 97, 109, 115], [48], [95, 95, 112, 114, 111, 116, 111, 95, 95]] : List JSString).all
      (fun key => match sourceObserved (initial (entryObject key)) with
        | some (.ok (scope, params, children, heap, regexps, executions, objects, method)) =>
          scope && params == some (.data (.object 1)) && children == .object 1 &&
          heap == [[some (.string path)], [none, none, some (.array 4)], tempCells,
            [some (.string [47]), some (.string [47])], [some (.object 0)]] &&
          regexps.length == 2 && executions == [[0, 2]] && objects && method == some (.method (.function 0))
        | _ => false) = true := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem enumerable_accessor_does_not_call_getter :
    sourceObserved (initial accessorObject) = sourceObserved (initial (entryObject [])) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem multiple_keys_execute_one_body_and_restore_scope :
    sourceObserved (initial many) = sourceObserved (initial (entryObject [])) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem params_can_alias_children_or_owner :
    sourceObserved (initial (entryObject []) (.object 0)) = some (.ok
      (true, some (.data (.object 0)), .object 1,
        [[some (.string path)], [none, none, some (.array 4)], tempCells,
         [some (.string [47]), some (.string [47])], [some (.object 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0, 2]], true, some (.method (.function 0)))) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem existing_queue_self_target_and_m_aliases_are_preserved :
    sourceObserved (initial (entryObject []) (.object 1) [47] 1 [none, some (.array 1)]) = some (.ok
      (true, some (.data (.object 1)), .object 1,
        [[some (.string [47])], [none, some (.array 1), some (.object 0)], tempCells, [some (.string [47])]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[0]], true, some (.method (.function 0)))) ∧
    sourceObserved (initial (entryObject []) (.object 1) [] 0) = some (.ok
      (true, some (.data (.object 1)), .object 1,
        [[some (.array 4)], [], tempCells, [], [some (.object 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[]], true, some (.method (.function 0)))) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

theorem readonly_params_fails_before_count_when_entered :
    sourceLoop 120 {minimal with
      ambient := {minimal.ambient with objects :=
        [emptyNullObject, entryObject [], newDataObject emptyNullObject [111, 108, 100] (.number 7)]}
      regexp := {arrays := {environment := [("child", .object 0), ("params", .object 1)]}}} =
        some (.error .privateReadOnly) := by
  simp only [sourceLoop, parses_source]
  cbv

theorem zero_and_raw_utf16_counts_stay_inside_scope :
    sourceObserved (initial (entryObject []) (.object 1) []) = some (.ok
      (true, some (.data (.object 1)), .object 1,
        [[some (.string [])], [some (.array 4)], tempCells, [], [some (.object 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[]], true, some (.method (.function 0)))) ∧
    sourceObserved (initial (entryObject []) (.object 1) [55296, 47, 945, 47, 56320]) = some (.ok
      (true, some (.data (.object 1)), .object 1,
        [[some (.string [55296, 47, 945, 47, 56320])], [none, none, some (.array 4)], tempCells,
         [some (.string [47]), some (.string [47])], [some (.object 0)]],
        [⟨120, 37⟩, ⟨47, 0⟩], [[1, 3]], true, some (.method (.function 0)))) := by
  simp only [sourceObserved, sourceLoop, parses_source]
  cbv

private theorem minimal_children : ChildrenInputs minimal 0 2 1 hidden :=
  ⟨rfl, ⟨emptyNullObject, rfl⟩, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, by change (hidden.own.map Prod.fst).Nodup; decide⟩
private theorem hidden_nonEnumerable : NoEnumerable hidden := by
  intro key descriptor found
  by_cases same : key = hiddenKey
  · subst key
    have equal : descriptor = .accessor .unsupported .unsupported false true := by simpa [hidden, List.lookup] using found.symm
    subst descriptor
    rfl
  · simp [hidden, List.lookup, beq_false_of_ne same] at found

/-- This applies the universal empty theorem with a readonly METHOD params
slot and without any m/params/queue binding. Body readiness is not smuggled in. -/
theorem empty_universal_domain_needs_no_params_readiness :
    sourceLoop 120 minimal = some (.ok (.normal minimal)) ∧
    EmptyContract minimal minimal 0 2 1 hidden ∧
    minimal.regexp.arrays.environment.lookup "m" = none ∧
    minimal.regexp.arrays.environment.lookup "params" = none ∧
    minimal.regexp.arrays.environment.lookup "curNodesQueue" = none := by
  obtain ⟨_, run, contract⟩ := source_empty_satisfies 0 minimal 0 2 1 hidden minimal_children hidden_nonEnumerable
  exact ⟨run, contract, rfl, rfl, rfl⟩

private theorem entered_children : ChildrenInputs (initial many) 0 2 1 many :=
  ⟨rfl, ⟨emptyNullObject, rfl⟩, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, by change (many.own.map Prod.fst).Nodup; decide⟩
private theorem entered_inputs : BodyInputs (initial many) 0 2 5 (.object 2) (.object 1) 0 1
    (ofList [.string path]) (ofList []) path := by
  refine ⟨⟨rfl, ⟨emptyNullObject, rfl⟩, ⟨_, rfl, rfl⟩⟩, rfl, by decide,
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 1 ≤ 4294967295; decide⟩,
    ⟨rfl, rfl, rfl, ofList_wellFormed _, by change 0 ≤ 4294967295; decide, by decide⟩, Or.inl rfl⟩

/-- The full source theorem is instantiated from before-loop facts. The
unused key ranges over every legal complete order, not just stored-list order. -/
theorem entered_universal_contract_covers_every_legal_order :
    ∃ after, sourceLoop 120 (initial many) = some (.ok (.normal after)) ∧
      EnteredContract (initial many) after 0 2 1 5 many (.object 2) (.object 1) 1 (ofList []) path ∧
      (∀ keys, LegalForInOrder many keys → executeForInKeys 119 "_" body keys (initial many) = .ok after) := by
  exact (source_entered_satisfies 0 (initial many) 0 2 1 5 many (.object 2) (.object 1) 0 1
    (ofList [.string path]) (ofList []) path entered_children entered_inputs []
    (.data .undefined true true true) rfl rfl).2

private def classBefore : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection [], emptyNullObject]
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def coreNormal : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported
private def objectRef : Value → Except EvalError Nat
  | .object reference => .ok reference
  | _ => .error .unsupported
private def classPipeline : Option (Except EvalError Observation) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let arrays ← parseBlock "const m = ['a/b']\nconst curNodesQueue = []\n" []
  let loop ← parseForInSequence pinnedSource bindings privateNames
  pure do
    let module ← coreNormal (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry classBefore))
    let (definition, _, _) ← match definePrivateClass fields [method] module (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
      | some result => pure result | none => throw .unsupported
    let (owner, created) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) module
    let active := NodeClass.classActivation created 1
    let children ← objectRef (← privateGet (.object owner) "children" active)
    -- This map entry is an explicit tree input, not an insert reachability proof.
    let objects ← (setProperty propertyFuel active.objects children [] (.object owner)).mapError .objectError
    let ready ← coreNormal (← execute 32 defaultSplitLimit arrays {active with objects})
    let entry := {ready with environment := [("child", .object owner), ("params", .object children)] ++ ready.environment}
    let before : ForInState := ⟨entry, ⟨liftState entry, [], []⟩⟩
    let after ← normalState (← executeForInSequence 120 loop before)
    observe before after owner

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- Actual parsed preamble/class installation/instance supplies the branded
DATA fields. Params is the existing children object; no params slot is staged. -/
theorem source_class_instance_enters_actual_loop :
    classPipeline = some (.ok
      (true, some (.data (.object 4)), .object 4,
        [[], [], [some (.string [97, 47, 98])], [none, some (.array 5)], [some (.string [47])], [some (.object 3)]],
        [⟨47, 0⟩], [[1]], true, some (.method (.function 1)))) := by
  simp only [classPipeline, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method, parses_source]
  cbv

/-- info: 'HonoLean.Upstream.NodeChildEnumeration.source_empty_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeChildEnumeration.source_empty_satisfies

/-- info: 'HonoLean.Upstream.NodeChildEnumeration.source_entered_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeChildEnumeration.source_entered_satisfies

end HonoLean.Upstream.NodeChildEnumeration.Examples
