import HonoLean.Upstream.NodeFirstLiteral.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeFirstLiteral.Examples

open SourceSubset ECMA2025 RegistrationHistory MethodsLoopInitial

private def getKey : JSString := [71, 69, 84]
private def xKey : JSString := [120]
private def idKey : JSString := [105, 100]
private def before : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection [], newDataObject emptyNullObject idKey (.number 7), emptyNullObject]
   functions := [⟨CreateNullObject.createProgram, []⟩]}

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported
private def objectReference : Value → Except EvalError Nat
  | .object reference => .ok reference
  | _ => .error .unsupported
private def arrayReference : Value → Except EvalError Nat
  | .array reference => .ok reference
  | _ => .error .unsupported

/-- Ordinary maps are supplied tree inputs, not a Node.insert reachability claim. -/
private def childEntry (state : State) (owner : Nat) (key : JSString) (value : Value) : Except EvalError State := do
  let children ← objectReference (← privateGet (.object owner) "children" state)
  let objects ← (setProperty propertyFuel state.objects children key value).mapError .objectError
  pure {state with objects}

private structure Prepared where
  state : State
  methods : PrivateMethodTable
  functions : FunctionTable
  splitClosure : StringFunctionClosure
  root : Nat
  child : Nat

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push : Expr) (seed : Assignment) (split : Function) (hasNext wildcard self : Bool) (path : JSString) : Except EvalError Prepared := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry before))
  let (definition, _, methods) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some result => pure result
    | none => throw .unsupported
  let (root, one) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) module
  let (child, two) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) one
  let active := {two with privates := {two.privates with names := definition.names}}
  let rootRegistered ← runSourceHistory push root [⟨getKey, .number 10, [idKey, idKey]⟩] active
  let registered ← runSourceHistory push child [⟨SearchEntry.allKey, .number 20, [idKey]⟩] rootRegistered
  let old := registered.environment
  let (_, rootSeeded) ← executeAssignment 32 defaultSplitLimit seed
    {registered with environment := [("child", .object root), ("params", .object 1)] ++ old}
  let rootSeeded := {rootSeeded with environment := old}
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit seed
    {rootSeeded with environment := [("child", .object child), ("params", .object 1)] ++ old}
  let seeded := {seeded with environment := old}
  let target := if self then root else child
  let linked ← if hasNext then childEntry seeded root xKey (.object target) else pure seeded
  let linked ← if wildcard then childEntry linked target [42] (.object target) else pure linked
  let splitClosure : StringFunctionClosure := ⟨split, module.environment, []⟩
  let functions : FunctionTable := ⟨methods.base + methods.entries.length, [splitClosure]⟩
  let state := {linked with
    thisValue := .object root
    environment := [("splitPath", .function functions.base), ("path", .string path), ("method", .string getKey)] ++ linked.environment}
  pure ⟨state, methods, functions, splitClosure, root, child⟩

private def prepare (hasNext wildcard self : Bool) (path : JSString) : Option (Except EvalError Prepared) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let seed ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let split ← parse SourceSubset.pinnedSource
  pure (prepareCore preamble fields method push seed split hasNext wildcard self path)

private def arrayNamed (state : State) (name : String) : Except EvalError (List Value) := do
  let reference ← arrayReference (← lookupVariable state name)
  match state.heap[reference]? with | some values => pure values | none => throw .invalidReference

private structure Observation where
  collector : List Value
  params : List Value
  temp : Option (List Value)
  rootParams : Value
  childParams : Value
  oldArrays : Bool
  sourceArrays : List (List Value)
  deriving Repr

private def observe (prepared : Prepared) (outcome : Result) : Except EvalError Observation := do
  let collector ← arrayNamed outcome.state "handlerSets"
  let references ← collector.mapM objectReference
  let params ← references.mapM (fun reference =>
    (getProperty propertyFuel outcome.state.objects reference HandlerRecord.paramsKey).mapError .objectError)
  let temp ← match outcome.state.environment.lookup "tempNodes" with
    | none => pure none
    | some (.array reference) => match outcome.state.heap[reference]? with
      | some values => pure (some values)
      | none => throw .invalidReference
    | _ => throw .unsupported
  let rootParams ← privateGet (.object prepared.root) "params" outcome.state
  let childParams ← privateGet (.object prepared.child) "params" outcome.state
  let arrays ← ["curNodes", "parts", "curNodesQueue"].mapM (arrayNamed outcome.state)
  pure ⟨collector, params, temp, rootParams, childParams,
    decide (outcome.state.heap.take prepared.state.heap.length = prepared.state.heap), arrays⟩

private def sourcePipeline (hasNext wildcard self : Bool) (path : JSString) : Option (Except EvalError Observation) := do
  let ready ← prepare hasNext wildcard self path
  let literal ← parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let outer ← parseForHeader NodeLoopEntry.pinnedOuterSource NodeLoopEntry.outerBindings
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let inner ← parseForHeader NodeLoopEntry.pinnedInnerSource NodeLoopEntry.innerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← ready
    let entered ← NodeLoopEntry.executePrefix startup outer iteration inner entry prepared.methods prepared.functions prepared.state
    let outcome ← executeFirst 256 prepared.methods literal entered
    observe prepared outcome

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem all_four_literal_paths_from_actual_startup :
    sourcePipeline false false false [47, 120] =
      some (.ok ⟨[], [], some [], .object 3, .object 1, true, [[.object 4], [.string [120]], []]⟩) ∧
    sourcePipeline true false false [47, 120, 47, 121] =
      some (.ok ⟨[], [], some [.object 6], .object 3, .object 3, true, [[.object 4], [.string [120], .string [121]], []]⟩) ∧
    sourcePipeline true false false [47, 120] =
      some (.ok ⟨[.object 11], [.object 12], some [], .object 3, .object 3, true, [[.object 4], [.string [120]], []]⟩) ∧
    sourcePipeline true true false [47, 120] =
      some (.ok ⟨[.object 11, .object 11], [.object 13, .object 13], some [], .object 3, .object 3, true, [[.object 4], [.string [120]], []]⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeLiteralBranch.parses_source, NodeSearchSetup.parses_source, NodeLoopEntry.parses_outer, NodeIterationSetup.parses_outer,
    NodeLoopEntry.parses_inner, NodeIterationSetup.parses_node_branch]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem self_child_reset_and_shared_repeated_record :
    sourcePipeline true false true [47, 120, 47, 121] =
      some (.ok ⟨[], [], some [.object 4], .object 3, .object 1, true, [[.object 4], [.string [120], .string [121]], []]⟩) ∧
    sourcePipeline true true true [47, 120] =
      some (.ok ⟨[.object 9, .object 9], [.object 13, .object 13], some [], .object 3, .object 1, true, [[.object 4], [.string [120]], []]⟩) ∧
    sourcePipeline true true false [] =
      some (.ok ⟨[], [], none, .object 3, .object 1, true, [[.object 4], [], []]⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeLiteralBranch.parses_source, NodeSearchSetup.parses_source, NodeLoopEntry.parses_outer, NodeIterationSetup.parses_outer,
    NodeLoopEntry.parses_inner, NodeIterationSetup.parses_node_branch]
  cbv

private def moduleState : State := NodeInitialization.preambleState before
private def sourceMethods : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def sourceDefinition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def methodClosure : PrivateMethodClosure := NodeClass.closure moduleState.environment 1
private def splitClosure : StringFunctionClosure := ⟨splitPathProgram, moduleState.environment, []⟩
private def sourceFunctions : FunctionTable := ⟨2, [splitClosure]⟩
private def one : State := NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 3)
private def two : State := NodeClass.instanceState one (some 0) moduleState.environment 1 1 (.object 3)
private def initialized : State := NodeClass.classActivation two 1
private def rootRequests : List Request := [⟨getKey, .number 10, [idKey, idKey]⟩]
private def childRequests : List Request := [⟨SearchEntry.allKey, .number 20, [idKey]⟩]
private def rootRegistered : State := endState initialized 4 0 0 [] rootRequests
private def registered : State := endState rootRegistered 6 2 1 [] childRequests
private def rootSeedBefore : State := {registered with environment := [("child", .object 4), ("params", .object 1)] ++ registered.environment}
private def rootSeeded : State := {writePrivateDataState rootSeedBefore 4 5 (.object 1) with environment := registered.environment}
private def childSeedBefore : State := {rootSeeded with environment := [("child", .object 6), ("params", .object 1)] ++ registered.environment}
private def seeded : State := {writePrivateDataState childSeedBefore 6 5 (.object 1) with environment := registered.environment}
private def linked (self : Bool) : State :=
  let target := if self then 4 else 6
  let childMap := if self then 5 else 7
  {seeded with
    objects := (seeded.objects.set 5 (newDataObject emptyNullObject xKey (.object target))).set childMap
      (if self then newDataObject (newDataObject emptyNullObject xKey (.object target)) [42] (.object target)
        else newDataObject emptyNullObject [42] (.object target))}
private def initialState (self : Bool) (path : JSString) : State :=
  {linked self with
    thisValue := .object 4
    environment := [("splitPath", .function 2), ("path", .string path), ("method", .string getKey)] ++ (linked self).environment}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem source_prepared (self : Bool) (path : JSString) :
    prepare true true self path = some (.ok ⟨initialState self path, sourceMethods, sourceFunctions, splitClosure, 4, 6⟩) := by
  have preambleRun := NodeInitialization.run_preamble before ⟨0, [], rfl, rfl, Or.inl rfl⟩
  have defineRun : definePrivateClass NodeClass.fieldsProgram [NodePrivateCall.methodProgram] moduleState
      (initialPrivateClassWorld moduleState ⟨1, []⟩) ⟨1, []⟩ = some (sourceDefinition, ⟨7⟩, sourceMethods) :=
    NodeClass.define_node moduleState ⟨1⟩ ⟨1, []⟩ (by decide)
  have first : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) moduleState = .ok (4, one) :=
    NodeClass.instantiate_node moduleState (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have second : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) one = .ok (6, two) :=
    NodeClass.instantiate_node one (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have rootSeed : Seed initialized 4 1 0 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have childSeed : Seed rootRegistered 6 1 2 1 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have rootHistory : runSourceHistory NodeMethodsPush.expression 4 [⟨getKey, .number 10, [idKey, idKey]⟩]
      {two with privates := {two.privates with names := sourceDefinition.names}} = .ok rootRegistered :=
    run_source_history initialized 4 1 0 0 [] rootRequests rootSeed
  have childHistory : runSourceHistory NodeMethodsPush.expression 6 [⟨SearchEntry.allKey, .number 20, [idKey]⟩] rootRegistered = .ok registered :=
    run_source_history rootRegistered 6 1 2 1 [] childRequests childSeed
  have rootWritable : NodePrivateWrite.Writable rootSeedBefore 4 5 (.object 3) :=
    ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  have childWritable : NodePrivateWrite.Writable childSeedBefore 6 5 (.object 3) :=
    ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  have rootWrite := NodePrivateWrite.run_parameter rootSeedBefore 4 5 (.object 3) (.object 1) rootWritable ⟨rfl, rfl⟩
  have childWrite := NodePrivateWrite.run_parameter childSeedBefore 6 5 (.object 3) (.object 1) childWritable ⟨rfl, rfl⟩
  dsimp only [moduleState] at defineRun first
  dsimp only [rootSeedBefore] at rootWrite
  dsimp only [childSeedBefore, rootSeeded, rootSeedBefore] at childWrite
  simp only [prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source]
  dsimp only [bind, pure, Option.bind]
  unfold prepareCore
  rw [preambleRun]
  dsimp only [normalState, bind, pure, Except.bind, Except.pure]
  rw [defineRun]
  dsimp only
  rw [first]
  dsimp only
  rw [second]
  dsimp only
  rw [rootHistory]
  dsimp only
  rw [childHistory]
  dsimp only
  rw [rootWrite]
  dsimp only
  rw [childWrite]
  cases self <;> cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem initial_inputs (self : Bool) (path : JSString) :
    NodeSearchSetup.Inputs (initialState self path) sourceMethods sourceFunctions splitClosure 4 5 2 3 (.object 1) path := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, by decide, by decide, rfl⟩
  · refine ⟨rfl, ?_, ?_⟩
    · cases self <;> exact ⟨⟨[], some 0, true⟩, rfl⟩
    · cases self <;> refine ⟨_, rfl, ?_⟩ <;> rfl
  · change (1 : Nat) ≤ 1
    decide

private def initial : State := initialState false [47, 120]
private def record : Record :=
  ⟨11, HandlerRecord.innerRecord (.number 20) 5 2, 5,
    ⟨[idKey], fun _ => .undefined, fun _ => .undefined⟩⟩
private def records : List Record := [record]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem initial_objects :
    initial.objects = [objectPrototypeProjection [], newDataObject emptyNullObject idKey (.number 7), emptyNullObject, emptyNullObject,
      ⟨[], some 0, true⟩, newDataObject emptyNullObject xKey (.object 6), ⟨[], some 0, true⟩,
      newDataObject emptyNullObject [42] (.object 6), HandlerRecord.outerRecord getKey 9, HandlerRecord.innerRecord (.number 10) 4 1,
      HandlerRecord.outerRecord SearchEntry.allKey 11, HandlerRecord.innerRecord (.number 20) 5 2] := by cbv

private theorem protected_cell (reference : Nat) (bound : reference < 12) (different : reference ≠ 11) :
    Protected initial records reference := by
  refine ⟨?_, ?_⟩
  · rw [initial_objects]; exact bound
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    exact different

private theorem parent_zero (reference : Nat) (object : OrdinaryObject)
    (found : initial.objects[reference]? = some object) (parent : Nat) (prototype : object.prototype = some parent) : parent = 0 := by
  have member := List.mem_of_getElem? found
  rw [initial_objects] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [objectPrototypeProjection, newDataObject, emptyNullObject, HandlerRecord.outerRecord, HandlerRecord.innerRecord] at prototype <;> exact prototype.symm

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem raw_union : Uncollected initial methodClosure.environment [.object 10, .object 10] getKey 1 records 3 := by
  refine {
    allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    capacity := by decide
    closed := ?_
    protectedParents := ?_
    nodeProtected := protected_cell 3 (by decide) (by decide)
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    rw [initial_objects]
    decide
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    exact protected_cell 0 (by decide) (by decide)
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    refine {
      found := rfl
      possibleKeys := rfl
      keysFound := rfl
      resettable := ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      unique := by decide
      legalKeys := by decide
      keyBound := by decide
      parameterUndefined := by intro key _; rfl
      nodeReads := ?_ }
    intro key member
    have same : key = idKey := by simpa [record] using member
    subst key
    rfl
  · intro current member parent prototype
    have same : current = record := by simpa [records] using member
    subst current
    have same : parent = 0 := by simpa [record, HandlerRecord.innerRecord] using prototype.symm
    subst parent
    exact protected_cell 0 (by decide) (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 := by change count < 2 at inside; omega
    rcases cases with rfl | rfl <;>
      refine ⟨10, .object 11, rfl, protected_cell 10 (by decide) (by decide), ?_, ?_⟩
    all_goals first
      | exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      | exact fun _ => ⟨record, by simp [records], rfl⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private def shared_ready : Wildcard initial sourceMethods methodClosure 4 6 6 1 1 7 1 3 getKey records := by
  let storage : Storage initial methodClosure 6 1 :=
    ⟨2, [.object 10], ⟨⟨[], some 0, true⟩, rfl⟩, rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl, by decide⟩
  exact ⟨⟨rfl, by decide, by decide, rfl, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl,
    storage, storage, rfl, rfl, raw_union⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem shared_child : Child initial 4 5 6 1 [47, 120] (.object 1) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩⟩

/-- A genuine initial raw union domain has repeated actual method rows. The
source allocates its collector later, so neither a future Layout nor a guessed
collector slot occurs in this source-prepared witness. -/
theorem source_prepared_shared_union_has_universal_contract :
    SourceBound ∧ ∃ prepared after,
      prepare true true false [47, 120] = some (.ok prepared) ∧
      sourceFirst 203 prepared.methods prepared.functions prepared.state =
        some (.ok ⟨NodeLoopEntry.result prepared.state 4 5 3 [47, 120], after⟩) ∧
      Contract prepared.state methodClosure 4 1 3 (.object 1) [47, 120] getKey
        ⟨NodeLoopEntry.result prepared.state 4 5 3 [47, 120], after⟩ := by
  obtain ⟨bound, after, run, contract⟩ := wildcard_satisfies initial sourceMethods sourceFunctions splitClosure methodClosure
    4 5 6 6 1 2 1 3 7 1 (.object 1) (.object 1) [47, 120] getKey records (initial_inputs false [47, 120])
    rfl rfl rfl shared_child shared_ready
  exact ⟨bound, ⟨initial, sourceMethods, sourceFunctions, splitClosure, 4, 6⟩, after, source_prepared false [47, 120], run, contract⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem self_child : Child (initialState true [47, 120, 47, 121]) 4 5 4 1 [47, 120, 47, 121] (.object 1) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩⟩

/-- The self-child starts with stale A, but startup resets that same owner.
The universal proof derives the postreset old value before source109 writes;
it never assumes the pre-startup value survived the reset. -/
theorem source_prepared_self_child_has_universal_nonlast_contract :
    SourceBound ∧ ∃ prepared after,
      prepare true true true [47, 120, 47, 121] = some (.ok prepared) ∧
      sourceFirst 200 prepared.methods prepared.functions prepared.state =
        some (.ok ⟨NodeLoopEntry.result prepared.state 4 5 3 [47, 120, 47, 121], after⟩) ∧
      Contract prepared.state methodClosure 4 1 3 (.object 1) [47, 120, 47, 121] getKey
        ⟨NodeLoopEntry.result prepared.state 4 5 3 [47, 120, 47, 121], after⟩ := by
  obtain ⟨bound, after, run, contract⟩ := nonlast_satisfies (initialState true [47, 120, 47, 121]) sourceMethods sourceFunctions splitClosure methodClosure
    4 5 4 1 2 3 (.object 1) (.object 1) [47, 120, 47, 121] getKey (initial_inputs true [47, 120, 47, 121])
    rfl rfl (by decide) (by decide) self_child
  exact ⟨bound, ⟨initialState true [47, 120, 47, 121], sourceMethods, sourceFunctions, splitClosure, 4, 6⟩, after,
    source_prepared true [47, 120, 47, 121], run, contract⟩

end HonoLean.Upstream.NodeFirstLiteral.Examples
