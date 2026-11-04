import HonoLean.Upstream.NodeIterationSetup.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeIterationSetup.Examples

open SourceSubset ECMA2025 RegistrationHistory

private def getKey : JSString := [71, 69, 84]
private def partKey : JSString := [120]
private def unusedKey : JSString := [117]
private def tailKey : JSString := [122]
private def idKey : JSString := [105, 100]
private def parts (terminal : Bool) : List JSString :=
  if terminal then [unusedKey, partKey] else [unusedKey, partKey, tailKey]
private def nodes : List Nat := [4, 6]
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
private def property (state : State) (reference : Nat) (key : JSString) : Except EvalError Value :=
  (getProperty propertyFuel state.objects reference key).mapError .objectError

/-- These ordinary child-map inputs remain outside Node.insert traversal. -/
private def childEntry (state : State) (owner : Nat) (key : JSString) (value : Value) : Except EvalError State := do
  let children ← objectReference (← privateGet (.object owner) "children" state)
  let objects ← (setProperty propertyFuel state.objects children key value).mapError .objectError
  pure {state with objects}

private def firstHandler (state : State) (owner : Nat) : Except EvalError Value := do
  let methods ← arrayReference (← privateGet (.object owner) "methods" state)
  let row ← match state.heap[methods]? with
    | some (.object reference :: _) => pure reference
    | _ => throw .invalidReference
  property state row getKey

/-- The arrays are supplied inputs, constructed by admitted array-literal
execution. This does not claim that path splitting/traversal produced them. -/
private def arraysSource (terminal : Bool) : String :=
  if terminal then "const parts = ['u', 'x']\nconst curNodes = [firstOwner, selectedOwner]"
  else "const parts = ['u', 'x', 'z']\nconst curNodes = [firstOwner, selectedOwner]"
private def arraysProgram (terminal : Bool) : List Stmt :=
  [.declare "parts" (.arrayLiteral ((parts terminal).map (fun text => (false, Expr.string text)))),
   .declare "curNodes" (.arrayLiteral [(false, .variable "firstOwner"), (false, .variable "selectedOwner")])]
private def prefixProgram : Expr := .call (.variable "handlerSets") "push" [.variable "existingHandler"]
private theorem parses_arrays (terminal : Bool) :
    parseBlock (arraysSource terminal) ["firstOwner", "selectedOwner"] = some (arraysProgram terminal) := by
  cases terminal <;> cbv
private theorem parses_prefix :
    parseExpression "handlerSets.push(existingHandler)" ["handlerSets", "existingHandler"] = some prefixProgram := by cbv

private structure Prepared where
  state : State
  table : PrivateMethodTable
  definition : SelectedPrivateClass
  root : Nat
  parent : Nat
  next : Nat
  collector : Nat

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push : Expr) (seed : Assignment) (arrays collector : List Stmt) (prefixPush : Expr)
    (hasNext hasWildcard shared livePrefix : Bool) : Except EvalError Prepared := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry before))
  let (definition, _, table) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some result => pure result
    | none => throw .unsupported
  let (root, one) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) module
  let (parent, two) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) one
  let (next, three) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) two
  let (wildcard, four) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) three
  let active := {four with privates := {four.privates with names := definition.names}}
  let directRegistered ← runSourceHistory push next [⟨getKey, .number 10, [idKey, idKey]⟩] active
  let registered ← runSourceHistory push wildcard [⟨SearchEntry.allKey, .number 20, [idKey]⟩] directRegistered
  let old := registered.environment
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit seed
    {registered with environment := [("child", .object parent), ("params", .object 1)] ++ old}
  let seeded := {seeded with environment := old}
  let linked ← if hasNext then childEntry seeded parent partKey (.object next) else pure seeded
  let linked ← if hasWildcard then childEntry linked next [42] (.object (if shared then next else wildcard)) else pure linked
  let supplied ← normalState (← execute 32 defaultSplitLimit arrays
    {linked with environment := [("firstOwner", .object root), ("selectedOwner", .object parent)] ++ linked.environment})
  let parts ← lookupVariable supplied "parts"
  let curNodes ← lookupVariable supplied "curNodes"
  let caller := [("parts", parts), ("curNodes", curNodes), ("method", .string getKey)] ++ linked.environment
  let collected ← normalState (← execute 32 defaultSplitLimit collector
    {supplied with environment := caller, thisValue := .object root})
  let collector ← arrayReference (← lookupVariable collected "handlerSets")
  let ready ← if livePrefix then do
    let existing ← firstHandler collected next
    let (_, after) ← evalExpression 32 defaultSplitLimit prefixPush
      {collected with environment := ("existingHandler", existing) :: collected.environment}
    pure {after with environment := collected.environment}
    else pure collected
  pure ⟨ready, table, definition, root, parent, next, collector⟩

/-- Private state is source-installed; the earlier202 params write runs under
a separate supplied activation. No part/last/temp/node binding is staged. -/
private def prepare (hasNext terminal hasWildcard shared livePrefix : Bool) : Option (Except EvalError Prepared) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let seed ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let arrays ← parseBlock (arraysSource terminal) ["firstOwner", "selectedOwner"]
  let collector ← parseBlock SearchEntry.pinnedCollectorSource []
  let prefixPush ← parseExpression "handlerSets.push(existingHandler)" ["handlerSets", "existingHandler"]
  pure (prepareCore preamble fields method push seed arrays collector prefixPush hasNext hasWildcard shared livePrefix)

private structure Observation where
  collector : List Value
  handlers : List Value
  values : List Value
  params : List Value
  queue : List Value
  length : Value
  part : Value
  last : Value
  node : Value
  next : Value
  nextParams : Value
  queueFresh : Bool
  callerScope : Bool
  runtimeThis : Bool
  newObjects : Nat
  deriving Repr

private def observe (prepared : Prepared) (inner after : State) : Except EvalError Observation := do
  let entries ← match after.heap[prepared.collector]? with | some entries => pure entries | none => throw .invalidReference
  let handlers ← entries.mapM fun value => do property after (← objectReference value) HandlerRecord.handlerKey
  let params ← entries.mapM fun value => do property after (← objectReference value) HandlerRecord.paramsKey
  let values ← params.mapM fun value => do property after (← objectReference value) idKey
  let queueRef ← arrayReference (← lookupVariable after "tempNodes")
  let queue ← match after.heap[queueRef]? with | some entries => pure entries | none => throw .invalidReference
  let length ← lookupVariable after "len"
  let part ← lookupVariable after "part"
  let last ← lookupVariable after "isLast"
  let node ← lookupVariable after "node"
  let next ← lookupVariable after "nextNode"
  let nextParams ← privateGet (.object prepared.next) "params" after
  pure ⟨entries, handlers, values, params, queue, length, part, last, node, next, nextParams,
    decide (queueRef = prepared.state.heap.length) && (prepared.state.heap[queueRef]?).isNone,
    decide (after.environment = ("nextNode", next) :: ("node", node) :: inner.environment),
    decide (after.thisValue = .object prepared.root), after.objects.length - prepared.state.objects.length⟩

private def sourcePipeline (hasNext terminal hasWildcard shared livePrefix : Bool) (i j : Nat) :
    Option (Except EvalError Observation) := do
  let prepared ← prepare hasNext terminal hasWildcard shared livePrefix
  let search ← parseBlock pinnedSearchSource lengthBindings
  let iteration ← parseBlock pinnedIterationSource outerBindings
  let entry ← parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← prepared
    let lengths ← normalState (← execute 32 defaultSplitLimit search prepared.state)
    let outer ← normalState (← execute 32 defaultSplitLimit iteration (outerActivation lengths i))
    let inner := innerActivation outer j
    let after ← normalState (← executePrivateControl 128 defaultSplitLimit prepared.table entry inner)
    observe prepared inner after

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem all_four_source_paths_at_nonzero_indices :
    sourcePipeline false true true false false 1 1 =
      some (.ok ⟨[], [], [], [], [], .number 2, .string partKey, .boolean true, .object 6, .undefined,
        .object 3, true, true, true, 0⟩) ∧
    sourcePipeline true false true false false 1 1 =
      some (.ok ⟨[], [], [], [], [.object 8], .number 3, .string partKey, .boolean false, .object 6, .object 8,
        .object 1, true, true, true, 0⟩) ∧
    sourcePipeline true true false false false 1 1 =
      some (.ok ⟨[.object 13], [.number 10], [.number 7], [.object 16], [], .number 2, .string partKey,
        .boolean true, .object 6, .object 8, .object 1, true, true, true, 1⟩) ∧
    sourcePipeline true true true false false 1 1 =
      some (.ok ⟨[.object 15, .object 13], [.number 20, .number 10], [.number 7, .number 7],
        [.object 16, .object 17], [], .number 2, .string partKey, .boolean true, .object 6, .object 8,
        .object 1, true, true, true, 2⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, parses_arrays, SearchEntry.parses_collector,
    parses_prefix, parses_length, parses_outer, parses_node_branch]
  cbv
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem shared_target_and_live_prefix_have_fresh_params :
    sourcePipeline true true true true true 1 1 =
      some (.ok ⟨[.object 13, .object 13, .object 13], [.number 10, .number 10, .number 10],
        [.number 7, .number 7, .number 7], [.object 17, .object 17, .object 17], [], .number 2,
        .string partKey, .boolean true, .object 6, .object 8, .object 1, true, true, true, 2⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, parses_arrays, SearchEntry.parses_collector,
    parses_prefix, parses_length, parses_outer, parses_node_branch]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem indices_select_different_actual_entries :
    sourcePipeline true true true false false 0 1 =
      some (.ok ⟨[], [], [], [], [], .number 2, .string unusedKey, .boolean false, .object 6, .undefined,
        .object 3, true, true, true, 0⟩) ∧
    sourcePipeline true true true false false 1 0 =
      some (.ok ⟨[], [], [], [], [], .number 2, .string partKey, .boolean true, .object 4, .undefined,
        .object 3, true, true, true, 0⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, parses_arrays, SearchEntry.parses_collector,
    parses_prefix, parses_length, parses_outer, parses_node_branch]
  cbv
  exact ⟨rfl, rfl⟩

/- One compact initial endpoint, connected to actual parsed preparation once.
No field below runs the source preparation evaluator again. -/
private def moduleState : State := NodeInitialization.preambleState before
private def closure : PrivateMethodClosure := NodeClass.closure moduleState.environment 1
private def sourceTable : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def sourceDefinition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def one : State := NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 3)
private def two : State := NodeClass.instanceState one (some 0) moduleState.environment 1 1 (.object 3)
private def three : State := NodeClass.instanceState two (some 0) moduleState.environment 1 1 (.object 3)
private def four : State := NodeClass.instanceState three (some 0) moduleState.environment 1 1 (.object 3)
private def initialized : State := NodeClass.classActivation four 1
private def directRequests : List Request := [⟨getKey, .number 10, [idKey, idKey]⟩]
private def wildcardRequests : List Request := [⟨SearchEntry.allKey, .number 20, [idKey]⟩]
private def directRegistered : State := endState initialized 8 4 0 [] directRequests
private def registered : State := endState directRegistered 10 6 1 [] wildcardRequests
private def seedBefore : State :=
  {registered with environment := [("child", .object 6), ("params", .object 1)] ++ registered.environment}
private def seeded : State :=
  {writePrivateDataState seedBefore 6 5 (.object 1) with environment := registered.environment}
private def parentLinked : State :=
  {seeded with objects := seeded.objects.set 7 (newDataObject emptyNullObject partKey (.object 8))}
private def linked : State :=
  {parentLinked with objects := parentLinked.objects.set 9 (newDataObject emptyNullObject [42] (.object 8))}
private def caller : List (String × Value) :=
  [("parts", .array 10), ("curNodes", .array 11), ("method", .string getKey)] ++ linked.environment
private def entryState : State :=
  {linked with
    environment := ("handlerSets", .array 12) :: caller
    thisValue := .object 4
    heap := linked.heap ++ [(parts true).map Value.string, nodes.map Value.object, [.object 13]]}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem source_prepared :
    prepare true true true true true = some (.ok ⟨entryState, sourceTable, sourceDefinition, 4, 6, 8, 12⟩) := by
  have preambleRun := NodeInitialization.run_preamble before ⟨0, [], rfl, rfl, Or.inl rfl⟩
  have defineRun : definePrivateClass NodeClass.fieldsProgram [NodePrivateCall.methodProgram] moduleState
      (initialPrivateClassWorld moduleState ⟨1, []⟩) ⟨1, []⟩ = some (sourceDefinition, ⟨7⟩, sourceTable) :=
    NodeClass.define_node moduleState ⟨1⟩ ⟨1, []⟩ (by decide)
  have first : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) moduleState = .ok (4, one) :=
    NodeClass.instantiate_node moduleState (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have second : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) one = .ok (6, two) :=
    NodeClass.instantiate_node one (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have third : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) two = .ok (8, three) :=
    NodeClass.instantiate_node two (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have fourth : instantiatePrivateClass 64 defaultSplitLimit sourceDefinition (some 0) three = .ok (10, four) :=
    NodeClass.instantiate_node three (some 0) moduleState.environment 1 1 (.object 3) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have directSeed : Seed initialized 8 1 4 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have wildcardSeed : Seed directRegistered 10 1 6 1 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have directRun : runSourceHistory NodeMethodsPush.expression 8
      [⟨getKey, .number 10, [idKey, idKey]⟩]
      {four with privates := {four.privates with names := sourceDefinition.names}} = .ok directRegistered :=
    run_source_history initialized 8 1 4 0 [] directRequests directSeed
  have wildcardRun : runSourceHistory NodeMethodsPush.expression 10
      [⟨SearchEntry.allKey, .number 20, [idKey]⟩] directRegistered = .ok registered :=
    run_source_history directRegistered 10 1 6 1 [] wildcardRequests wildcardSeed
  have writable : NodePrivateWrite.Writable seedBefore 6 5 (.object 3) :=
    ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  have seedRun := NodePrivateWrite.run_parameter seedBefore 6 5 (.object 3) (.object 1) writable ⟨rfl, rfl⟩
  dsimp only [moduleState] at defineRun first
  dsimp only [seedBefore] at seedRun
  simp only [prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, parses_arrays,
    SearchEntry.parses_collector, parses_prefix]
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
  rw [third]
  dsimp only
  rw [fourth]
  dsimp only
  rw [directRun]
  dsimp only
  rw [wildcardRun]
  dsimp only
  rw [seedRun]
  cbv

theorem initial_state_does_not_supply_generated_bindings :
    (["len", "partOffsets", "part", "isLast", "tempNodes", "node", "nextNode", "i", "j"].all
      (fun name => (entryState.environment.lookup name).isNone)) = true := by cbv

private def record : MethodsLoopInitial.Record :=
  ⟨13, HandlerRecord.innerRecord (.number 10) 8 1, 8,
    ⟨[idKey], fun _ => .undefined, fun _ => .number 7⟩⟩
private def records : List MethodsLoopInitial.Record := [record]
private def origin : State := NodePrivateCall.bodyState entryState closure (.object 4) 12 8 getKey 1 .undefined

private theorem entry_objects :
    origin.objects = [objectPrototypeProjection [], newDataObject emptyNullObject idKey (.number 7),
      emptyNullObject, emptyNullObject, ⟨[], some 0, true⟩, emptyNullObject,
      ⟨[], some 0, true⟩, newDataObject emptyNullObject partKey (.object 8),
      ⟨[], some 0, true⟩, newDataObject emptyNullObject [42] (.object 8),
      ⟨[], some 0, true⟩, emptyNullObject,
      HandlerRecord.outerRecord getKey 13, HandlerRecord.innerRecord (.number 10) 8 1,
      HandlerRecord.outerRecord SearchEntry.allKey 15, HandlerRecord.innerRecord (.number 20) 9 2] := by cbv

private theorem parent_zero (reference : Nat) (object : OrdinaryObject)
    (found : origin.objects[reference]? = some object) (parent : Nat)
    (prototype : object.prototype = some parent) : parent = 0 := by
  have member := List.mem_of_getElem? found
  rw [entry_objects] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (Option.some.inj prototype).symm | cases prototype

private theorem safeReference (reference : Nat) (bound : reference < 16) (different : reference ≠ 13) :
    MethodsLoopInitial.Protected origin records reference := by
  refine ⟨?_, ?_⟩
  · rw [entry_objects]; exact bound
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    exact different

private theorem inputs : Inputs entryState 10 11 (parts true) nodes 1 1 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩

private theorem initial_child : InitialChild entryState (parts true) nodes 1 1 7 8 4 1 12 1 getKey (.object 3) := by
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩

private theorem initial_layout :
    MethodsLoopInitial.Layout origin [.object 12, .object 12] getKey 12 1 records .undefined 1 [.object 13] := by
  refine {
    collectorBinding := rfl, parameterBinding := rfl, nodeBinding := rfl, allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    collectorFound := rfl, capacity := by decide
    closed := ?_, protectedParents := ?_
    nodeProtected := safeReference 1 (by decide) (by decide)
    parameterProtected := ?_, recordsFound := ?_, handlerParents := ?_, rowChoices := ?_ }
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    rw [entry_objects]
    decide
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    exact safeReference 0 (by decide) (by decide)
  · intro reference equal
    cases equal
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    refine {
      found := rfl, possibleKeys := rfl, keysFound := rfl, separate := by decide
      resettable := ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      unique := by decide, legalKeys := by decide, keyBound := by decide, reads := ?_ }
    intro key used
    have same : key = idKey := by simpa [record] using used
    subst key
    exact ⟨.nullish _ (Or.inr rfl), rfl⟩
  · intro current member parent prototype
    have same : current = record := by simpa [records] using member
    subst current
    have same : parent = 0 := by simpa [record, HandlerRecord.innerRecord] using prototype.symm
    subst parent
    exact safeReference 0 (by decide) (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 := by change count < 2 at inside; omega
    rcases cases with rfl | rfl <;>
      refine ⟨12, .object 13, rfl, safeReference 12 (by decide) (by decide), ?_, ?_⟩
    all_goals first
      | exact ⟨.object 13, rfl, Or.inl ⟨trivial, rfl⟩⟩
      | exact fun _ => ⟨record, by simp [records], rfl⟩

private def initial_wildcard : InitialWildcard entryState sourceTable closure 8 8 4 1 1 12 9 1 1
    getKey records [.object 13] := by
  let storage : NodePrivateCall.Storage entryState closure 8 1 4 12 [.object 12] :=
    ⟨⟨⟨[], some 0, true⟩, rfl⟩, rfl, by refine ⟨_, rfl, ?_⟩; rfl,
      rfl, by decide, by decide⟩
  exact ⟨⟨rfl, by decide, by decide, rfl, rfl⟩,
    ⟨4, [.object 12], storage⟩, ⟨4, [.object 12], storage⟩, rfl, rfl, initial_layout⟩

/-- Inputs contain only actual dense arrays and index bounds. The universal
theorem derives every selected value, last-index test and fresh queue before
running both source calls; no future branch/call result is supplied. -/
theorem source_prepared_initial_domain_has_composition_contract :
    ∃ prepared after,
      prepare true true true true true = some (.ok prepared) ∧
      SetupSource prepared.state (parts true) 1 ∧ SetupContract prepared.state (parts true) nodes 1 1 ∧
      (parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl 204 defaultSplitLimit prepared.table source
          (innerActivation (outerState (outerActivation (lengthState prepared.state (parts true)) 1) (parts true) 1) 1)) =
        some (.ok (.normal after)) ∧
      NodeLiteralBranch.BranchContract (branchEntry prepared.state (parts true) nodes 1 1) closure
        (.object 8) 4 12 13 1 getKey 1 after := by
  obtain ⟨source, contracts, after, executed, branch⟩ := wildcard_satisfies entryState sourceTable closure
    10 11 (parts true) nodes 1 1 7 8 8 4 1 1 12 9 1 1 getKey (.object 3) records [.object 13]
    inputs initial_child rfl initial_wildcard
  exact ⟨⟨entryState, sourceTable, sourceDefinition, 4, 6, 8, 12⟩, after, source_prepared,
    source, contracts, executed, branch⟩

end HonoLean.Upstream.NodeIterationSetup.Examples
