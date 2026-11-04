import HonoLean.Upstream.NodeLiteralBranch.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeLiteralBranch.Examples

open SourceSubset ECMA2025 RegistrationHistory

private def getKey : JSString := [71, 69, 84]
private def partKey : JSString := [120]
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

private def property (state : State) (reference : Nat) (key : JSString) : Except EvalError Value :=
  (getProperty propertyFuel state.objects reference key).mapError .objectError

/-- Ordinary child-map contents are supplied boundary inputs; this helper does
not install a private element or claim a Node.insert traversal theorem. -/
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

private structure Prepared where
  state : State
  table : PrivateMethodTable
  definition : SelectedPrivateClass
  root : Nat
  parent : Nat
  next : Nat
  wildcard : Nat
  collector : Nat
  temp : Nat

private def prefixProgram : Expr := .call (.variable "handlerSets") "push" [.variable "existingHandler"]

private theorem parses_prefix :
    parseExpression "handlerSets.push(existingHandler)" ["handlerSets", "existingHandler"] = some prefixProgram := by cbv

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push : Expr) (seed : Assignment) (collector : List Stmt) (prefixPush : Expr)
    (hasNext isLast hasWildcard shared livePrefix : Bool) : Except EvalError Prepared := do
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
  let seedState := {registered with environment := [("child", .object parent), ("params", .object 1)] ++ old}
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit seed seedState
  let seeded := {seeded with environment := old}
  let linked ← if hasNext then childEntry seeded parent partKey (.object next) else pure seeded
  let linked ← if hasWildcard then childEntry linked next [42] (.object (if shared then next else wildcard)) else pure linked
  let caller := [("node", .object parent), ("part", .string partKey),
    ("isLast", .boolean isLast), ("method", .string getKey)] ++ linked.environment
  let start := {linked with environment := caller, thisValue := .object root}
  let collected ← normalState (← execute 32 defaultSplitLimit collector start)
  let collector ← arrayReference (← lookupVariable collected "handlerSets")
  let temp := collected.heap.length
  let ready := {collected with
    environment := ("tempNodes", .array temp) :: collected.environment
    heap := collected.heap ++ [[]]}
  let ready ← if livePrefix then do
    let existing ← firstHandler ready next
    let (_, after) ← evalExpression 32 defaultSplitLimit prefixPush
      {ready with environment := ("existingHandler", existing) :: ready.environment}
    pure {after with environment := ready.environment}
    else pure ready
  pure ⟨ready, table, definition, root, parent, next, wildcard, collector, temp⟩

/-- Every private cell originates in parsed source class installation or an
actual parsed write. Only ordinary child maps and optional collector prefixes
are supplied. Source202 is a distinct earlier activation, not same-branch
search control flow leading backward from202 to106. -/
private def prepare (hasNext isLast hasWildcard shared livePrefix : Bool) :
    Option (Except EvalError Prepared) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let seed ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let collector ← parseBlock SearchEntry.pinnedCollectorSource []
  let prefixPush ← parseExpression "handlerSets.push(existingHandler)" ["handlerSets", "existingHandler"]
  pure (prepareCore preamble fields method push seed collector prefixPush hasNext isLast hasWildcard shared livePrefix)

private structure Observation where
  collector : List Value
  handlers : List Value
  values : List Value
  params : List Value
  temp : List Value
  savedNext : Value
  nextParams : Value
  newObjects : Nat
  callerScope : Bool
  runtimeThis : Bool
  methodKind : Bool
  deriving Repr

private def observe (prepared : Prepared) (after : State) : Except EvalError Observation := do
  let entries ← match after.heap[prepared.collector]? with
    | some entries => pure entries
    | none => throw .invalidReference
  let records ← entries.mapM objectReference
  let handlers ← records.mapM (fun record => property after record HandlerRecord.handlerKey)
  let params ← records.mapM (fun record => property after record HandlerRecord.paramsKey)
  let values ← params.mapM fun value => do
    let reference ← objectReference value
    property after reference idKey
  let temp ← match after.heap[prepared.temp]? with
    | some entries => pure entries
    | none => throw .invalidReference
  let savedNext ← lookupVariable after "nextNode"
  let nextParams ← privateGet (.object prepared.next) "params" after
  let methodKind := (after.privates.elements.lookup prepared.root).any fun fields =>
    (prepared.definition.names.lookup "pushHandlerSets").any fun identity =>
      decide (fields.lookup identity = some (.method (.function prepared.definition.firstHandle)))
  pure ⟨entries, handlers, values, params, temp, savedNext, nextParams,
    after.objects.length - prepared.state.objects.length,
    decide (after.environment = ("nextNode", savedNext) :: prepared.state.environment),
    decide (after.thisValue = .object prepared.root), methodKind⟩

private def sourcePipeline (hasNext isLast hasWildcard shared livePrefix : Bool) :
    Option (Except EvalError Observation) := do
  let ready ← prepare hasNext isLast hasWildcard shared livePrefix
  let branch ← parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← ready
    let after ← normalState (← executePrivateControl 128 defaultSplitLimit prepared.table branch prepared.state)
    observe prepared after

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem all_four_source_paths :
    sourcePipeline false true true false false =
      some (.ok ⟨[], [], [], [], [], .undefined, .object 3, 0, true, true, true⟩) ∧
    sourcePipeline true false true false false =
      some (.ok ⟨[], [], [], [], [.object 8], .object 8, .object 1, 0, true, true, true⟩) ∧
    sourcePipeline true true false false false =
      some (.ok ⟨[.object 13], [.number 10], [.number 7], [.object 16], [],
        .object 8, .object 1, 1, true, true, true⟩) ∧
    sourcePipeline true true true false false =
      some (.ok ⟨[.object 15, .object 13], [.number 20, .number 10], [.number 7, .number 7],
        [.object 16, .object 17], [], .object 8, .object 1, 2, true, true, true⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SearchEntry.parses_collector, parses_prefix, parses_source]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- The wildcard and literal paths target the same initialized Node. A supplied
collector prefix already aliases its handler record. Both actual source calls
append that same record again and reset its params, so all three live entries
observe the latest fresh cell17; cell16 was the earlier capture, not a snapshot
stored separately in the collector. -/
theorem shared_target_and_live_collector_observe_latest_params :
    sourcePipeline true true true true true =
      some (.ok ⟨[.object 13, .object 13, .object 13], [.number 10, .number 10, .number 10],
        [.number 7, .number 7, .number 7], [.object 17, .object 17, .object 17], [],
        .object 8, .object 1, 2, true, true, true⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SearchEntry.parses_collector, parses_prefix, parses_source]
  cbv

/- The following domain witness uses only the state *before* the branch.
Its preparation executes source initialization/registration/202; it contains
no branch evaluator result, future readiness, capture trace or desired output. -/
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
  [("node", .object 6), ("part", .string partKey), ("isLast", .boolean true), ("method", .string getKey)] ++ linked.environment
private def collected : State := SearchEntry.collectorState {linked with environment := caller, thisValue := .object 4}
private def ready : State :=
  {collected with environment := ("tempNodes", .array 11) :: collected.environment, heap := collected.heap ++ [[]]}
/-- Compact independent preparation endpoint. source_prepared below proves that
actual parsed initialization, registrations and202 produce this state; it is
not used as a manually staged input to the closed source executions above. -/
private def entryState : State := {ready with heap := ready.heap.set 10 [.object 13]}

private def record : MethodsLoopInitial.Record :=
  ⟨13, HandlerRecord.innerRecord (.number 10) 8 1, 8,
    ⟨[idKey], fun _ => .undefined, fun _ => .number 7⟩⟩
private def records : List MethodsLoopInitial.Record := [record]
private def origin : State := NodePrivateCall.bodyState entryState closure (.object 4) 10 8 getKey 1 .undefined

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem source_prepared :
    prepare true true true true true =
      some (.ok ⟨entryState, sourceTable, sourceDefinition, 4, 6, 8, 10, 10, 11⟩) := by
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
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SearchEntry.parses_collector, parses_prefix,
    ]
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

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem entry_objects :
    origin.objects = [objectPrototypeProjection [], newDataObject emptyNullObject idKey (.number 7),
      emptyNullObject, emptyNullObject, ⟨[], some 0, true⟩, emptyNullObject,
      ⟨[], some 0, true⟩, newDataObject emptyNullObject partKey (.object 8),
      ⟨[], some 0, true⟩, newDataObject emptyNullObject [42] (.object 8),
      ⟨[], some 0, true⟩, emptyNullObject,
      HandlerRecord.outerRecord getKey 13, HandlerRecord.innerRecord (.number 10) 8 1,
      HandlerRecord.outerRecord SearchEntry.allKey 15, HandlerRecord.innerRecord (.number 20) 9 2] := by
  cbv

private theorem parent_zero (reference : Nat) (object : OrdinaryObject)
    (found : origin.objects[reference]? = some object) (parent : Nat)
    (prototype : object.prototype = some parent) : parent = 0 := by
  have member := List.mem_of_getElem? found
  rw [entry_objects] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact (Option.some.inj prototype).symm
      | cases prototype

private theorem safeReference (reference : Nat) (bound : reference < 16) (different : reference ≠ 13) :
    MethodsLoopInitial.Protected origin records reference := by
  refine ⟨?_, ?_⟩
  · rw [entry_objects]; exact bound
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    exact different

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem child_entry :
    ChildEntry entryState 6 7 8 4 1 10 11 1 partKey getKey (.boolean true) (.object 3) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem initial_layout :
    MethodsLoopInitial.Layout origin [.object 12, .object 12] getKey 10 1 records .undefined 1 [.object 13] := by
  refine {
    collectorBinding := rfl, parameterBinding := rfl, nodeBinding := rfl, allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    collectorFound := rfl
    capacity := by decide
    closed := ?_
    protectedParents := ?_
    nodeProtected := safeReference 1 (by decide) (by decide)
    parameterProtected := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
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
      unique := by decide
      legalKeys := by decide
      keyBound := by decide
      reads := ?_ }
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

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private def wildcard_entry :
    WildcardEntry entryState sourceTable closure 8 8 4 1 1 10 11 9 1 1 getKey records [.object 13] := by
  let storage : NodePrivateCall.Storage entryState closure 8 1 4 10 [.object 12] :=
    ⟨⟨⟨[], some 0, true⟩, rfl⟩, rfl, by refine ⟨_, rfl, ?_⟩; rfl,
      rfl, by decide, by decide⟩
  exact ⟨⟨rfl, by decide, by decide, rfl, rfl⟩,
    ⟨4, [.object 12], storage⟩, ⟨4, [.object 12], storage⟩,
    rfl, rfl, by decide, initial_layout⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- The universal sequential contract has a nonempty, source-prepared domain
with shared wildcard/literal methods and an already live collector alias.
Only initial structural facts are proved; second-call readiness is derived by
the universal theorem from the first call's actual contract. -/
theorem source_prepared_shared_domain_has_branch_contract :
    ∃ prepared after,
      prepare true true true true true = some (.ok prepared) ∧
      (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl 203 defaultSplitLimit prepared.table source prepared.state) =
        some (.ok (.normal after)) ∧
      BranchContract prepared.state closure (.object 8) 4 10 11 1 getKey 1 after := by
  obtain ⟨after, executed, contract⟩ := wildcard_satisfies entryState sourceTable closure
    6 7 8 8 4 1 1 10 11 9 1 1 partKey getKey (.boolean true) (.object 3) records [.object 13]
    child_entry rfl wildcard_entry
  exact ⟨⟨entryState, sourceTable, sourceDefinition, 4, 6, 8, 10, 10, 11⟩, after, source_prepared,
    executed, contract⟩

end HonoLean.Upstream.NodeLiteralBranch.Examples
