import HonoLean.Upstream.NodeSearchSetup.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeSearchSetup.Examples

open SourceSubset ECMA2025 RegistrationHistory

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

/-- Ordinary child-map inputs remain outside the Node.insert traversal proof. -/
private def childEntry (state : State) (owner : Nat) (key : JSString) (value : Value) : Except EvalError State := do
  let children ← objectReference (← privateGet (.object owner) "children" state)
  let objects ← (setProperty propertyFuel state.objects children key value).mapError .objectError
  pure {state with objects}

private structure Prepared where
  state : State
  methods : PrivateMethodTable
  functions : FunctionTable
  closure : StringFunctionClosure
  root : Nat
  child : Nat

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push : Expr) (seed : Assignment) (split : Function) (path : JSString) : Except EvalError Prepared := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry before))
  let (definition, _, methods) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some result => pure result
    | none => throw .unsupported
  let (root, one) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) module
  let (child, two) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) one
  let active := {two with privates := {two.privates with names := definition.names}}
  let registered ← runSourceHistory push child [⟨getKey, .number 10, [idKey, idKey]⟩] active
  let old := registered.environment
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit seed
    {registered with environment := [("child", .object root), ("params", .object 1)] ++ old}
  let seeded := {seeded with environment := old}
  let linked ← childEntry seeded root xKey (.object child)
  let linked ← childEntry linked child [42] (.object child)
  let closure : StringFunctionClosure := ⟨split, module.environment, []⟩
  let functions : FunctionTable := ⟨methods.base + methods.entries.length, [closure]⟩
  let state := {linked with
    thisValue := .object root
    environment := [("splitPath", .function functions.base), ("path", .string path), ("method", .string getKey)] ++ linked.environment}
  pure ⟨state, methods, functions, closure, root, child⟩

/-- Parsed preamble/class installation, actual registration and an earlier
actual source202 stale-params write. The imported split closure itself comes
from its pinned source parser. No parts/current-nodes/collector is supplied. -/
private def prepare (path : JSString) : Option (Except EvalError Prepared) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let seed ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let split ← parse SourceSubset.pinnedSource
  pure (prepareCore preamble fields method push seed split path)

private def arrayNamed (state : State) (name : String) : Except EvalError (List Value) := do
  let reference ← arrayReference (← lookupVariable state name)
  match state.heap[reference]? with
  | some values => pure values
  | none => throw .invalidReference

private structure Observation where
  collector : List Value
  nodes : List Value
  parts : List Value
  pending : List Value
  references : List Value
  length : Value
  offsets : Value
  params : Value
  allocations : Nat
  oldArrays : Bool
  objects : Bool
  runtimeThis : Bool
  deriving Repr

private def observe (prepared : Prepared) (after : State) : Except EvalError Observation := do
  let collector ← arrayNamed after "handlerSets"
  let nodes ← arrayNamed after "curNodes"
  let parts ← arrayNamed after "parts"
  let pending ← arrayNamed after "curNodesQueue"
  let references ← ["handlerSets", "curNodes", "parts", "curNodesQueue"].mapM (lookupVariable after)
  let length ← lookupVariable after "len"
  let offsets ← lookupVariable after "partOffsets"
  let params ← privateGet (.object prepared.root) "params" after
  pure ⟨collector, nodes, parts, pending, references, length, offsets, params,
    after.heap.length - prepared.state.heap.length,
    decide (after.heap.take prepared.state.heap.length = prepared.state.heap),
    decide (after.objects = prepared.state.objects), decide (after.thisValue = .object prepared.root)⟩

private def sourcePipeline (path : JSString) : Option (Except EvalError Observation) := do
  let ready ← prepare path
  let source ← parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true
  pure do
    let prepared ← ready
    let after ← normalState (← executeFunctionStatements 100 defaultSplitLimit prepared.methods prepared.functions source prepared.state)
    observe prepared after

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem empty_path_still_allocates_returned_array :
    sourcePipeline [] = some (.ok ⟨[], [.object 4], [], [], [.array 5, .array 6, .array 7, .array 8],
      .number 0, .null, .object 3, 4, true, true, true⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source, parses_source]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem trailing_fields_and_raw_utf16_survive_actual_call :
    sourcePipeline [47, 945, 47, 55296, 47] =
      some (.ok ⟨[], [.object 4], [.string [945], .string [55296], .string []], [],
        [.array 5, .array 6, .array 7, .array 8], .number 3, .null, .object 3, 4, true, true, true⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source, parses_source]
  cbv

private def literalPipeline : Option (Except EvalError (List Value × List Value × List Value × Value)) := do
  let ready ← prepare [47, 120]
  let startup ← parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← ready
    let started ← normalState (← executeFunctionStatements 100 defaultSplitLimit prepared.methods prepared.functions startup prepared.state)
    let iterated ← normalState (← execute 32 defaultSplitLimit iteration (NodeIterationSetup.outerActivation started 0))
    let after ← normalState (← executePrivateControl 256 defaultSplitLimit prepared.methods entry (NodeIterationSetup.innerActivation iterated 0))
    let collected ← arrayNamed after "handlerSets"
    let references ← collected.mapM objectReference
    let params ← references.mapM (fun reference => (getProperty propertyFuel after.objects reference HandlerRecord.paramsKey).mapError .objectError)
    let values ← params.mapM fun value => do
      let reference ← objectReference value
      (getProperty propertyFuel after.objects reference idKey).mapError .objectError
    let node ← lookupVariable after "node"
    pure (collected, params, values, node)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- Full first literal step is a closed nonempty source example. Both helper
calls share a handler, so collector aliases observe the last params reset.
The earlier stale private value7 is absent after actual startup reset. -/
theorem source_startup_then_first_literal_step :
    literalPipeline = some (.ok ([.object 9, .object 9], [.object 11, .object 11], [.undefined, .undefined], .object 4)) := by
  simp only [literalPipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source, parses_source,
    NodeIterationSetup.parses_outer, NodeIterationSetup.parses_node_branch]
  cbv

/- Compact expected constructor state is used only after the preparation
equality below proves the real source operations reach it. -/
private def moduleState : State := NodeInitialization.preambleState before
private def sourceMethods : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def sourceDefinition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def sourceClosure : StringFunctionClosure := ⟨splitPathProgram, moduleState.environment, []⟩
private def sourceFunctions : FunctionTable := ⟨2, [sourceClosure]⟩
private def one : State := NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 3)
private def two : State := NodeClass.instanceState one (some 0) moduleState.environment 1 1 (.object 3)
private def initialized : State := NodeClass.classActivation two 1
private def requests : List Request := [⟨getKey, .number 10, [idKey, idKey]⟩]
private def registered : State := endState initialized 6 2 0 [] requests
private def seedBefore : State := {registered with environment := [("child", .object 4), ("params", .object 1)] ++ registered.environment}
private def seeded : State := {writePrivateDataState seedBefore 4 5 (.object 1) with environment := registered.environment}
private def linked : State :=
  {seeded with
    objects := (seeded.objects.set 5 (newDataObject emptyNullObject xKey (.object 6))).set 7
      (newDataObject emptyNullObject [42] (.object 6))}
private def initialState (path : JSString) : State :=
  {linked with
    thisValue := .object 4
    environment := [("splitPath", .function 2), ("path", .string path), ("method", .string getKey)] ++ linked.environment}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem source_prepared (path : JSString) :
    prepare path = some (.ok ⟨initialState path, sourceMethods, sourceFunctions, sourceClosure, 4, 6⟩) := by
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
  have historySeed : Seed initialized 6 1 2 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have history : runSourceHistory NodeMethodsPush.expression 6 [⟨getKey, .number 10, [idKey, idKey]⟩]
      {two with privates := {two.privates with names := sourceDefinition.names}} = .ok registered :=
    run_source_history initialized 6 1 2 0 [] requests historySeed
  have writable : NodePrivateWrite.Writable seedBefore 4 5 (.object 3) :=
    ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  have seedRun := NodePrivateWrite.run_parameter seedBefore 4 5 (.object 3) (.object 1) writable ⟨rfl, rfl⟩
  dsimp only [moduleState] at defineRun first
  dsimp only [seedBefore] at seedRun
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
  rw [history]
  dsimp only
  rw [seedRun]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem initial_inputs (path : JSString) :
    Inputs (initialState path) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1) path := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, by decide, by decide, rfl⟩
  · exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  · change (1 : Nat) ≤ 1
    decide

/-- The generic theorem has an inhabited source-prepared domain, including an
actual registration and stale private params set by earlier source202. The
result follows from initial facts; no completed startup or split result is an input. -/
theorem source_prepared_input_has_universal_startup_contract (path : JSString) :
    ∃ prepared after parts,
      prepare path = some (.ok prepared) ∧
      (parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true).map
        (fun source => executeFunctionStatements 100 defaultSplitLimit prepared.methods prepared.functions source prepared.state) =
        some (.ok (.normal after)) ∧
      StartupContract prepared.state after 4 5 3 (.object 1) path parts := by
  obtain ⟨run, contract⟩ := startup_satisfies (initialState path) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1) path (initial_inputs path)
  exact ⟨⟨initialState path, sourceMethods, sourceFunctions, sourceClosure, 4, 6⟩, _, _, source_prepared path, run, contract⟩

end HonoLean.Upstream.NodeSearchSetup.Examples
