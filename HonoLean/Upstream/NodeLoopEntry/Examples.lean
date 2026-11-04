import HonoLean.Upstream.NodeLoopEntry.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeLoopEntry.Examples

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
    NodeSearchSetup.Inputs (initialState path) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1) path := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, by decide, by decide, rfl⟩
  · exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
  · change (1 : Nat) ≤ 1
    decide


private structure Observation where
  outerTaken : Bool
  innerTaken : Option Bool
  nodeDeclared : Bool
  i : Option Value
  j : Option Value
  len2 : Option Value
  part : Option Value
  isLast : Option Value
  node : Option Value
  temp : Option Value
  allocations : Nat
  deriving Repr

private def sourcePipeline (path : JSString) : Option (Except EvalError Observation) := do
  let ready ← prepare path
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let outer ← parseForHeader pinnedOuterSource outerBindings
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let inner ← parseForHeader pinnedInnerSource innerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← ready
    let outcome ← executePrefix startup outer iteration inner entry prepared.methods prepared.functions prepared.state
    pure ⟨outcome.outerTaken, outcome.innerTaken, outcome.nodeDeclared,
      outcome.state.environment.lookup "i", outcome.state.environment.lookup "j", outcome.state.environment.lookup "len2",
      outcome.state.environment.lookup "part", outcome.state.environment.lookup "isLast", outcome.state.environment.lookup "node",
      outcome.state.environment.lookup "tempNodes", outcome.state.heap.length - prepared.state.heap.length⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem empty_source_guard_skips_every_body_setup :
    sourcePipeline [] = some (.ok ⟨false, none, false, some (.number 0), none, none, none, none, none, none, 4⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeSearchSetup.parses_source, parses_outer, NodeIterationSetup.parses_outer, parses_inner, NodeIterationSetup.parses_node_branch]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem trailing_utf16_uses_actual_zero_indices_and_saved_singleton :
    sourcePipeline [47, 945, 47, 55296, 47] =
      some (.ok ⟨true, some true, true, some (.number 0), some (.number 0), some (.number 1),
        some (.string [945]), some (.boolean false), some (.object 4), some (.array 9), 5⟩) := by
  simp only [sourcePipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeSearchSetup.parses_source, parses_outer, NodeIterationSetup.parses_outer, parses_inner, NodeIterationSetup.parses_node_branch]
  cbv

private def literalPipeline : Option (Except EvalError (List Value × List Value × Value × Value)) := do
  let ready ← prepare [47, 120]
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let outer ← parseForHeader pinnedOuterSource outerBindings
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let inner ← parseForHeader pinnedInnerSource innerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  let literal ← parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames
  pure do
    let prepared ← ready
    let outcome ← executePrefix startup outer iteration inner entry prepared.methods prepared.functions prepared.state
    if !outcome.nodeDeclared then throw .unsupported else do
    let after ← normalState (← executePrivateControl 256 defaultSplitLimit prepared.methods literal outcome.state)
    let collector ← arrayReference (← lookupVariable after "handlerSets")
    let references ← match after.heap[collector]? with
      | some values => pure values
      | none => throw .invalidReference
    let handlers ← references.mapM objectReference
    let params ← handlers.mapM (fun reference =>
      (getProperty propertyFuel after.objects reference HandlerRecord.paramsKey).mapError .objectError)
    let i ← lookupVariable after "i"
    let j ← lookupVariable after "j"
    pure (references, params, i, j)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- One complete literal fragment now follows both real header initializers
and true guards. The remaining source body is still omitted; this closed
example observes live shared handler aliases without claiming loop completion. -/
theorem source_prepared_first_literal_step_uses_actual_headers :
    literalPipeline = some (.ok ([.object 9, .object 9], [.object 11, .object 11], .number 0, .number 0)) := by
  simp only [literalPipeline, prepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeSearchSetup.parses_source, parses_outer, NodeIterationSetup.parses_outer, parses_inner, NodeIterationSetup.parses_node_branch,
    NodeLiteralBranch.parses_source]
  cbv

/-- A controlled continuation probe, not the omitted Hono body: growing the
array after real header entry does not change its saved len2. -/
theorem inner_saved_length_exits_after_one_update_even_after_growth :
    ((parseForHeader pinnedInnerSource innerBindings).map fun header => do
      let entered ← enterForHeader 32 defaultSplitLimit header
        {environment := [("curNodes", .array 0)], heap := [[.object 4]], objects := List.replicate 7 emptyNullObject}
      let grown := {entered with heap := [[.object 4, .object 6]]}
      let advanced ← advanceForHeader header grown
      let (taken, checked) ← testForHeader 32 defaultSplitLimit header advanced
      pure (taken, checked.environment.lookup "j", checked.environment.lookup "len2", checked.heap)) =
      some (.ok (false, some (.number 1), some (.number 1), [[.object 4, .object 6]])) := by
  rw [parses_inner]
  cbv

/-- Another controlled probe: a saved true guard does not establish that a
shrunk current array has that element. The universal prefix has no such
intervening mutation; later iterations require an explicit array invariant. -/
theorem true_saved_guard_does_not_prove_current_index_exists :
    ((parseForHeader pinnedInnerSource innerBindings).map fun header => do
      let entered ← enterForHeader 32 defaultSplitLimit header
        {environment := [("curNodes", .array 0)], heap := [[.object 4]], objects := List.replicate 7 emptyNullObject}
      let shrunk := {entered with heap := [[]]}
      let (taken, checked) ← testForHeader 32 defaultSplitLimit header shrunk
      let value ← readProperty (.array 0) (.number 0) checked
      pure (taken, value)) = some (.ok (true, .undefined)) := by
  rw [parses_inner]
  cbv

theorem source_prepared_input_has_universal_header_prefix_contract (path : JSString) :
    ∃ prepared outcome,
      prepare path = some (.ok prepared) ∧
      sourcePrefix prepared.methods prepared.functions prepared.state = some (.ok outcome) ∧
      PrefixContract prepared.state 4 5 3 (.object 1) path outcome := by
  obtain ⟨run, contract⟩ := source_prefix_satisfies (initialState path) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1) path (initial_inputs path)
  exact ⟨⟨initialState path, sourceMethods, sourceFunctions, sourceClosure, 4, 6⟩, _, source_prepared path, run, contract⟩

end HonoLean.Upstream.NodeLoopEntry.Examples
