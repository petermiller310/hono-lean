import HonoLean.Upstream.NodePartOffsets.Composition
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodePartOffsets.Examples
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

set_option maxRecDepth 65536 in
/-- The universal two-activation theorem has an actual source-prepared domain:
class installation, two constructors, real registration and stale source202
params. The only later entry input is i; no parts/table/cache is staged. -/
theorem source_prepared_input_has_universal_offsets_contract (path : JSString) (index : Nat)
    (bound : path.length < defaultSplitLimit) (inside : index < (NodeSearchSetup.producedParts path).length) :
    ∃ prepared started active front back after,
      prepare path = some (.ok prepared) ∧
      NodeSearchSetup.Inputs prepared.state prepared.methods prepared.functions prepared.closure 4 5 2 3 (.object 1) path ∧
      sourceStartup prepared.state prepared.methods prepared.functions = some (.ok (.normal started)) ∧
      NodeSearchSetup.StartupContract prepared.state started 4 5 3 (.object 1) path (NodeSearchSetup.producedParts path) ∧
      active = indexActivation started index ∧
      sourceOffsets ((NodeSearchSetup.producedParts path).length + 80) active = some (.ok after) ∧
      PreparedContract active (prepareState active front back path (NodeSearchSetup.producedParts path)) path (NodeSearchSetup.producedParts path) ∧
      CachedContract (prepareState active front back path (NodeSearchSetup.producedParts path)) after active.heap.length
        (tableValues path (NodeSearchSetup.producedParts path) (NodeSearchSetup.producedParts path).length)
        path index (offsetAt path (NodeSearchSetup.producedParts path) index) := by
  have result := startup_offsets_satisfies 0 (initialState path) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1)
    path index (initial_inputs path) bound inside
  simp only [Nat.zero_add] at result
  exact ⟨⟨initialState path, sourceMethods, sourceFunctions, sourceClosure, 4, 6⟩, _, _, _, _, _, source_prepared path,
    initial_inputs path, result.1, result.2.1, rfl, result.2.2.1, result.2.2.2.1, result.2.2.2.2.1⟩

private def freshFixture (path : JSString) (parts : List JSString) (index : Nat) : State :=
  {environment := [("partOffsets", .null), ("path", .string path), ("parts", .array 0), ("len", .number parts.length),
      ("i", .number index), ("p", .number 73), ("offset", .number 91), ("partOffsets", .array 1)]
   heap := [parts.map Value.string, [.number 19]]}

private def freshObservation (path : JSString) (index : Nat) : Option (Except EvalError (List Value × Value × Value × Value × Value × Nat)) := do
  let parts := NodeSearchSetup.producedParts path
  let result ← sourceOffsets (parts.length + 100) (freshFixture path parts index)
  pure do
    let after ← result
    let values ← match after.heap[2]? with | some values => pure values | none => throw .invalidReference
    pure (values, ← lookupVariable after "restPathString", ← lookupVariable after "p", ← lookupVariable after "offset",
      ← lookupVariable after "partOffsets", after.heap.length)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem leading_repeated_trailing_and_raw_utf16 :
    freshObservation [47, 945, 47, 47, 55296, 56320, 47] 2 =
      some (.ok ([.number 1, .number 3, .number 4, .number 7], .string [55296, 56320, 47], .number 73, .number 91, .array 2, 3)) ∧
    freshObservation [97, 47, 98, 47] 2 =
      some (.ok ([.number 0, .number 2, .number 4], .string [], .number 73, .number 91, .array 2, 3)) := by
  constructor <;> simp only [freshObservation, sourceOffsets, parses_source] <;> cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem genuinely_empty_loop_still_allocates_empty_cache :
    freshObservation [] 0 = some (.ok ([], .string [], .number 73, .number 91, .array 2, 3)) := by
  simp only [freshObservation, sourceOffsets, parses_source]
  cbv

private def cachedFixture (values : List Value) (path : JSString) : State :=
  {environment := [("partOffsets", .array 0), ("path", .string path), ("i", .number 0)]
   heap := [values]}

private def cacheObservation (values : List Value) (path : JSString) : Option (Except EvalError (Value × Nat × Bool)) := do
  let result ← sourceOffsets 100 (cachedFixture values path)
  pure do
    let after ← result
    pure (← lookupVariable after "restPathString", after.heap.length, decide (after.heap = [values]))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem cached_empty_and_wrong_tables_are_used_without_repair :
    cacheObservation [] [97, 47, 98] = some (.ok (.string [97, 47, 98], 1, true)) ∧
    cacheObservation [.number (-1)] [97, 47, 98] = some (.ok (.string [98], 1, true)) ∧
    cacheObservation [.number 99] [97, 47, 98] = some (.ok (.string [], 1, true)) ∧
    cacheObservation [.number 1] [55296, 56320, 47, 120] = some (.ok (.string [56320, 47, 120], 1, true)) := by
  repeat' constructor
  all_goals simp only [cacheObservation, sourceOffsets, parses_source]; cbv

private def repeatedObservation : Option (Except EvalError (Value × Value × Nat × Bool)) := do
  let path := [47, 945, 47, 120, 47]
  let parts := NodeSearchSetup.producedParts path
  let first ← sourceOffsets 100 (freshFixture path parts 0)
  let source ← parseOffsetSequence pinnedSource bindings mutableBindings
  pure do
    let first ← first
    let after ← executeOffsetSequence 100 defaultSplitLimit mutableBindings source (indexActivation first 1)
    pure (← lookupVariable first "partOffsets", ← lookupVariable after "restPathString", after.heap.length,
      decide (after.heap = first.heap))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem later_source_invocation_reuses_actual_first_table :
    repeatedObservation = some (.ok (.array 2, .string [120, 47], 3, true)) := by
  simp only [repeatedObservation, sourceOffsets, parses_source]
  cbv

/-- The initial structural fresh domain is nonempty, including caller p/offset
and a deeper duplicate cache. The universal fresh/cached theorem is applied. -/
theorem initial_domain_has_fresh_then_cached_contract :
    let path : JSString := [47, 945, 47, 120, 47]
    let parts := NodeSearchSetup.producedParts path
    let before := freshFixture path parts 0
    let front : List (String × Value) := []
    let back := before.environment.tail
    let prepared := prepareState before front back path parts
    let first := sliceState prepared [945, 47, 120, 47]
    let next := indexActivation first 1
    let last := sliceState next [120, 47]
    sourceOffsets (parts.length + 80) before = some (.ok first) ∧
    sourceOffsets 64 next = some (.ok last) ∧ last.heap = prepared.heap := by
  let path : JSString := [47, 945, 47, 120, 47]
  let parts := NodeSearchSetup.producedParts path
  let state := freshFixture path parts 0
  have inputs : FreshInputs state 0 path parts [] state.environment.tail := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide +kernel
  have split : SplitPathContract defaultSplitLimit path parts := (contract_iff _ _ _).mpr rfl
  have result := source_fresh_then_cached 0 state 0 path parts [] state.environment.tail inputs split (by decide +kernel)
    0 1 (by decide +kernel) (by decide +kernel) rfl
  exact ⟨result.1, result.2.1, result.2.2.2.1⟩

private def sourcePipeline (path : JSString) (index : Nat) : Option (Except EvalError (List Value × Value × Value × Nat)) := do
  let ready ← prepare path
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let offsets ← parseOffsetSequence pinnedSource bindings mutableBindings
  pure do
    let prepared ← ready
    let started ← normalState (← executeFunctionStatements 100 defaultSplitLimit prepared.methods prepared.functions startup prepared.state)
    let after ← executeOffsetSequence ((NodeSearchSetup.producedParts path).length + 100) defaultSplitLimit mutableBindings offsets (indexActivation started index)
    let values ← match after.heap[started.heap.length]? with | some values => pure values | none => throw .invalidReference
    pure (values, ← lookupVariable after "restPathString", ← privateGet (.object prepared.root) "params" after,
      after.heap.length - prepared.state.heap.length)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
theorem actual_startup_then_empty_and_utf16_offset_source :
    sourcePipeline [] 0 = some (.ok ([], .string [], .object 3, 5)) ∧
    sourcePipeline [47, 945, 47, 47, 55296, 56320, 47] 2 =
      some (.ok ([.number 1, .number 3, .number 4, .number 7], .string [55296, 56320, 47], .object 3, 5)) := by
  constructor
  · have started := NodeSearchSetup.execute_startup (initialState []) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1) [] (initial_inputs [])
    simp only [sourcePipeline, source_prepared, NodeSearchSetup.parses_source, parses_source]
    dsimp only [bind, Option.bind, pure, Except.bind]
    rw [started]
    cbv
  · have started := NodeSearchSetup.execute_startup (initialState [47, 945, 47, 47, 55296, 56320, 47]) sourceMethods sourceFunctions sourceClosure 4 5 2 3 (.object 1)
        [47, 945, 47, 47, 55296, 56320, 47] (initial_inputs _)
    simp only [sourcePipeline, source_prepared, NodeSearchSetup.parses_source, parses_source]
    dsimp only [bind, Option.bind, pure, Except.bind]
    rw [started]
    cbv

end HonoLean.Upstream.NodePartOffsets.Examples
