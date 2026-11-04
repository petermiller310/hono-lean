import HonoLean.Upstream.NodeQueueAdvance.Correctness
import HonoLean.Upstream.NodeFirstLiteral.Correctness
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeQueueAdvance.Examples

open SourceSubset ECMA2025 RegistrationHistory

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

private def initial (queued temporary : List Value) (temp : Nat := 1) : State :=
  {environment := [("unrelated", .number 9), ("curNodesQueue", .array 0), ("tempNodes", .array temp),
      ("curNodes", .string [111, 108, 100]), ("curNodes", .number 99), ("shifted", .number 88)]
   heap := [queued, temporary]
   objects := List.replicate 4 emptyNullObject
   thisValue := .object 3
   sets := [[[120]]]
   privates := PrivateStore.ofData [("saved", 7)] [(3, [(7, .number 8)])]}

private def front (temp : Nat := 1) : List (String × Value) :=
  [("unrelated", .number 9), ("curNodesQueue", .array 0), ("tempNodes", .array temp)]
private def back : List (String × Value) := [("curNodes", .number 99), ("shifted", .number 88)]

private def observed (before : State) : Option (Except EvalError (List (List Value) × List (String × Value))) :=
  (sourceAdvance 32 defaultSplitLimit before).map fun result => do
    let after ← normalState (← result)
    pure (after.heap, after.environment)

/-- Even an empty shifted array is truthy. Every self/shared reference is a
shallow value copy; the source reads queue/temp aliases only after shift. -/
theorem all_array_alias_patterns :
    (sourceAdvance 32 defaultSplitLimit (initial [.array 0, .object 1] [.object 2])).map
      (fun result => result.map (fun completion => match completion with | .normal state => state.heap | _ => [])) =
        some (.ok [[.object 1], [.object 2], [.object 2, .object 1]]) ∧
    (sourceAdvance 32 defaultSplitLimit (initial [.array 1, .object 1] [.object 2] 0)).map
      (fun result => result.map (fun completion => match completion with | .normal state => state.heap | _ => [])) =
        some (.ok [[.object 1], [.object 2], [.object 1, .object 2]]) ∧
    (sourceAdvance 32 defaultSplitLimit (initial [.array 0, .object 1, .array 0] [] 0)).map
      (fun result => result.map (fun completion => match completion with | .normal state => state.heap | _ => [])) =
        some (.ok [[.object 1, .array 0], [], [.object 1, .array 0, .object 1, .array 0]]) ∧
    (sourceAdvance 32 defaultSplitLimit (initial [.array 1] [.object 2, .array 1])).map
      (fun result => result.map (fun completion => match completion with | .normal state => state.heap | _ => [])) =
        some (.ok [[], [.object 2, .array 1], [.object 2, .array 1, .object 2, .array 1]]) ∧
    (sourceAdvance 32 defaultSplitLimit (initial [.array 1] [])).map
      (fun result => result.map (fun completion => match completion with | .normal state => state.heap | _ => [])) =
        some (.ok [[], [], []]) := by
  simp only [sourceAdvance, parses_source]
  cbv

theorem falsy_heads_reuse_temp_and_preserve_shadowed_bindings :
    ([.undefined, .null, .boolean false, .number 0, .string []] : List Value).all (fun head =>
      match observed (initial [head, .object 1] [.object 2]) with
      | some (.ok (heap, environment)) =>
          heap == [[.object 1], [.object 2]] && environment ==
            [("shifted", head), ("unrelated", .number 9), ("curNodesQueue", .array 0), ("tempNodes", .array 1),
             ("curNodes", .array 1), ("curNodes", .number 99), ("shifted", .number 88)]
      | _ => false) = true := by
  simp only [observed, sourceAdvance, parses_source]
  cbv

/-- Primitive strings are appended once, rather than spread into characters;
ordinary objects use default nonspreadability in this explicit model. -/
theorem truthy_nonarrays_append_one :
    ([.number 7, .string [945, 120], .object 2, .boolean true] : List Value).all (fun head =>
      match sourceAdvance 32 defaultSplitLimit (initial [head] [.object 1]) with
      | some (.ok (.normal state)) => state.heap == [[], [.object 1], [.object 1, head]]
      | _ => false) = true := by
  simp only [sourceAdvance, parses_source]
  cbv

/-- Missing old curNodes is an error after a successful RHS; an RHS error
takes precedence. Its previous value may be any type. The error interface
carries no observable partial mutation state. -/
theorem rejects_invalid_array_references_and_missing_lexical_slot :
    sourceAdvance 32 defaultSplitLimit (initial [.array 7] [.object 2]) = some (.error .invalidReference) ∧
    sourceAdvance 32 defaultSplitLimit {initial [] [] with heap := []} = some (.error .invalidReference) ∧
    sourceAdvance 32 defaultSplitLimit
      {environment := [("curNodesQueue", .array 0), ("tempNodes", .array 1)], heap := [[], []]} =
        some (.error .missingVariable) ∧
    sourceAdvance 32 defaultSplitLimit
      {environment := [("curNodesQueue", .array 0), ("tempNodes", .array 1)], heap := [[.array 7], []]} =
        some (.error .invalidReference) := by
  simp only [sourceAdvance, parses_source]
  cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem long_lists_are_not_limited_by_split_limit :
    (sourceAdvance 32 0 (initial [.array 1] ((List.range 512).map (fun index => .number (Int.ofNat index))))).map
      (fun result => result.map (fun completion => match completion with
        | .normal state => state.heap[2]?.map List.length
        | _ => none)) = some (.ok (some 1024)) := by
  simp only [sourceAdvance, parses_source]
  cbv

/-- A nonempty universal domain with queue=temp=argument, repeated shallow
references, a nonarray old curNodes and a shadowed second curNodes entry. -/
theorem self_alias_input_has_universal_contract :
    let before := initial [.array 0, .object 1, .array 0] [] 0
    ∃ after, sourceAdvance 32 defaultSplitLimit before = some (.ok (.normal after)) ∧
      Contract before 0 0 [.array 0, .object 1, .array 0] [.array 0, .object 1, .array 0] after := by
  dsimp only
  have inputs : Inputs (initial [.array 0, .object 1, .array 0] [] 0) 0 0
      [.array 0, .object 1, .array 0] [.array 0, .object 1, .array 0] (front 0) (.string [111, 108, 100]) back := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact source_advance_satisfies 22 defaultSplitLimit _ 0 0 _ _ (front 0) _ back inputs
    (by intro argument head; simp only [List.headD_cons, Value.array.injEq] at head; subst argument; exact ⟨_, rfl⟩)

private def getKey : JSString := [71, 69, 84]
private def xKey : JSString := [120]
private def idKey : JSString := [105, 100]
private def seedState : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection [], newDataObject emptyNullObject idKey (.number 7), emptyNullObject]
   functions := [⟨CreateNullObject.createProgram, []⟩]}

private def objectReference : Value → Except EvalError Nat
  | .object reference => .ok reference
  | _ => .error .unsupported
private def arrayReference : Value → Except EvalError Nat
  | .array reference => .ok reference
  | _ => .error .unsupported

private structure Prepared where
  state : State
  methods : PrivateMethodTable
  functions : FunctionTable

/-- Actual class/preamble, source push registration, and earlier source202
stale params. Ordinary child maps are explicit tree inputs. -/
private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push : Expr) (seed : Assignment) (split : Function) : Except EvalError Prepared := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry seedState))
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
  let children ← objectReference (← privateGet (.object root) "children" seeded)
  let objects ← (setProperty propertyFuel seeded.objects children xKey (.object child)).mapError .objectError
  let linked := {seeded with objects}
  let closure : StringFunctionClosure := ⟨split, module.environment, []⟩
  let functions : FunctionTable := ⟨methods.base + methods.entries.length, [closure]⟩
  let state := {linked with
    thisValue := .object root
    environment := [("splitPath", .function functions.base), ("path", .string [47, 120, 47, 121]),
      ("method", .string getKey)] ++ linked.environment}
  pure ⟨state, methods, functions⟩

private def arrayNamed (state : State) (name : String) : Except EvalError (List Value) := do
  let reference ← arrayReference (← lookupVariable state name)
  match state.heap[reference]? with | some values => pure values | none => throw .invalidReference

private def sourcePipeline (addPending : Bool) : Option (Except EvalError
    (Value × List Value × List Value × List Value × List Value × List Value × Nat × Value × Value)) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let seed ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let split ← parse SourceSubset.pinnedSource
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let outer ← parseForHeader NodeLoopEntry.pinnedOuterSource NodeLoopEntry.outerBindings
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let inner ← parseForHeader NodeLoopEntry.pinnedInnerSource NodeLoopEntry.innerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  let literal ← parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames
  let pending ← parseExpression "curNodesQueue.push(curNodes)" bindings
  let advance ← parseMutableSequence pinnedSource bindings mutableBindings
  pure do
    let prepared ← prepareCore preamble fields method push seed split
    let entry ← NodeLoopEntry.executePrefix startup outer iteration inner entry prepared.methods prepared.functions prepared.state
    let first ← NodeFirstLiteral.executeFirst 200 prepared.methods literal entry
    -- This optional ordinary push is supplied input preparation, not a proof
    -- that Hono's omitted pattern body produced this pending queue.
    let before ← if addPending then do
      let (_, state) ← evalExpression 32 defaultSplitLimit pending first.state
      pure state
      else pure first.state
    let after ← normalState (← executeMutableSequence 32 defaultSplitLimit mutableBindings advance before)
    let value ← lookupVariable after "curNodes"
    let nodes ← arrayNamed after "curNodes"
    let temp ← arrayNamed after "tempNodes"
    let queue ← arrayNamed after "curNodesQueue"
    let parts ← arrayNamed after "parts"
    let collector ← arrayNamed after "handlerSets"
    let rootParams ← privateGet (.object 4) "params" after
    let childParams ← privateGet (.object 6) "params" after
    pure (value, nodes, temp, queue, parts, collector, after.heap.length, rootParams, childParams)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- Source startup and actual first literal prefix produce the nonempty temp
queue. Queue advance is a separate source209–210 activation; the intervening
remainder of the real loop body has not been verified. -/
theorem source_prepared_nonlast_prefix_then_advance :
    sourcePipeline false = some (.ok (.array 9, [.object 6], [.object 6], [], [.string [120], .string [121]],
      [], 10, .object 3, .object 3)) ∧
    sourcePipeline true = some (.ok (.array 10, [.object 6, .object 4], [.object 6], [], [.string [120], .string [121]],
      [], 11, .object 3, .object 3)) := by
  constructor <;> simp only [sourcePipeline, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, NodePrivateWrite.parses_parameter, SourceSubset.parses_pinned_source,
    NodeSearchSetup.parses_source, NodeLoopEntry.parses_outer, NodeIterationSetup.parses_outer,
    NodeLoopEntry.parses_inner, NodeIterationSetup.parses_node_branch, NodeLiteralBranch.parses_source, parses_source,
    Bool.false_eq_true, ↓reduceIte] <;> cbv

/-- info: 'HonoLean.Upstream.NodeQueueAdvance.source_advance_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.NodeQueueAdvance.source_advance_satisfies

end HonoLean.Upstream.NodeQueueAdvance.Examples
