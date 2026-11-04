import HonoLean.Upstream.NodeCaptureCollect.Composition
import HonoLean.Upstream.NodeCaptureCollect.Frames
import HonoLean.Upstream.NodeClass.History

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureCollect.Examples
open SourceSubset ECMA2025 MethodsLoopInitial
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def getKey : JSString := [71, 69, 84]
private def idKey : JSString := [105, 100]
private def zeroKey : JSString := [122]
private def captured : JSString := [49, 50]
private def keys : List JSString := [idKey, constructorKey, zeroKey, protoKey]
private def payload : OrdinaryObject :=
  {own := [(idKey, .data (.string [97]) true true true), (zeroKey, .data (.number 0) true true true)]
   prototype := some 0}
private def classBefore : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection [], payload]
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def moduleState : State := NodeInitialization.preambleState classBefore
private def definition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def table : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def closure : PrivateMethodClosure := NodeClass.closure moduleState.environment 1
private def initialized : State := NodeClass.classActivation
  (NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2)) 1
private def requests : List RegistrationHistory.Request :=
  [⟨getKey, .number 10, keys⟩, ⟨SearchEntry.allKey, .number 11, keys⟩]
private def registered : State := RegistrationHistory.endState initialized 3 0 0 [] requests
private def rowGET : OrdinaryObject := HandlerRecord.outerRecord getKey 6
private def rowALL : OrdinaryObject := HandlerRecord.outerRecord SearchEntry.allKey 8
private def handlerGET : OrdinaryObject := HandlerRecord.innerRecord (.number 10) 2 1
private def handlerALL : OrdinaryObject := HandlerRecord.innerRecord (.number 11) 3 2
private def rows : List Value := [.object 5, .object 7, .object 5]
private def initial : List Value := [.object 6]
private def caller (name value : JSString) : List (String × Value) :=
  [("node", .object 3), ("child", .object 3), ("method", .string getKey), ("emptyParams", .object 2),
   ("name", .string name), ("firstRecord", .object 6), ("capture", .string value)] ++ moduleState.environment

/-- Compact endpoint. Proven source preparation below constructs this state;
using explicit cells prevents every domain field rerunning class/history ASTs. -/
private def before (parent : Nat) (name value : JSString) (withMatch : Bool) : State :=
  {environment := (if withMatch then [("m", .array 5)] else []) ++ ("handlerSets", .array 4) :: caller name value
   objects := [objectPrototypeProjection [], payload, emptyNullObject, emptyLiteralObject, emptyNullObject,
     rowGET, handlerGET, rowALL, handlerALL]
   heap := [rows, [], keys.map Value.string, keys.map Value.string, initial, [.string value]]
   functions := classBefore.functions
   sets := [keys, keys]
   thisValue := .object 3
   privates := ⟨NodeClass.names 1, [(3, [(5, .data (.object parent)), (4, .data .undefined),
     (3, .data (.array 1)), (2, .data (.object 4)), (1, .data (.array 0)), (6, .method (.function 1))])]⟩}
private def nodeValue (parent : Nat) (key : JSString) : Value :=
  if parent = 1 then if key = idKey then .string [97] else if key = constructorKey then .objectConstructor
    else if key = zeroKey then .number 0 else .object 0 else .undefined
private def rootValue (key : JSString) : Value :=
  if key = constructorKey then .objectConstructor else if key = protoKey then .object 0 else .undefined
private def recordGET (parent : Nat) : Record := ⟨6, handlerGET, 2, ⟨keys, fun _ => .undefined, nodeValue parent⟩⟩
private def recordALL (parent : Nat) : Record := ⟨8, handlerALL, 3, ⟨keys, fun _ => .undefined, nodeValue parent⟩⟩
private def records (parent : Nat) : List Record := [recordGET parent, recordALL parent]

private theorem safe_iff (parent : Nat) (name value : JSString) (withMatch : Bool) (reference : Nat) :
    Protected (before parent name value withMatch) (records parent) reference ↔
      reference < 9 ∧ reference ≠ 6 ∧ reference ≠ 8 := by
  simp [Protected, before, records, recordGET, recordALL]

private theorem parent_zero (parent : Nat) (name value : JSString) (withMatch : Bool) (reference : Nat)
    (object : OrdinaryObject) (found : (before parent name value withMatch).objects[reference]? = some object)
    (ancestor : Nat) (prototype : object.prototype = some ancestor) : ancestor = 0 := by
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], payload, emptyNullObject, emptyLiteralObject, emptyNullObject,
    rowGET, handlerGET, rowALL, handlerALL] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (Option.some.inj prototype).symm | cases prototype

private theorem physical_frame (parent : Nat) (name value : JSString) (withMatch : Bool) :
    TwoSourceFrame (before parent name value withMatch) closure.environment rows getKey 4 4 (records parent) initial := by
  refine {
    allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    collectorFound := rfl
    capacity := by decide
    closed := ?_
    protectedParents := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · intro reference _ object found ancestor prototype
    have same := parent_zero parent name value withMatch reference object found ancestor prototype
    subst ancestor
    change 0 < 9
    decide
  · intro reference _ object found ancestor prototype
    have same := parent_zero parent name value withMatch reference object found ancestor prototype
    subst ancestor
    exact (safe_iff parent name value withMatch 0).mpr (by decide)
  · intro record member
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨rfl, rfl, rfl, by change 4 ≠ 2; decide, ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩,
        by change keys.Nodup; decide, by change 4 ≤ 4294967295; decide, by change 4 ≤ 4; decide⟩
    · exact ⟨rfl, rfl, rfl, by change 4 ≠ 3; decide, ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩,
        by change keys.Nodup; decide, by change 4 ≤ 4294967295; decide, by change 4 ≤ 4; decide⟩
  · intro record member ancestor prototype
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      have same : ancestor = 0 := (Option.some.inj prototype).symm <;> subst ancestor <;>
      exact (safe_iff parent name value withMatch 0).mpr (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 ∨ count = 2 := by change count < 3 at inside; omega
    rcases cases with rfl | rfl | rfl
    · refine ⟨5, .object 6, rfl, (safe_iff parent name value withMatch 5).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 6, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨recordGET parent, by simp [records], rfl⟩
    · refine ⟨7, .object 8, rfl, (safe_iff parent name value withMatch 7).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro _; exact ⟨recordALL parent, by simp [records], rfl⟩
    · refine ⟨5, .object 6, rfl, (safe_iff parent name value withMatch 5).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 6, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨recordGET parent, by simp [records], rfl⟩

private theorem writable (parent : Nat) (name value : JSString) (withMatch : Bool) :
    NodePrivateWrite.Writable (before parent name value withMatch) 3 5 (.object parent) :=
  ⟨rfl, ⟨emptyLiteralObject, rfl⟩, _, rfl, rfl⟩

private theorem entry (parent : Nat) (name value : JSString) (withMatch : Bool) (validParent : parent = 1 ∨ parent = 2) :
    EntryInputs (before parent name value withMatch) table closure 3 1 3 5 3 1 0 4 parent 4 rows initial getKey (records parent) rootValue := by
  refine {
    installed := ⟨⟨6, rfl, ⟨emptyLiteralObject, rfl⟩, ⟨_, rfl, rfl⟩, rfl,
      by change 1 ≤ 1; decide, by change 1 ≤ 1; decide, rfl⟩⟩
    thisValue := rfl
    collectorBinding := ?_
    childBinding := ?_
    methodBinding := ?_
    nodeBinding := ?_
    parentData := writable parent name value withMatch
    stored := ⟨⟨emptyLiteralObject, rfl⟩, rfl, ⟨_, rfl, rfl⟩, rfl, by decide, by decide⟩
    frame := physical_frame parent name value withMatch
    parentProtected := ?_
    rootProtected := (safe_iff parent name value withMatch 0).mpr (by decide)
    parentReads := ?_
    rootReads := ?_ }
  · cases withMatch <;> rfl
  · cases withMatch <;> rfl
  · cases withMatch <;> rfl
  · cases withMatch <;> rfl
  · apply (safe_iff parent name value withMatch parent).mpr
    rcases validParent with rfl | rfl <;> decide
  · intro record member key used
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      change key ∈ [idKey, constructorKey, zeroKey, protoKey] at used <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used <;>
      rcases used with rfl | rfl | rfl | rfl <;> rcases validParent with rfl | rfl <;> rfl
  · intro record member key used
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      change key ∈ [idKey, constructorKey, zeroKey, protoKey] at used <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used <;>
      rcases used with rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨none, 1, .absent rfl rfl rfl, by decide, .absent⟩
      | exact ⟨_, 1, .own rfl rfl, by decide, .data .objectConstructor true false true⟩
      | exact ⟨_, 1, .own rfl rfl, by decide, .prototype .prototype false true⟩

private theorem header (parent : Nat) (name value : JSString) (withMatch : Bool) :
    NodeParamsInit.HeaderInputs (before parent name value withMatch) 3 5 parent 2 := by
  refine ⟨?_, ?_, ⟨emptyNullObject, rfl⟩, writable parent name value withMatch, ⟨objectPrototypeProjection [], rfl⟩⟩ <;>
    cases withMatch <;> rfl
private theorem copy_inputs (name value : JSString) (withMatch : Bool) :
    InitInputs (before 1 name value withMatch) 3 5 1 2 (NodeParamsInit.copiedObject payload) 18 := by
  apply InitInputs.copied payload
  refine ⟨header 1 name value withMatch, by decide, rfl, ?_⟩
  apply NodeParamsInit.enumerableData_of_ready
  · change [idKey, zeroKey].Nodup
    decide
  · intro key getter setter configurable found
    simp only [payload, List.lookup_cons] at found
    repeat' (split at found <;> simp_all)

private theorem match_inputs (name : JSString) (descriptor : Option PropertyDescriptor)
    (path : NodeCaptureGuard.DescriptorPath (before 1 name captured true).objects name 0 descriptor 1) :
    MatchInputs (before 1 name captured true) name 5 [.string captured] captured descriptor 1 :=
  ⟨Or.inl rfl, rfl, rfl, rfl, rfl, by decide, path, by decide⟩

private def Protocol (state : State) (parent : Nat) (object : OrdinaryObject) (fuel : Nat)
    (name : JSString) (guardedObject : OrdinaryObject) : Prop :=
  NodeParamsInit.sourceInit fuel state = some (.ok (NodeParamsInit.mapState state object)) ∧
  NodeParamsInit.InitContract state (NodeParamsInit.mapState state object) 3 5 parent 2 ∧
  ∃ after, sourceCollect 113 table (NodeParamsInit.mapState state object) = some (.ok (.normal after)) ∧
    NodeCaptureGuard.GuardContract (NodeParamsInit.mapState state object) state.objects.length object name
      (.ok (.normal (NodeParamsInit.mapState state guardedObject))) ∧
    Contract (NodeParamsInit.mapState state guardedObject) after closure 3 3 1 0 4 parent state.objects.length rows initial getKey

/-- Constructor is the SECOND key: actual161 preserves parent-fourth/q-fifth,
so native Object is represented explicitly as .objectConstructor in output. -/
theorem created_constructor_second_has_causal_contract :
    Protocol (before 1 constructorKey captured true) 1 (NodeParamsInit.copiedObject payload) 18 constructorKey
      (newDataObject (NodeParamsInit.copiedObject payload) constructorKey (.string captured)) := by
  exact source_init_created_collect_satisfies _ table closure 3 1 3 5 3 1 0 4 1 2 4 18 rows initial getKey constructorKey captured
    (records 1) rootValue _ 5 [.string captured] _ 1 (entry 1 constructorKey captured true (Or.inl rfl))
    (copy_inputs constructorKey captured true) (match_inputs constructorKey _ (.own rfl rfl)) rfl rfl

/-- Existing own zero skips m entirely. No m binding occurs at this entry. -/
theorem owned_falsy_skips_missing_match_binding :
    (before 1 zeroKey [] false).environment.lookup "m" = none ∧
    Protocol (before 1 zeroKey [] false) 1 (NodeParamsInit.copiedObject payload) 18 zeroKey (NodeParamsInit.copiedObject payload) := by
  refine ⟨rfl, ?_⟩
  exact source_init_owned_collect_satisfies _ table closure 3 1 3 5 3 1 0 4 1 2 4 18 rows initial getKey zeroKey (records 1) rootValue
    _ (.data (.number 0) true true true) (entry 1 zeroKey [] false (Or.inl rfl)) (copy_inputs zeroKey [] false) (Or.inl rfl) rfl rfl

/-- The standard primitive-string __proto__ setter leaves q without an own
field. The actual call still reads both source maps rather than repairing it. -/
theorem legacy_ignore_still_calls_with_actual_sources :
    Protocol (before 1 protoKey captured true) 1 (NodeParamsInit.copiedObject payload) 18 protoKey (NodeParamsInit.copiedObject payload) := by
  exact source_init_ignored_collect_satisfies _ table closure 3 1 3 5 3 1 0 4 1 2 4 18 rows initial getKey protoKey captured
    (records 1) rootValue _ 5 [.string captured] _ 1 (entry 1 protoKey captured true (Or.inl rfl)) (copy_inputs protoKey captured true)
    (match_inputs protoKey _ (.own rfl rfl)) rfl rfl

/-- Shared123 arm and a genuinely empty/falsy captured string are inhabited. -/
theorem shared_empty_capture_has_causal_contract :
    Protocol (before 2 idKey [] true) 2 emptyLiteralObject 16 idKey (newDataObject emptyLiteralObject idKey (.string [])) := by
  exact source_init_created_collect_satisfies _ table closure 3 1 3 5 3 1 0 4 2 2 4 16 rows initial getKey idKey []
    (records 2) rootValue emptyLiteralObject 5 [.string []] none 1 (entry 2 idKey [] true (Or.inr rfl))
    (.shared (header 2 idKey [] true) rfl)
    ⟨Or.inl rfl, rfl, rfl, rfl, rfl, by decide, .absent rfl rfl rfl, by decide⟩ rfl rfl

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state | _ => .error .unsupported
private def duplicateSource : String := "node.#methods.push(node.#methods[0])"
private def duplicateProgram : Expr := .call (.privateProperty (.variable "node") "methods") "push"
  [.index (.privateProperty (.variable "node") "methods") (.number 0)]
private def allocationSource : String := "const handlerSets = [firstRecord]\nconst m = [capture]\n"
private def allocationProgram : List Stmt :=
  [.declare "handlerSets" (.arrayLiteral [(false, .variable "firstRecord")]),
   .declare "m" (.arrayLiteral [(false, .variable "capture")])]
private theorem parses_duplicate : parseExpression duplicateSource ["node"] ["methods"] = some duplicateProgram := by cbv
private theorem parses_allocations : parseBlock allocationSource ["firstRecord", "capture"] = some allocationProgram := by cbv

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push duplicate : Expr) (parameter : Assignment) (allocations : List Stmt)
    (parent : Nat) (name value : JSString) (withMatch : Bool) : Except EvalError State := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry classBefore))
  let (selected, _, _) ← match definePrivateClass fields [method] module ⟨1⟩ ⟨1, []⟩ with
    | some selected => pure selected | none => throw .unsupported
  let (owner, one) ← instantiatePrivateClass 64 defaultSplitLimit selected (some 0) module
  let active := {one with privates := {one.privates with names := selected.names}}
  let history ← RegistrationHistory.runSourceHistory push owner requests active
  -- An explicit fixture appends the first GET row again. This is not another
  -- original registration event and is not claimed to be full insert behavior.
  let entry := {history with environment := caller name value, thisValue := .object owner}
  let (_, repeated) ← evalExpression 32 defaultSplitLimit duplicate entry
  -- The supplied ordinary payload is seeded through ACTUAL source202, in a
  -- separate activation; no guessed private DATA/METHOD slot is written here.
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit parameter
    {repeated with environment := ("params", .object parent) :: repeated.environment}
  let allocated ← normalState (← execute 32 defaultSplitLimit allocations {seeded with environment := entry.environment})
  pure (if withMatch then allocated else {allocated with environment := withoutBindings allocated.environment ["m"]})

/-- Actual selected preamble/class/constructor/source registration/202. Payload,
GET-row repetition, live collector and m=[capture] are explicit parsed fixture
inputs; this does not claim full insert/search reachability or matcher.exec. -/
private def sourcePrepare (parent : Nat) (name value : JSString) (withMatch : Bool) : Option (Except EvalError State) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let duplicate ← parseExpression duplicateSource ["node"] ["methods"]
  let parameter ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let allocations ← parseBlock allocationSource ["firstRecord", "capture"]
  pure (prepareCore preamble fields method push duplicate parameter allocations parent name value withMatch)

private theorem prepared (parent : Nat) (name value : JSString) (withMatch : Bool) :
    sourcePrepare parent name value withMatch = some (.ok (before parent name value withMatch)) := by
  have preamble := NodeInitialization.run_preamble classBefore ⟨0, [], rfl, rfl, Or.inl rfl⟩
  have selected : definePrivateClass NodeClass.fieldsProgram [NodePrivateCall.methodProgram] moduleState ⟨1⟩ ⟨1, []⟩ =
      some (definition, ⟨7⟩, table) := NodeClass.define_node moduleState ⟨1⟩ ⟨1, []⟩ (by decide)
  have instanceRun : instantiatePrivateClass 64 defaultSplitLimit definition (some 0) moduleState =
      .ok (3, NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2)) :=
    NodeClass.instantiate_node moduleState (some 0) moduleState.environment 1 1 (.object 2) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have seed : RegistrationHistory.Seed initialized 3 1 0 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨emptyLiteralObject, rfl⟩,
      rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
  have history := RegistrationHistory.run_source_history initialized 3 1 0 0 [] requests seed
  dsimp only [moduleState] at selected instanceRun
  simp only [sourcePrepare, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    NodeMethodsPush.parses_pinned_source, parses_duplicate, NodePrivateWrite.parses_parameter, parses_allocations]
  dsimp only [bind, Option.bind, pure]
  unfold prepareCore
  rw [preamble]
  dsimp only [bind, Except.bind, pure, Except.pure, normalState]
  rw [selected]
  dsimp only
  rw [instanceRun]
  dsimp only
  change RegistrationHistory.runSourceHistory NodeMethodsPush.expression 3 requests
    {NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2) with
      privates := {(NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2)).privates with names := definition.names}} =
    .ok registered at history
  dsimp only [moduleState] at history
  rw [history]
  cases withMatch <;> cbv

/-- The causal theorem's initial domain is reached by checked source preparation
with an actual METHOD installation, rather than a supplied function-valued slot.
Only the named fixture boundaries in sourcePrepare remain supplied. -/
theorem actual_class_history_202_prepares_causal_entry :
    ∃ ready, sourcePrepare 1 constructorKey captured true = some (.ok ready) ∧
      EntryInputs ready table closure 3 1 3 5 3 1 0 4 1 4 rows initial getKey (records 1) rootValue ∧
      InitInputs ready 3 5 1 2 (NodeParamsInit.copiedObject payload) 18 ∧
      Protocol ready 1 (NodeParamsInit.copiedObject payload) 18 constructorKey
        (newDataObject (NodeParamsInit.copiedObject payload) constructorKey (.string captured)) :=
  ⟨before 1 constructorKey captured true, prepared 1 constructorKey captured true,
    entry 1 constructorKey captured true (Or.inl rfl), copy_inputs constructorKey captured true,
    created_constructor_second_has_causal_contract⟩

private def capturedRecord (state : State) (reference : Nat) : Option (Nat × List (Option PropertyDescriptor)) := do
  let handler ← state.objects[reference]?
  let .data (.object output) _ _ _ ← handler.own.lookup NodeParamAssignment.paramsKey | none
  let object ← state.objects[output]?
  return (output, keys.map (fun key => object.own.lookup key))
private def observation (state : State) : Option (Except EvalError
    (Option (List Value) × Option (Nat × List (Option PropertyDescriptor)) × Option (Nat × List (Option PropertyDescriptor)) ×
     Option PropertyDescriptor × Option Value)) :=
  (sourceCollect 113 table state).map (fun outcome => outcome.map (fun result => match result with
    | .normal after => (after.heap[4]?, capturedRecord after 6, capturedRecord after 8,
        (after.objects[9]?).bind (fun object => object.own.lookup constructorKey), after.environment.lookup "m")
    | .returned _ _ => (none, none, none, none, none)))
private def ordinaryFields : List (Option PropertyDescriptor) :=
  [some (.data (.string [97]) true true true), some (.data .objectConstructor true true true),
   some (.data (.number 0) true true true), some (.data (.object 0) true true true)]

/-- The current q owns string12, while the SECOND helper key captures the
parent's inherited Object function. Every old prefix/GET alias of handler6
observes its LAST output12; ALL's distinct handler8 retains output11. -/
theorem constructor_capture_and_repeated_live_aliases_are_explicit :
    observation (NodeParamsInit.mapState (before 1 constructorKey captured true) (NodeParamsInit.copiedObject payload)) =
      some (.ok (some [.object 6, .object 6, .object 8, .object 6], some (12, ordinaryFields), some (11, ordinaryFields),
        some (.data (.string captured) true true true), some (.array 5))) := by
  simp only [observation, sourceCollect, parses_source, Option.map_some]
  cbv

theorem owned_skip_executes_without_match_and_preserves_zero :
    observation (NodeParamsInit.mapState (before 1 zeroKey [] false) (NodeParamsInit.copiedObject payload)) =
      some (.ok (some [.object 6, .object 6, .object 8, .object 6], some (12, ordinaryFields), some (11, ordinaryFields), none, none)) := by
  simp only [observation, sourceCollect, parses_source, Option.map_some]
  cbv

theorem legacy_ignore_does_not_invent_an_own_capture :
    observation (NodeParamsInit.mapState (before 1 protoKey captured true) (NodeParamsInit.copiedObject payload)) =
      some (.ok (some [.object 6, .object 6, .object 8, .object 6], some (12, ordinaryFields), some (11, ordinaryFields), none, some (.array 5))) := by
  simp only [observation, sourceCollect, parses_source, Option.map_some]
  cbv

theorem shared_falsy_capture_remains_empty_string :
    observation (NodeParamsInit.mapState (before 2 idKey [] true) emptyLiteralObject) =
      some (.ok (some [.object 6, .object 6, .object 8, .object 6],
        some (12, [some (.data (.string []) true true true), some (.data .objectConstructor true true true),
          some (.data .undefined true true true), some (.data (.object 0) true true true)]),
        some (11, [some (.data (.string []) true true true), some (.data .objectConstructor true true true),
          some (.data .undefined true true true), some (.data (.object 0) true true true)]), none, some (.array 5))) := by
  simp only [observation, sourceCollect, parses_source, Option.map_some]
  cbv

/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_created_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_created_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_ignored_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_ignored_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_owned_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_owned_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_call_protected_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_call_protected_frames

end HonoLean.Upstream.NodeCaptureCollect.Examples
