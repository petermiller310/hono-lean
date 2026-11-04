import HonoLean.Upstream.NodeRegExpExec.Composition
import HonoLean.Upstream.NodeClass.History

set_option autoImplicit false
namespace HonoLean.Upstream.NodeRegExpExec.Examples
open SourceSubset ECMA2025 MethodsLoopInitial
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def getKey : JSString := [71, 69, 84]
private def idKey : JSString := [105, 100]
private def zeroKey : JSString := [122]
private def digits : JSString := [49, 50]
private def keys : List JSString := [idKey, constructorKey, zeroKey, protoKey]
private def payload : OrdinaryObject :=
  ⟨[(idKey, .data (.string [97]) true true true), (zeroKey, .data (.number 0) true true true)], some 0, true⟩
/-- Supplied RegExp projection: constructor/getPattern/native brand linking is
NOT proved here. Public own source is deliberately spoofed; the internal record
keeps actual parsed digits code. A nonextensible readonly negative lastIndex
still works nonglobally and remains unchanged. -/
private def matcherObject : OrdinaryObject :=
  ⟨[(lastIndexKey, .data (.number (-7)) false false false),
    ([115, 111, 117, 114, 99, 101], .data (.string [101, 118, 105, 108]) false true false)], some 10, false⟩
private def regexpPrototype : OrdinaryObject := ⟨[(NodeExecCall.execKey, .data (.function 5) true false true)], some 0, true⟩
private def functions : FunctionTable := ⟨2, []⟩
private def members : MemberTable := ⟨3, []⟩
private def builtins : RegExpBuiltinTable := ⟨5, [.regexpExec]⟩
private def classBefore : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)]
   objects := [objectPrototypeProjection [], payload]
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def moduleState : State := NodeInitialization.preambleState classBefore
private def definition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def methods : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
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
private def caller (name input : JSString) : List (String × Value) :=
  [("node", .object 3), ("child", .object 3), ("method", .string getKey), ("emptyParams", .object 2),
   ("name", .string name), ("firstRecord", .object 6), ("matcher", .object 9), ("restPathString", .string input)] ++ moduleState.environment

/-- Compact ambient endpoint of source preparation below. No m array/binding
exists: genuine builtin execution will allocate heap cell5 after actual123. -/
private def ambient (parent : Nat) (name input : JSString) : State :=
  {environment := ("handlerSets", .array 4) :: caller name input
   objects := [objectPrototypeProjection [], payload, emptyNullObject, emptyLiteralObject, emptyNullObject,
     rowGET, handlerGET, rowALL, handlerALL, matcherObject, regexpPrototype]
   heap := [rows, [], keys.map Value.string, keys.map Value.string, initial]
   functions := classBefore.functions
   sets := [keys, keys]
   thisValue := .object 3
   privates := ⟨NodeClass.names 1, [(3, [(5, .data (.object parent)), (4, .data .undefined),
     (3, .data (.array 1)), (2, .data (.object 4)), (1, .data (.array 0)), (6, .method (.function 1))])]⟩}
private def before (parent : Nat) (name input : JSString) : RegExpCallState :=
  ⟨ambient parent name input, [(9, digitsRecord)], []⟩
private def nodeValue (parent : Nat) (key : JSString) : Value :=
  if parent = 1 then if key = idKey then .string [97] else if key = constructorKey then .objectConstructor
    else if key = zeroKey then .number 0 else .object 0 else .undefined
private def rootValue (key : JSString) : Value :=
  if key = constructorKey then .objectConstructor else if key = protoKey then .object 0 else .undefined
private def recordGET (parent : Nat) : Record := ⟨6, handlerGET, 2, ⟨keys, fun _ => .undefined, nodeValue parent⟩⟩
private def recordALL (parent : Nat) : Record := ⟨8, handlerALL, 3, ⟨keys, fun _ => .undefined, nodeValue parent⟩⟩
private def records (parent : Nat) : List Record := [recordGET parent, recordALL parent]

private theorem exec_inputs (parent : Nat) (name input : JSString) :
    Inputs (before parent name input) methods functions members builtins 9 5 input digitsRecord matcherObject (-7) false :=
  ⟨rfl, rfl, ⟨true, false, true, 2, .parent rfl rfl rfl (.own rfl rfl), by decide⟩,
    by change 1 ≤ 3; decide, by decide, by decide, by decide, by decide, rfl, rfl, initialize_digits, rfl, rfl, by decide⟩

private theorem safe_iff (parent : Nat) (name input : JSString) (reference : Nat) :
    Protected (ambient parent name input) (records parent) reference ↔ reference < 11 ∧ reference ≠ 6 ∧ reference ≠ 8 := by
  simp [Protected, ambient, records, recordGET, recordALL]
private theorem ancestors (parent : Nat) (name input : JSString) (reference : Nat) (object : OrdinaryObject)
    (found : (ambient parent name input).objects[reference]? = some object) (ancestor : Nat) (prototype : object.prototype = some ancestor) : ancestor = 0 ∨ ancestor = 10 := by
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], payload, emptyNullObject, emptyLiteralObject, emptyNullObject,
    rowGET, handlerGET, rowALL, handlerALL, matcherObject, regexpPrototype] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact Or.inl (Option.some.inj prototype).symm | exact Or.inr (Option.some.inj prototype).symm | cases prototype
private theorem physical_frame (parent : Nat) (name input : JSString) :
    TwoSourceFrame (ambient parent name input) closure.environment rows getKey 4 4 (records parent) initial := by
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
    rcases ancestors parent name input reference object found ancestor prototype with rfl | rfl <;> change _ < 11 <;> decide
  · intro reference _ object found ancestor prototype
    apply (safe_iff parent name input ancestor).mpr
    rcases ancestors parent name input reference object found ancestor prototype with rfl | rfl <;> decide
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
    rcases member with rfl | rfl <;> have same : ancestor = 0 := (Option.some.inj prototype).symm <;> subst ancestor <;>
      exact (safe_iff parent name input 0).mpr (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 ∨ count = 2 := by change count < 3 at inside; omega
    rcases cases with rfl | rfl | rfl
    · refine ⟨5, .object 6, rfl, (safe_iff parent name input 5).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 6, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨recordGET parent, by simp [records], rfl⟩
    · refine ⟨7, .object 8, rfl, (safe_iff parent name input 7).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro _; exact ⟨recordALL parent, by simp [records], rfl⟩
    · refine ⟨5, .object 6, rfl, (safe_iff parent name input 5).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 6, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨recordGET parent, by simp [records], rfl⟩
private theorem parent_writable (parent : Nat) (name input : JSString) : NodePrivateWrite.Writable (ambient parent name input) 3 5 (.object parent) :=
  ⟨rfl, ⟨emptyLiteralObject, rfl⟩, _, rfl, rfl⟩
private theorem entry (parent : Nat) (name input : JSString) (valid : parent = 1 ∨ parent = 2) :
    NodeCaptureCollect.EntryInputs (ambient parent name input) methods closure 3 1 3 5 3 1 0 4 parent 4 rows initial getKey (records parent) rootValue := by
  refine {
    installed := ⟨⟨6, rfl, ⟨emptyLiteralObject, rfl⟩, ⟨_, rfl, rfl⟩, rfl, by change 1 ≤ 1; decide, by decide, rfl⟩⟩
    thisValue := rfl
    collectorBinding := rfl
    childBinding := rfl
    methodBinding := rfl
    nodeBinding := rfl
    parentData := parent_writable parent name input
    stored := ⟨⟨emptyLiteralObject, rfl⟩, rfl, ⟨_, rfl, rfl⟩, rfl, by decide, by decide⟩
    frame := physical_frame parent name input
    parentProtected := ?_
    rootProtected := (safe_iff parent name input 0).mpr (by decide)
    parentReads := ?_
    rootReads := ?_ }
  · apply (safe_iff parent name input parent).mpr
    rcases valid with rfl | rfl <;> decide
  · intro record member key used
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> change key ∈ [idKey, constructorKey, zeroKey, protoKey] at used <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used <;>
      rcases used with rfl | rfl | rfl | rfl <;> rcases valid with rfl | rfl <;> rfl
  · intro record member key used
    change record ∈ [recordGET parent, recordALL parent] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> change key ∈ [idKey, constructorKey, zeroKey, protoKey] at used <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used <;> rcases used with rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨none, 1, .absent rfl rfl rfl, by decide, .absent⟩
      | exact ⟨_, 1, .own rfl rfl, by decide, .data .objectConstructor true false true⟩
      | exact ⟨_, 1, .own rfl rfl, by decide, .prototype .prototype false true⟩
private theorem header (parent : Nat) (name input : JSString) : NodeParamsInit.HeaderInputs (ambient parent name input) 3 5 parent 2 :=
  ⟨rfl, rfl, ⟨emptyNullObject, rfl⟩, parent_writable parent name input, ⟨objectPrototypeProjection [], rfl⟩⟩
private theorem copied_init (name input : JSString) :
    NodeCaptureCollect.InitInputs (ambient 1 name input) 3 5 1 2 (NodeParamsInit.copiedObject payload) 18 := by
  apply NodeCaptureCollect.InitInputs.copied payload
  refine ⟨header 1 name input, by decide, rfl, ?_⟩
  apply NodeParamsInit.enumerableData_of_ready
  · change ([idKey, zeroKey] : List JSString).Nodup
    decide
  · intro key getter setter configurable found
    simp only [payload, List.lookup_cons] at found
    repeat' (split at found <;> simp_all)

/-- No prepared m is present at the actual source-entry initial state. -/
theorem initial_state_has_no_match_binding_or_cell (parent : Nat) (name input : JSString) :
    (before parent name input).ambient.environment.lookup "m" = none ∧ (before parent name input).ambient.heap.length = 5 := ⟨rfl, rfl⟩

/-- The current builtin executes its parsed digits program on ANY raw UTF16
argument; this normal domain includes negative/readonly lastIndex and spoofed
public source. No accepted-language premise is needed for the miss contract. -/
theorem real_builtin_domain_is_inhabited (input : JSString) :
    sourceExec 20 methods functions members builtins (before 1 constructorKey input) = some (.ok (resultState (before 1 constructorKey input) input)) ∧
      Contract 20 (before 1 constructorKey input) (resultState (before 1 constructorKey input) input) 9 5 input matcherObject (-7) false :=
  source_exec_satisfies 0 _ methods functions members builtins 9 5 input digitsRecord matcherObject (-7) false (exec_inputs 1 constructorKey input)

private def Pipeline (parent : Nat) (name input : JSString) (object : OrdinaryObject) (fuel : Nat) : Prop :=
  let start := before parent name input
  let initializedAmbient := NodeParamsInit.mapState start.ambient object
  let initializedWorld := {start with ambient := initializedAmbient}
  let computed := resultState initializedWorld input
  let guarded := matchAmbient (NodeParamsInit.mapState start.ambient (newDataObject object name (.string input))) input
  NodeParamsInit.sourceInit fuel start.ambient = some (.ok initializedAmbient) ∧
  NodeParamsInit.InitContract start.ambient initializedAmbient 3 5 parent 2 ∧
  sourceExec 20 methods functions members builtins initializedWorld = some (.ok computed) ∧
  Contract 20 initializedWorld computed 9 5 input matcherObject (-7) false ∧
  evalExpression 1 defaultSplitLimit guardCondition computed.ambient = .ok (.array 5, computed.ambient) ∧
  ∃ after, NodeCaptureCollect.sourceCollect 113 methods computed.ambient = some (.ok (.normal after)) ∧
    NodeCaptureGuard.GuardContract computed.ambient 11 object name (.ok (.normal guarded)) ∧
    NodeCaptureCollect.Contract guarded after closure 3 3 1 0 4 parent 11 rows initial getKey ∧
    after.heap[5]? = some [.string input] ∧
    observeRegExpResult {computed with ambient := after} 5 .groups = some (.data .undefined true true true) ∧
    observeRegExpResult {computed with ambient := after} 5 .zero = some (.data (.string input) true true true)

/-- GENUINE builtin result supplies the capture and actual161 collection. The
constructor SECOND-key issue now has computed regex provenance rather than an
assumed m array. GET/ALL/repeated rows/live old prefix share one caller state. -/
theorem copied_initializer_builtin_capture_collect_has_initial_domain :
    Pipeline 1 constructorKey digits (NodeParamsInit.copiedObject payload) 18 :=
  source_init_builtin_created_collect_satisfies 0 _ methods functions members builtins 9 5 digits digitsRecord matcherObject (-7) false
    closure 3 1 3 5 3 1 0 4 1 2 4 18 rows initial getKey constructorKey (records 1) rootValue (NodeParamsInit.copiedObject payload) _ 1
    (exec_inputs 1 constructorKey digits) (entry 1 constructorKey digits (Or.inl rfl)) (copied_init constructorKey digits)
    (Or.inl rfl) rfl rfl (.own rfl rfl) (by decide) rfl (by decide)

/-- Shared123 arm is also genuinely inhabited before the computed builtin
result enters capture and the same actual helper call. -/
theorem shared_initializer_builtin_capture_collect_has_initial_domain :
    Pipeline 2 idKey digits emptyLiteralObject 16 :=
  source_init_builtin_created_collect_satisfies 0 _ methods functions members builtins 9 5 digits digitsRecord matcherObject (-7) false
    closure 3 1 3 5 3 1 0 4 2 2 4 16 rows initial getKey idKey (records 2) rootValue emptyLiteralObject none 1
    (exec_inputs 2 idKey digits) (entry 2 idKey digits (Or.inr rfl)) (.shared (header 2 idKey digits) rfl)
    (Or.inl rfl) rfl rfl (.absent rfl rfl rfl) (by decide) rfl (by decide)

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state | _ => .error .unsupported
private def duplicateSource : String := "node.#methods.push(node.#methods[0])"
private def duplicateProgram : Expr := .call (.privateProperty (.variable "node") "methods") "push"
  [.index (.privateProperty (.variable "node") "methods") (.number 0)]
private def allocationSource : String := "const handlerSets = [firstRecord]\n"
private def allocationProgram : List Stmt := [.declare "handlerSets" (.arrayLiteral [(false, .variable "firstRecord")])]
private theorem parses_duplicate : parseExpression duplicateSource ["node"] ["methods"] = some duplicateProgram := by cbv
private theorem parses_allocations : parseBlock allocationSource ["firstRecord"] = some allocationProgram := by cbv

private def prepareCore (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (push duplicate : Expr) (parameter : Assignment) (allocations : List Stmt)
    (parent : Nat) (name input : JSString) : Except EvalError RegExpCallState := do
  let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry classBefore))
  let (selected, _, _) ← match definePrivateClass fields [method] module ⟨1⟩ ⟨1, []⟩ with
    | some selected => pure selected | none => throw .unsupported
  let (owner, one) ← instantiatePrivateClass 64 defaultSplitLimit selected (some 0) module
  let active := {one with privates := {one.privates with names := selected.names}}
  let history ← RegistrationHistory.runSourceHistory push owner requests active
  -- Explicit fixture: repeat the GET row and allocate a nonempty live prefix.
  let entry := {history with environment := caller name input, thisValue := .object owner}
  let (_, repeated) ← evalExpression 32 defaultSplitLimit duplicate entry
  let (_, seeded) ← executeAssignment 32 defaultSplitLimit parameter
    {repeated with environment := ("params", .object parent) :: repeated.environment}
  let allocated ← normalState (← execute 32 defaultSplitLimit allocations {seeded with environment := entry.environment})
  let record ← match initializeRangeRecord digitsPattern [] with | some record => pure record | none => throw .unsupported
  -- Supplied RegExp-object/prototype/brand projection, NOT native constructor
  -- semantics. The internal matcher code itself comes from the genuine parser.
  pure ⟨{allocated with objects := allocated.objects ++ [matcherObject, regexpPrototype]}, [(9, record)], []⟩
private def sourcePrepare (parent : Nat) (name input : JSString) : Option (Except EvalError RegExpCallState) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let duplicate ← parseExpression duplicateSource ["node"] ["methods"]
  let parameter ← parseAssignment NodePrivateWrite.pinnedParameterSource NodePrivateWrite.parameterBindings NodePrivateCall.classPrivateNames
  let allocations ← parseBlock allocationSource ["firstRecord"]
  pure (prepareCore preamble fields method push duplicate parameter allocations parent name input)
private theorem prepared (parent : Nat) (name input : JSString) : sourcePrepare parent name input = some (.ok (before parent name input)) := by
  have preamble := NodeInitialization.run_preamble classBefore ⟨0, [], rfl, rfl, Or.inl rfl⟩
  have selected : definePrivateClass NodeClass.fieldsProgram [NodePrivateCall.methodProgram] moduleState ⟨1⟩ ⟨1, []⟩ =
      some (definition, ⟨7⟩, methods) := NodeClass.define_node moduleState ⟨1⟩ ⟨1, []⟩ (by decide)
  have instanceRun : instantiatePrivateClass 64 defaultSplitLimit definition (some 0) moduleState =
      .ok (3, NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2)) :=
    NodeClass.instantiate_node moduleState (some 0) moduleState.environment 1 1 (.object 2) rfl
      ⟨objectPrototypeProjection [], rfl⟩ ⟨⟨0, [], rfl, rfl, Or.inl rfl⟩, rfl⟩
  have seed : RegistrationHistory.Seed initialized 3 1 0 0 [] :=
    ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨emptyLiteralObject, rfl⟩, rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
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
      privates := {(NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 2)).privates with names := definition.names}} = .ok registered at history
  dsimp only [moduleState] at history
  rw [history]
  cbv

/-- Actual class/METHOD installation, GET/ALL source registrations and202
prepare the universal pipeline domain. Matcher/prototype/brand remain the
explicit fixture extension above; full insert/search/constructor is not claimed. -/
theorem actual_source_history_prepares_builtin_pipeline :
    ∃ ready, sourcePrepare 1 constructorKey digits = some (.ok ready) ∧
      Inputs ready methods functions members builtins 9 5 digits digitsRecord matcherObject (-7) false ∧
      NodeCaptureCollect.EntryInputs ready.ambient methods closure 3 1 3 5 3 1 0 4 1 4 rows initial getKey (records 1) rootValue ∧
      Pipeline 1 constructorKey digits (NodeParamsInit.copiedObject payload) 18 :=
  ⟨before 1 constructorKey digits, prepared 1 constructorKey digits, exec_inputs 1 constructorKey digits,
    entry 1 constructorKey digits (Or.inl rfl), copied_initializer_builtin_capture_collect_has_initial_domain⟩

/-- Selected successful continuation, not a manufactured complete if157 body.
Every source fragment is parsed; errors prevent all later execution stages. -/
private def selectedRun (parent : Nat) (name input : JSString) (initFuel : Nat) : Option (Except RegExpCallError RegExpCallState) := do
  let initializer ← parseObjectInitDeclaration NodeParamsInit.pinnedSource NodeParamsInit.bindings NodeParamsInit.privateNames
  let exec ← parseMemberDeclaration pinnedSource bindings []
  let collect ← parsePrivateControl NodeCaptureCollect.pinnedSource NodeCaptureCollect.bindings NodePrivateCall.classPrivateNames
  pure do
    let first ← (executeObjectInitDeclaration initFuel defaultSplitLimit initializer (ambient parent name input)).mapError RegExpCallError.evaluation
    let computed ← executeRegExpDeclaration 20 defaultSplitLimit methods functions members builtins exec {(before parent name input) with ambient := first}
    let completion ← (executePrivateControl 113 defaultSplitLimit methods collect computed.ambient).mapError RegExpCallError.evaluation
    match completion with
    | .normal after => pure {computed with ambient := after}
    | _ => throw (.evaluation .unsupported)

private def capturedRecord (state : State) (reference : Nat) : Option (Nat × List (Option PropertyDescriptor)) := do
  let handler ← state.objects[reference]?
  let .data (.object output) _ _ _ ← handler.own.lookup NodeParamAssignment.paramsKey | none
  let object ← state.objects[output]?
  return (output, keys.map (fun key => object.own.lookup key))
private def observePipeline (parent : Nat) (name input : JSString) (initFuel : Nat) : Option (Except RegExpCallError
    (Option (List Value) × Option (Nat × List (Option PropertyDescriptor)) × Option (Nat × List (Option PropertyDescriptor)) ×
      Option PropertyDescriptor × Option PropertyDescriptor × Option PropertyDescriptor × Option PropertyDescriptor)) :=
  (selectedRun parent name input initFuel).map (fun outcome => outcome.map (fun state =>
    (state.ambient.heap[4]?, capturedRecord state.ambient 6, capturedRecord state.ambient 8,
      (state.ambient.objects[11]?).bind (fun object => object.own.lookup name),
      observeRegExpResult state 5 .groups, observeRegExpResult state 5 .zero,
      (state.ambient.objects[9]?).bind (fun object => object.own.lookup lastIndexKey))))
private def ordinaryFields : List (Option PropertyDescriptor) :=
  [some (.data (.string [97]) true true true), some (.data .objectConstructor true true true),
    some (.data (.number 0) true true true), some (.data (.object 0) true true true)]

/-- Current q owns the computed string12; parent-fourth/second-key fallback
captures Object itself. Old collector aliases see handler6's LAST reset14. -/
theorem genuine_builtin_result_reaches_live_GET_ALL_collector :
    observePipeline 1 constructorKey digits 18 =
      some (.ok (some [.object 6, .object 6, .object 8, .object 6], some (14, ordinaryFields), some (13, ordinaryFields),
        some (.data (.string digits) true true true), some (.data .undefined true true true),
        some (.data (.string digits) true true true), some (.data (.number (-7)) false false false))) := by
  simp only [observePipeline, selectedRun, NodeParamsInit.parses_source, parses_source, NodeCaptureCollect.parses_source]
  cbv

/-- Empty, trailing-line-terminator, fullwidth and surrogate inputs are genuine
VM misses: source binds null, allocates no array and retains readonly lastIndex. -/
theorem misses_bind_null_without_array_or_lastIndex_write :
    ([[], [49, 10], [49, 13], [49, 0x2028], [49, 0x2029], [0xff11], [0xd800], [49, 0xdc00]] : List JSString).map
      (fun input => ((resultState (before 1 idKey input) input).ambient.environment.lookup "m",
        (resultState (before 1 idKey input) input).ambient.heap.length,
        ((resultState (before 1 idKey input) input).ambient.objects[9]?).bind (fun object => object.own.lookup lastIndexKey))) =
      List.replicate 8 (some Value.null, 5, some (.data (.number (-7)) false false false)) := by cbv

end HonoLean.Upstream.NodeRegExpExec.Examples
