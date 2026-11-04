import HonoLean.Upstream.NodeRegExpExec.Correctness
import HonoLean.Upstream.NodeCaptureCollect.Composition
import HonoLean.Upstream.NodeCaptureCollect.Frames

set_option autoImplicit false
namespace HonoLean.Upstream.NodeRegExpExec
open SourceSubset ECMA2025 MethodsLoopInitial

/-- A single real match-array allocation preserves every OLD allocated array.
The initial frame supplies collector/key-cell bounds; no later Layout or
completed match/capture is an admission premise. Caller env is irrelevant to
captured imports and ordinary source reads. -/
theorem frame_heap_append (before after : State) (captureEnvironment : List (String × Value))
    (rows initial : List Value) (query : JSString) (collector keyBound : Nat) (records : List Record) (extra : List (List Value))
    (frame : TwoSourceFrame before captureEnvironment rows query collector keyBound records initial)
    (objects : after.objects = before.objects) (functions : after.functions = before.functions) (heap : after.heap = before.heap ++ extra) :
    TwoSourceFrame after captureEnvironment rows query collector keyBound records initial := by
  have safe : ∀ reference, Protected after records reference ↔ Protected before records reference := by
    intro reference
    simp only [Protected, objects]
  refine {
    allBinding := frame.allBinding
    helper := ?_
    collectorFound := ?_
    capacity := frame.capacity
    closed := by simpa [objects] using frame.closed
    protectedParents := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · obtain ⟨reference, environment, binding, found, standard⟩ := frame.helper
    exact ⟨reference, environment, binding, by simpa [functions] using found, by simpa [StandardObjectBinding] using standard⟩
  · rw [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp frame.collectorFound).1]
    exact frame.collectorFound
  · intro reference protectedRef object found parent prototype
    exact (safe parent).mpr (frame.protectedParents reference ((safe reference).mp protectedRef) object (by simpa [objects] using found) parent prototype)
  · intro record member
    have shape := frame.recordsFound record member
    refine ⟨by simpa [objects] using shape.found, shape.possibleKeys, ?_, shape.separate,
      by simpa [objects] using shape.resettable, shape.unique, shape.legalKeys, shape.keyBound⟩
    rw [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp shape.keysFound).1]
    exact shape.keysFound
  · intro record member parent prototype
    exact (safe parent).mpr (frame.handlerParents record member parent prototype)
  · intro count inside
    obtain ⟨row, chosen, atRow, protectedRow, choice, admitted⟩ := frame.rowChoices count inside
    refine ⟨row, chosen, atRow, (safe row).mpr protectedRow, ?_, admitted⟩
    simpa only [SearchEntry.Choice, capturedView, objects] using choice

theorem sources_same_objects (before after : State) (records : List Record) (parent : Nat) (q : Value)
    (objects : after.objects = before.objects) (sources : TwoSourceReads before records parent q) : TwoSourceReads after records parent q := by
  refine ⟨by simpa [Protected, objects] using sources.nodeProtected, ?_, ?_⟩
  · intro reference same
    simpa [Protected, objects] using sources.parameterProtected reference same
  · intro record member key used
    obtain ⟨parameter, node⟩ := sources.reads record member key used
    exact ⟨parameterRead_same_objects before after key q _ objects parameter, by simpa [objects] using node⟩

def matchAmbient (before : State) (input : JSString) : State :=
  {before with
    environment := ("m", .array before.heap.length) :: before.environment
    heap := before.heap ++ [[.string input]]}

theorem success_ambient (before : RegExpCallState) (input : JSString) (accepted : DigitsLanguage input) :
    (resultState before input).ambient = matchAmbient before.ambient input := by
  have admitted : RangeRegExp.Accepted 48 57 input := accepted
  simp [resultState, callState, returnedValue, rangeExecState, rangeExecValue, admitted, matchAmbient]

theorem inputs_after_init (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool) (freshObject : OrdinaryObject)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable) :
    Inputs {before with ambient := NodeParamsInit.mapState before.ambient freshObject} methods functions members builtins matcher handle input record object last writable := by
  refine ⟨?_, ?_, ?_, inputs.noArgBeforeMember, inputs.privateBeforeMember, inputs.functionsBeforeMember,
    inputs.membersBeforeBuiltin, inputs.handleBound, inputs.identity, inputs.brand, inputs.initialized, ?_, inputs.lastIndex, inputs.numericBound⟩
  · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.matcherBinding
  · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.inputBinding
  · obtain ⟨write, enumerable, configurable, depth, path, bound⟩ := inputs.current
    exact ⟨write, enumerable, configurable, depth, NodeCaptureGuard.descriptor_path_append before.ambient.objects [freshObject] NodeExecCall.execKey matcher _ depth path, bound⟩
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp inputs.objectFound).1).trans inputs.objectFound

/-- Before156 target structure, without an m binding or match cell. -/
structure GuardTarget (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop extends NodeCaptureGuard.HeaderInputs before params object name where
  absent : object.own.lookup name = none
  path : NodeCaptureGuard.DescriptorPath before.objects name params descriptor depth
  bound : depth ≤ propertyFuel

theorem computed_guard_inputs (before : State) (input : JSString) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat) (target : GuardTarget before params object name descriptor depth) :
    NodeCaptureGuard.AbsentInputs (matchAmbient before input) params object name before.heap.length [.string input] input descriptor depth := by
  refine ⟨⟨?_, ?_, ?_, target.found, target.wellFormed⟩, target.absent, rfl, ?_, rfl, ?_, target.path, target.bound⟩
  · simpa [StandardObjectBinding, matchAmbient, List.lookup_cons] using target.standardObject
  · simpa [matchAmbient, List.lookup_cons] using target.paramsBinding
  · simpa [matchAmbient, List.lookup_cons] using target.nameBinding
  · simp [matchAmbient]
  · change 1 ≤ maximumArrayLength
    decide

/-- Real builtin156 produces m before the actual guard consumes it. The
accepted premise concerns the INITIAL input language, not a matcher output.
Failure remains covered by source_exec_satisfies without any guard target facts. -/
theorem source_builtin_then_guard_satisfies (extra : Nat) (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool) (params : Nat) (paramsObject : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable)
    (accepted : DigitsLanguage input) (target : GuardTarget before.ambient params paramsObject name descriptor depth) :
    sourceExec (extra + 20) methods functions members builtins before = some (.ok (resultState before input)) ∧
    Contract (extra + 20) before (resultState before input) matcher handle input object last writable ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard (extra + 27) (resultState before input).ambient = some outcome ∧
      NodeCaptureGuard.GuardContract (resultState before input).ambient params paramsObject name outcome := by
  obtain ⟨run, contract⟩ := source_exec_satisfies extra before methods functions members builtins matcher handle input record object last writable inputs
  have guard := NodeCaptureGuard.source_absent_satisfies extra _ params paramsObject name before.ambient.heap.length [.string input] input descriptor depth
    (computed_guard_inputs before.ambient input params paramsObject name descriptor depth target)
  exact ⟨run, contract, by simpa [success_ambient before input accepted] using guard⟩

/-- Transport actual fresh-map physical facts through the computed match array.
The env now has m BEFORE params, matching123→156 exactly; no reordering occurs. -/
theorem match_map_sources (before : State) (object : OrdinaryObject) (closure : PrivateMethodClosure)
    (rows initial : List Value) (query : JSString) (collector keyBound parent : Nat) (records : List Record) (root : JSString → Value) (input : JSString)
    (frame : TwoSourceFrame before closure.environment rows query collector keyBound records initial)
    (parentProtected : Protected before records parent) (rootProtected : Protected before records 0)
    (parentReads : NodeCaptureCollect.ParentReads before records parent) (rootReads : NodeCaptureCollect.RootReads before records root)
    (ready : SpreadTargetReady object) (prototype : object.prototype = some 0) :
    TwoSource (matchAmbient (NodeParamsInit.mapState before object) input) closure.environment rows query collector keyBound
      (NodeCaptureCollect.readRecords records object root) parent (.object before.objects.length) initial := by
  have facts := NodeCaptureCollect.fresh_map_sources before object closure rows initial query collector keyBound parent records root
    frame parentProtected rootProtected parentReads rootReads ready prototype
  exact ⟨frame_heap_append _ _ closure.environment rows initial query collector keyBound _ [[.string input]] facts.frame rfl rfl rfl,
    sources_same_objects (NodeParamsInit.mapState before object) (matchAmbient (NodeParamsInit.mapState before object) input) _ parent (.object before.objects.length) rfl facts.sources⟩

def installed_match_map (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure) (receiver handle : Nat)
    (object : OrdinaryObject) (input : JSString) (installed : NodeCaptureCollect.Installed before table closure receiver handle) :
    NodeCaptureCollect.Installed (matchAmbient (NodeParamsInit.mapState before object) input) table closure receiver handle := by
  let mapped := NodeCaptureCollect.installed_map before table closure receiver handle object installed
  exact ⟨mapped.identity, mapped.scope, mapped.receiverFound, mapped.method, mapped.source, mapped.separate, mapped.handleBound, mapped.closureFound⟩

theorem storage_match_map (before : State) (closure : PrivateMethodClosure) (child slot methods collector : Nat) (rows : List Value)
    (object : OrdinaryObject) (input : JSString) (stored : NodeCaptureCollect.Storage before closure child slot methods collector rows) :
    NodeCaptureCollect.Storage (matchAmbient (NodeParamsInit.mapState before object) input) closure child slot methods collector rows := by
  have mapped := NodeCaptureCollect.storage_map before closure child slot methods collector rows object stored
  refine ⟨mapped.childFound, mapped.scope, mapped.data, ?_, mapped.separate, mapped.legal⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored.rowsFound).1).trans stored.rowsFound

theorem call_after_match_map (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent keyBound : Nat)
    (rows initial : List Value) (query : JSString) (records : List Record) (root : JSString → Value) (object : OrdinaryObject) (input : JSString)
    (inputs : NodeCaptureCollect.EntryInputs before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root)
    (ready : SpreadTargetReady object) (prototype : object.prototype = some 0) :
    ∃ after, NodeCaptureCollect.sourceCall (rows.length + keyBound + 103) table (matchAmbient (NodeParamsInit.mapState before object) input) = some (.ok (.undefined, after)) ∧
      NodeCaptureCollect.Contract (matchAmbient (NodeParamsInit.mapState before object) input) after closure receiver child slot methods collector parent before.objects.length rows initial query := by
  obtain ⟨installed⟩ := inputs.installed
  have writable := NodeParamsInit.map_child_writable before node parentIdentity (.object parent) object inputs.parentData
  have reads : NodeCaptureCollect.CallReads (matchAmbient (NodeParamsInit.mapState before object) input) receiver node parentIdentity child collector parent before.objects.length query := by
    refine ⟨inputs.thisValue, ?_, ?_, ?_, ?_, ⟨writable.scope, writable.allocated, writable.data⟩, ?_⟩
    · simpa [matchAmbient, NodeParamsInit.mapState, List.lookup_cons] using inputs.collectorBinding
    · simpa [matchAmbient, NodeParamsInit.mapState, List.lookup_cons] using inputs.childBinding
    · simpa [matchAmbient, NodeParamsInit.mapState, List.lookup_cons] using inputs.methodBinding
    · simpa [matchAmbient, NodeParamsInit.mapState, List.lookup_cons] using inputs.nodeBinding
    · rfl
  exact NodeCaptureCollect.source_call_satisfies _ table closure receiver handle node parentIdentity child slot methods collector parent before.objects.length keyBound rows initial query
    (NodeCaptureCollect.readRecords records object root) (installed_match_map before table closure receiver handle object input installed) reads
    (storage_match_map before closure child slot methods collector rows object input inputs.stored)
    (match_map_sources before object closure rows initial query collector keyBound parent records root input inputs.frame inputs.parentProtected inputs.rootProtected
      inputs.parentReads inputs.rootReads ready prototype)

theorem written_match_map_eq (before : State) (object : OrdinaryObject) (input name : JSString) :
    NodeCaptureGuard.writtenState (matchAmbient (NodeParamsInit.mapState before object) input) before.objects.length object name input =
      matchAmbient (NodeParamsInit.mapState before (newDataObject object name (.string input))) input := by
  simp [NodeCaptureGuard.writtenState, matchAmbient, NodeParamsInit.mapState, List.set_append_right]

/-- Selected source order123→builtin156→actual188B158–161. The only regex
condition is the independent language of the INITIAL argument. The match array,
q, guard write, actual target rows and helper Layout are derived; m is never
staged before123. Header157 is tested, not given an invented upstream body.
The three selected activations omit146–154/current tuple production/traversal.
Constructor/getPattern/native brand correspondence remain declared boundaries. -/
theorem source_init_builtin_created_collect_satisfies (extra : Nat) (before : RegExpCallState)
    (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable) (builtins : RegExpBuiltinTable)
    (matcher builtinHandle : Nat) (input : JSString) (record : RangeRegExpRecord) (matcherObject : OrdinaryObject) (last : Int) (writable : Bool)
    (closure : PrivateMethodClosure) (receiver handle node parentIdentity child slot methodArray collector parent empty keyBound initFuel : Nat)
    (rows initial : List Value) (query name : JSString) (records : List Record) (root : JSString → Value) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (execInputs : Inputs before methods functions members builtins matcher builtinHandle input record matcherObject last writable)
    (entry : NodeCaptureCollect.EntryInputs before.ambient methods closure receiver handle node parentIdentity child slot methodArray collector parent keyBound rows initial query records root)
    (initializer : NodeCaptureCollect.InitInputs before.ambient node parentIdentity parent empty object initFuel)
    (standard : StandardObjectBinding before.ambient) (nameBinding : before.ambient.environment.lookup "name" = some (.string name))
    (absent : object.own.lookup name = none)
    (rootPath : NodeCaptureGuard.DescriptorPath before.ambient.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel)
    (classified : NodeCaptureGuard.action descriptor true = .create) (accepted : DigitsLanguage input) :
    let initializedAmbient := NodeParamsInit.mapState before.ambient object
    let initialized := {before with ambient := initializedAmbient}
    let computed := resultState initialized input
    let guarded := matchAmbient (NodeParamsInit.mapState before.ambient (newDataObject object name (.string input))) input
    NodeParamsInit.sourceInit initFuel before.ambient = some (.ok initializedAmbient) ∧
    NodeParamsInit.InitContract before.ambient initializedAmbient node parentIdentity parent empty ∧
    sourceExec (extra + 20) methods functions members builtins initialized = some (.ok computed) ∧
    Contract (extra + 20) initialized computed matcher builtinHandle input matcherObject last writable ∧
    evalExpression (extra + 1) defaultSplitLimit guardCondition computed.ambient = .ok (.array before.ambient.heap.length, computed.ambient) ∧
    ∃ after, NodeCaptureCollect.sourceCollect (rows.length + keyBound + 106) methods computed.ambient = some (.ok (.normal after)) ∧
      NodeCaptureGuard.GuardContract computed.ambient before.ambient.objects.length object name (.ok (.normal guarded)) ∧
      NodeCaptureCollect.Contract guarded after closure receiver child slot methodArray collector parent before.ambient.objects.length rows initial query ∧
      after.heap[before.ambient.heap.length]? = some [.string input] ∧
      observeRegExpResult {computed with ambient := after} before.ambient.heap.length .groups = some (.data .undefined true true true) ∧
      observeRegExpResult {computed with ambient := after} before.ambient.heap.length .zero = some (.data (.string input) true true true) := by
  dsimp only
  obtain ⟨initRun, initContract, ready, well, prototype⟩ := NodeCaptureCollect.init_inputs_satisfies before.ambient node parentIdentity parent empty object initFuel initializer
  let initialized : RegExpCallState := {before with ambient := NodeParamsInit.mapState before.ambient object}
  obtain ⟨execRun, execContract⟩ := source_exec_satisfies extra initialized methods functions members builtins matcher builtinHandle input record matcherObject last writable
    (inputs_after_init before methods functions members builtins matcher builtinHandle input record matcherObject last writable object execInputs)
  have computedAmbient := success_ambient initialized input accepted
  have target : GuardTarget (NodeParamsInit.mapState before.ambient object) before.ambient.objects.length object name descriptor (depth + 1) :=
    ⟨NodeCaptureCollect.map_guard_header before.ambient object name well standard nameBinding, absent,
      .parent (by simp [NodeParamsInit.mapState]) absent prototype
        (NodeCaptureGuard.descriptor_path_append before.ambient.objects [object] name 0 descriptor depth rootPath), pathBound⟩
  have guard := computed_guard_inputs _ input before.ambient.objects.length object name descriptor (depth + 1) target
  have condition := NodeCaptureGuard.eval_condition (rows.length + keyBound + 96) _ before.ambient.objects.length object name guard.toHeaderInputs
  simp only [absent, Option.isSome_none, Bool.not_false] at condition
  have assigned := NodeCaptureGuard.execute_assignment (rows.length + keyBound + 77) _ before.ambient.objects.length object name
    before.ambient.heap.length [.string input] input descriptor (depth + 1) guard
  rw [ready.extensible, classified, written_match_map_eq] at assigned
  obtain ⟨after, called, contract⟩ := call_after_match_map before.ambient methods closure receiver handle node parentIdentity child slot methodArray collector parent keyBound
    rows initial query records root (newDataObject object name (.string input)) input entry
    (newDataObject_spreadReady object name (.string input) ready) prototype
  have created := NodeCaptureGuard.created_contract _ before.ambient.objects.length object name input guard.found
  rw [written_match_map_eq] at created
  have combined := NodeCaptureCollect.collect_after_guard (rows.length + keyBound) methods _ _ after true condition ⟨.string input, assigned⟩ called
  have untouched : after.heap[before.ambient.heap.length]? = some [.string input] := by
    have oldCollector := (List.getElem?_eq_some_iff.mp entry.frame.collectorFound).1
    rw [contract.arrays before.ambient.heap.length (by omega)]
    simp [matchAmbient, NodeParamsInit.mapState]
  have groups : observeRegExpResult {(resultState initialized input) with ambient := after} before.ambient.heap.length .groups = some (.data .undefined true true true) := by
    have admitted : RangeRegExp.Accepted 48 57 input := accepted
    simp [observeRegExpResult, resultState, callState, rangeExecState, admitted, initialized, NodeParamsInit.mapState, observeRegExpMatch, untouched]
  have zero : observeRegExpResult {(resultState initialized input) with ambient := after} before.ambient.heap.length .zero = some (.data (.string input) true true true) := by
    have admitted : RangeRegExp.Accepted 48 57 input := accepted
    simp [observeRegExpResult, resultState, callState, rangeExecState, admitted, initialized, NodeParamsInit.mapState, observeRegExpMatch, untouched]
  have header := (produced_guard_test extra initialized input).1
  have result : returnedValue initialized input = .array before.ambient.heap.length := by
    have admitted : RangeRegExp.Accepted 48 57 input := accepted
    simp [returnedValue, rangeExecValue, admitted, initialized, NodeParamsInit.mapState]
  rw [result] at header
  refine ⟨initRun, initContract, execRun, execContract, header, after, ?_, ?_, contract, untouched, groups, zero⟩
  · exact (congrArg (NodeCaptureCollect.sourceCollect (rows.length + keyBound + 106) methods) computedAmbient).trans combined
  · let finish := matchAmbient (NodeParamsInit.mapState before.ambient (newDataObject object name (.string input))) input
    have normal : NodeCaptureGuard.GuardContract (matchAmbient (NodeParamsInit.mapState before.ambient object) input)
        before.ambient.objects.length object name (.ok (.normal finish)) :=
      .created before.ambient.heap.length [.string input] input descriptor (depth + 1) guard
        (by simpa [ready.extensible] using classified) _ created
    have equality := congrArg (fun state : State => NodeCaptureGuard.GuardContract state before.ambient.objects.length object name (.ok (.normal finish))) computedAmbient
    exact Eq.mpr equality normal


/-- info: 'HonoLean.Upstream.NodeRegExpExec.source_builtin_then_guard_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_builtin_then_guard_satisfies
/-- info: 'HonoLean.Upstream.NodeRegExpExec.match_map_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms match_map_sources
/-- info: 'HonoLean.Upstream.NodeRegExpExec.source_init_builtin_created_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_builtin_created_collect_satisfies

end HonoLean.Upstream.NodeRegExpExec
