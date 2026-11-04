import HonoLean.Upstream.GetPatternInvocation.Contract
import HonoLean.Upstream.GetPatternInvocation.Program

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternInvocation
open SourceSubset hiding pinnedSource
open ECMA2025 LexicalArrow
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

theorem binding_path_resolves (before : Runtime) (name : String) (environment cell depth : Nat)
    (path : BindingPath before.environments name environment cell depth) (fuel : Nat) (bound : depth < fuel) :
    resolveBinding fuel before environment name = .ok cell := by
  induction path generalizing fuel with
  | here found lookup =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [resolveBinding, found, lookup]
  | parent found lookup parent path ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [resolveBinding, found, lookup, parent, ih fuel (by omega)]

theorem cell_value_reads (before : Runtime) (environment : Nat) (name : String) (value : Value)
    (inputs : CellValue before environment name value) :
    getBindingValue (before.environments.length + 1) before environment name = .ok value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  simp [getBindingValue, binding_path_resolves before name environment cell depth path _ bound, found]

theorem binding_path_flattens (before : Runtime) (name : String) (environment cell depth : Nat)
    (path : BindingPath before.environments name environment cell depth) (fuel : Nat) (bound : depth < fuel) :
    (flattenBindings fuel before environment).lookup name = some cell := by
  induction path generalizing fuel with
  | here found lookup =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [flattenBindings, found, List.lookup_append, lookup]
  | parent found lookup parent path ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [flattenBindings, found, List.lookup_append, lookup, parent, ih fuel (by omega)]

private theorem lookup_map_values {α β : Type} (bindings : List (String × α)) (name : String) (mapValue : α → β) :
    (bindings.map (fun (key, value) => (key, mapValue value))).lookup name = (bindings.lookup name).map mapValue := by
  induction bindings with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    simp only [List.map_cons, List.lookup_cons, ih]
    split <;> rfl

/-- The lossy legacy projection is adequate for this particular ready cell.
Live evaluation itself continues to use `getBindingValue` at every read. -/
theorem cell_value_projects (before : Runtime) (environment : Nat) (name : String) (value : Value)
    (inputs : CellValue before environment name value) :
    (projectEnvironment (before.environments.length + 1) before environment).lookup name = some value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  rw [projectEnvironment, lookup_map_values (flattenBindings (before.environments.length + 1) before environment) name
    (fun reference => ((before.cells[reference]?).bind Cell.value).getD .undefined),
    binding_path_flattens before name environment cell depth path _ bound]
  simp [found]

theorem cell_value_ready (before : Runtime) (environment : Nat) (name : String) (value : Value)
    (inputs : CellValue before environment name value) :
    (readyEnvironment (before.environments.length + 1) before environment).lookup name = some value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  rw [readyEnvironment, readyBindings_lookup,
    binding_path_flattens before name environment cell depth path _ bound]
  simp [found]

theorem binding_path_append (environments : List Environment) (extra : List Environment) (name : String)
    (environment cell depth : Nat) (path : BindingPath environments name environment cell depth) :
    BindingPath (environments ++ extra) name environment cell depth := by
  induction path with
  | here found lookup =>
    exact .here ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found) lookup
  | parent found lookup parent path ih =>
    exact .parent ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found) lookup parent ih

/-- Initial lexical values survive an actual append-only activation/local
extension. This is an internal structural lemma, not a future-read premise. -/
theorem cell_value_append (before after : Runtime) (extraEnvironments : List Environment) (extraCells : List Cell)
    (environments : after.environments = before.environments ++ extraEnvironments)
    (cells : after.cells = before.cells ++ extraCells) (environment : Nat) (name : String) (value : Value)
    (inputs : CellValue before environment name value) : CellValue after environment name value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  refine ⟨cell, kind, depth, ?_, ?_, ?_⟩
  · rw [environments]
    exact binding_path_append before.environments extraEnvironments name environment cell depth path
  · rw [environments, List.length_append]
    omega
  · rw [cells]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem arrow_object_metadata (functionPrototype : Nat) :
    FunctionObjectContract (arrowObject GetPatternBody.declaration functionPrototype) := by
  exact ⟨rfl, rfl, rfl⟩

def callActivation (before : Runtime) (closure : ArrowClosure) (arguments : List Value) : Runtime :=
  {before with
    cells := before.cells ++ parameterCells GetPatternBody.declaration.parameters arguments
    environments := before.environments ++
      [⟨parameterBindings GetPatternBody.declaration.parameters before.cells.length, some closure.environment⟩]
    current := before.environments.length
    thisValue := closure.lexicalThis}

def callEntry (before : Runtime) (closure : ArrowClosure) (arguments : List Value) : Runtime :=
  let activation := callActivation before closure arguments
  withAmbient activation {activation.data.base.regexp.ambient with
    environment := readyEnvironment (activation.environments.length + 1) activation activation.current
    thisValue := closure.lexicalThis}

def callCaller (before : Runtime) : Caller :=
  ⟨before.current, before.thisValue, before.data.base.regexp.ambient.environment, before.data.base.regexp.ambient.thisValue⟩

theorem enter_call (before : Runtime) (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value)
    (inputs : CallableInputs before handle closure) :
    enterCall handle arguments before = .ok (callCaller before, callEntry before closure arguments) := by
  simp [enterCall, inputs.found, inputs.program, callCaller, callEntry, callActivation]

theorem entry_environment (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    (callEntry before closure arguments).data.base.regexp.ambient.environment =
      readyEnvironment ((callEntry before closure arguments).environments.length + 1)
        (callEntry before closure arguments) (callEntry before closure arguments).current := by
  rw [ready_environment_store_congr _ (callEntry before closure arguments) (callActivation before closure arguments) _ rfl rfl]
  rfl

theorem entry_agrees (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    EnvironmentAgrees (callEntry before closure arguments) :=
  ready_environment_agrees _ (entry_environment before closure arguments)

theorem entry_arrays (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    (callEntry before closure arguments).data.base.regexp.ambient.heap = before.data.base.regexp.ambient.heap := rfl

theorem actual_body : GetPatternBody.declaration.body = GetPatternBody.program := rfl

theorem entry_label_cell (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    CellValue (callEntry before closure arguments) before.environments.length "label" (argument arguments 0) := by
  refine ⟨before.cells.length, .parameter, 0, ?_, ?_, ?_⟩
  · exact .here (frame := ⟨[("label", before.cells.length), ("next", before.cells.length + 1)], some closure.environment⟩)
      (by simp [callEntry, callActivation, withAmbient, withData, actual_parameter_bindings]) rfl
  · simp [callEntry, callActivation, withAmbient, withData]
  · simp [callEntry, callActivation, withAmbient, withData, actual_parameters, argument]

theorem entry_next_cell (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    CellValue (callEntry before closure arguments) before.environments.length "next" (argument arguments 1) := by
  refine ⟨before.cells.length + 1, .parameter, 0, ?_, ?_, ?_⟩
  · exact .here (frame := ⟨[("label", before.cells.length), ("next", before.cells.length + 1)], some closure.environment⟩)
      (by simp [callEntry, callActivation, withAmbient, withData, actual_parameter_bindings]) rfl
  · simp [callEntry, callActivation, withAmbient, withData]
  · simp [callEntry, callActivation, withAmbient, withData, actual_parameters, argument]

theorem entry_free_cell (before : Runtime) (closure : ArrowClosure) (arguments : List Value) (name : String) (value : Value)
    (labelDifferent : name ≠ "label") (nextDifferent : name ≠ "next")
    (inputs : CellValue before closure.environment name value) :
    CellValue (callEntry before closure arguments) before.environments.length name value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  refine ⟨cell, kind, depth + 1, ?_, ?_, ?_⟩
  · refine .parent (frame := ⟨[("label", before.cells.length), ("next", before.cells.length + 1)], some closure.environment⟩)
      (by simp [callEntry, callActivation, withAmbient, withData, actual_parameter_bindings])
      (by simp [labelDifferent, nextDifferent]) rfl ?_
    exact binding_path_append before.environments _ name closure.environment cell depth path
  · simp only [callEntry, callActivation, withAmbient, withData, List.length_append, List.length_cons, List.length_nil]
    omega
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem entry_realm (before : Runtime) (closure : ArrowClosure) (arguments : List Value) (context : LabelMatchContext)
    (realm : LabelRealm before.data context) : LabelRealm (callEntry before closure arguments).data context := by
  cases realm
  constructor <;> assumption

theorem entry_header (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before context handle closure arguments input name body next cache object descriptor depth) :
    PatternCache.HeaderInputs (callEntry before closure arguments).data context input name body next cache object descriptor depth := by
  refine ⟨⟨entry_realm before closure arguments context.label inputs.realm, ?_⟩,
    inputs.label, ?_, ?_, inputs.cacheFound, inputs.path, inputs.pathBound⟩
  · have label := cell_value_ready _ _ _ _ (entry_label_cell before closure arguments)
    rw [inputs.arguments.label] at label
    rw [entry_environment]
    exact label
  · have next := cell_value_ready _ _ _ _ (entry_next_cell before closure arguments)
    rw [inputs.arguments.next] at next
    rw [entry_environment]
    exact next
  · rw [entry_environment]
    exact cell_value_ready _ _ _ _ (entry_free_cell before closure arguments "patternCache" _
      (by decide) (by decide) inputs.cacheCell)

theorem entry_plain_inputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context handle closure arguments input name next cache object descriptor depth) :
    PatternCache.PlainInputs (callEntry before closure arguments).data context input name next cache object descriptor depth :=
  ⟨entry_header before context handle closure arguments input name none next cache object descriptor depth inputs.toHeaderInputs,
    inputs.falsy, inputs.writable⟩

theorem entry_warm_inputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context handle closure arguments input name body next cache object value writable enumerable configurable depth) :
    PatternCache.WarmInputs (callEntry before closure arguments).data context input name body next cache object value writable enumerable configurable depth :=
  ⟨entry_header before context handle closure arguments input name body next cache object _ depth inputs.toHeaderInputs, inputs.truthy⟩

theorem entry_terminal_inputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : TerminalInputs before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject) :
    PatternCacheTerminal.Inputs (callEntry before closure arguments).data context name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject := by
  refine ⟨entry_header before context handle closure arguments _ name _ next cache object descriptor depth inputs.toHeaderInputs,
    inputs.terminal, inputs.validName, inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.falsy, inputs.writable,
    ?_, inputs.handleBound, inputs.identity, inputs.prototypeFound⟩
  rw [entry_environment]
  exact cell_value_ready _ _ _ _ (entry_free_cell before closure arguments "RegExp" _ (by decide) (by decide) inputs.constructorCell)

def callerData (caller data : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient data {data.base.regexp.ambient with
    environment := caller.base.regexp.ambient.environment
    thisValue := caller.base.regexp.ambient.thisValue}

theorem entry_caller_data (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    callerData before.data (callEntry before closure arguments).data = before.data := rfl

theorem frames_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (frames : PatternCache.Frames before after context input) :
    PatternCache.Frames (callerData caller before) (callerData caller after) context input :=
  ⟨rfl, frames.functions, frames.privates, frames.sets, rfl, frames.rangeBrands, frames.rangeResults,
   frames.iteratorSymbols, frames.iterators, frames.iteratorTrace, frames.labelSymbols, frames.accessors,
   frames.labelBrands, frames.labelResults, frames.trace⟩

theorem plain_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (input name : JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (returned : Value)
    (contract : PatternCache.PlainContract before after context input name next cache object returned) :
    PatternCache.PlainContract (callerData caller before) (callerData caller after) context input name next cache object returned :=
  ⟨contract.returned, contract.captures, contract.objects, contract.cacheOwn, contract.otherObjects,
   contract.oldArrays, frames_caller_data caller before after context input contract.frames⟩

theorem warm_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (cache : Nat) (retained returned : Value)
    (contract : PatternCache.WarmContract before after context input name body cache retained returned) :
    PatternCache.WarmContract (callerData caller before) (callerData caller after) context input name body cache retained returned :=
  ⟨contract.returned, contract.cacheObject, contract.captures, contract.objects, contract.oldArrays,
   frames_caller_data caller before after context input contract.frames⟩

theorem miss_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (input : JSString) (returned : Value)
    (contract : PatternCache.MissContract before after context input returned) :
    PatternCache.MissContract (callerData caller before) (callerData caller after) context input returned :=
  ⟨contract.returned, contract.arrays, contract.objects, frames_caller_data caller before after context input contract.frames⟩

theorem terminal_frames_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (lower upper : UInt16) (frames : PatternCacheTerminal.Frames before after context input lower upper) :
    PatternCacheTerminal.Frames (callerData caller before) (callerData caller after) context input lower upper :=
  ⟨rfl, frames.functions, frames.privates, frames.sets, rfl, frames.rangeBrands, frames.rangeResults,
   frames.iteratorSymbols, frames.iterators, frames.iteratorTrace, frames.labelSymbols, frames.accessors,
   frames.labelBrands, frames.labelResults, frames.trace⟩

theorem terminal_caller_data (caller before after : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) (returned : Value)
    (contract : PatternCacheTerminal.Contract before after context name lower upper next cache object prototype returned) :
    PatternCacheTerminal.Contract (callerData caller before) (callerData caller after) context name lower upper next cache object prototype returned :=
  ⟨contract.resultValue, contract.arrays, contract.objects, contract.cacheOwn, contract.regexFound, contract.lastIndex,
   contract.internal, contract.source, contract.flags, contract.compiled, contract.language, contract.otherObjects,
   contract.oldArrays, terminal_frames_caller_data caller before after context _ lower upper contract.frames⟩

theorem entry_store (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    StoreExtension before (callEntry before closure arguments) := by
  refine ⟨?_, ?_, ?_⟩
  · intro reference cell found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · intro reference frame found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · simp [callEntry, callActivation, withAmbient, withData]

theorem returned_frame (before : Runtime) (closure : ArrowClosure) (arguments : List Value) (after : Runtime)
    (frame : ExecutionFrame (callEntry before closure arguments) after) :
    CallFrame before (restoreCaller (callCaller before) after) := by
  have extension := StoreExtension.trans before (callEntry before closure arguments) after
    (entry_store before closure arguments) frame.store
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, extension.length, frame.closures⟩
  · intro reference bound
    have found := List.getElem?_eq_getElem bound
    exact (extension.cells reference _ found).trans found.symm
  · intro reference bound
    have found := List.getElem?_eq_getElem bound
    exact (extension.environments reference _ found).trans found.symm

def wildcardWorld (before : Runtime) (closure : ArrowClosure) (arguments : List Value) : Runtime :=
  restoreCaller (callCaller before) (callEntry before closure arguments)

theorem wildcard_contract (before : Runtime) (closure : ArrowClosure) (arguments : List Value) :
    WildcardContract before (wildcardWorld before closure arguments) GetPatternBody.star := by
  refine ⟨rfl, rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · intro reference bound
    exact List.getElem?_append_left bound
  · intro reference bound
    exact List.getElem?_append_left bound
  · simp [wildcardWorld, restoreCaller, callCaller, callEntry, callActivation, withAmbient, withData]

/-- A real call binds parameters and restores its caller. No next/cache/global
cell, object heap, realm, constructor or ghost-readiness premise is needed. -/
theorem invoke_wildcard_satisfies (extra limit : Nat) (context : PatternCacheContext)
    (before : Runtime) (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value)
    (inputs : WildcardInputs before handle closure arguments) :
    invoke (extra + 5) limit context handle arguments before =
      .returned GetPatternBody.star (wildcardWorld before closure arguments) ∧
    WildcardContract before (wildcardWorld before closure arguments) GetPatternBody.star := by
  have label := cell_value_reads _ _ _ _ (entry_label_cell before closure arguments)
  rw [inputs.label] at label
  have body := wildcard_run extra limit context (callEntry before closure arguments) label
  constructor
  · simp [invoke, enter_call before handle closure arguments inputs.toCallableInputs,
      inputs.found, inputs.program, actual_body, body, wildcardWorld]
  · exact wildcard_contract before closure arguments

private theorem invoke_from_run (fuel limit : Nat) (context : PatternCacheContext)
    (before : Runtime) (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value)
    (value : Value) (after : Runtime) (inputs : CallableInputs before handle closure)
    (body : run fuel limit context GetPatternBody.program (callEntry before closure arguments) = .ok (value, after)) :
    invoke fuel limit context handle arguments before = .returned value (restoreCaller (callCaller before) after) := by
  simp [invoke, enter_call before handle closure arguments inputs, inputs.found, inputs.program, actual_body, body]

theorem invoke_plain_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context handle closure arguments input name next cache object descriptor depth) :
    ∃ after, invoke (extra + 257) defaultSplitLimit context handle arguments before =
        .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) after ∧
      PlainContract before after context input name next cache object (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  let entry := callEntry before closure arguments
  have ready := entry_plain_inputs before context handle closure arguments input name next cache object descriptor depth inputs
  obtain ⟨source, contract⟩ := GetPatternBody.source_plain_satisfies extra entry.data context input name next cache object descriptor depth ready
  have old : runPatternCache (extra + 257) defaultSplitLimit context GetPatternBody.program entry.data =
      .ok (.array (before.data.base.regexp.ambient.heap.length + 1), PatternCache.plainState entry.data context input name next cache object) :=
    Option.some.inj (by simpa only [GetPatternBody.sourceBody, GetPatternBody.parses_body, Option.map_some, entry, entry_arrays] using source)
  obtain ⟨after, live, data, frame, _, _⟩ := run_refines (extra + 257) 128 defaultSplitLimit context GetPatternBody.program entry
    _ _ actual_call_program_profile (entry_agrees before closure arguments) old
  refine ⟨restoreCaller (callCaller before) after,
    invoke_from_run _ _ context before handle closure arguments _ after inputs.toHeaderInputs.toCallableInputs live, ?_⟩
  refine ⟨?_, returned_frame before closure arguments after frame⟩
  change PatternCache.PlainContract before.data (callerData before.data after.data) context input name next cache object _
  rw [data]
  simpa only [entry, entry_caller_data, entry_arrays] using plain_caller_data before.data entry.data _ context input name next cache object _ contract

theorem invoke_warm_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context handle closure arguments input name body next cache object value writable enumerable configurable depth) :
    ∃ after, invoke (extra + 257) defaultSplitLimit context handle arguments before = .returned value after ∧
      WarmContract before after context input name body cache value value := by
  let entry := callEntry before closure arguments
  have ready := entry_warm_inputs before context handle closure arguments input name body next cache object value writable enumerable configurable depth inputs
  obtain ⟨source, contract⟩ := GetPatternBody.source_warm_satisfies extra entry.data context input name body next cache object value writable enumerable configurable depth ready
  have old : runPatternCache (extra + 257) defaultSplitLimit context GetPatternBody.program entry.data =
      .ok (value, PatternCache.warmState entry.data context input) :=
    Option.some.inj (by simpa only [GetPatternBody.sourceBody, GetPatternBody.parses_body, Option.map_some, entry, entry_arrays] using source)
  obtain ⟨after, live, data, frame, _, _⟩ := run_refines (extra + 257) 128 defaultSplitLimit context GetPatternBody.program entry
    _ _ actual_call_program_profile (entry_agrees before closure arguments) old
  refine ⟨restoreCaller (callCaller before) after,
    invoke_from_run _ _ context before handle closure arguments _ after inputs.toHeaderInputs.toCallableInputs live, ?_⟩
  refine ⟨?_, returned_frame before closure arguments after frame⟩
  change PatternCache.WarmContract before.data (callerData before.data after.data) context input name body cache value value
  rw [data]
  simpa only [entry, entry_caller_data] using warm_caller_data before.data entry.data _ context input name body cache value value contract

theorem invoke_miss_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (input : JSString)
    (inputs : MissInputs before context handle closure arguments input) :
    ∃ after, invoke (extra + 257) defaultSplitLimit context handle arguments before = .returned .null after ∧
      MissContract before after context input .null := by
  let entry := callEntry before closure arguments
  have ready : LabelMatch.Inputs entry.data context.label input := by
    refine ⟨entry_realm before closure arguments context.label inputs.realm, ?_⟩
    rw [entry_environment]
    have label := cell_value_ready _ _ _ _ (entry_label_cell before closure arguments)
    rw [inputs.label] at label
    exact label
  obtain ⟨source, contract⟩ := GetPatternBody.source_miss_satisfies extra context entry.data input ready inputs.nonstar inputs.absent
  have old : runPatternCache (extra + 257) defaultSplitLimit context GetPatternBody.program entry.data =
      .ok (.null, PatternCache.warmState entry.data context input) :=
    Option.some.inj (by simpa only [GetPatternBody.sourceBody, GetPatternBody.parses_body, Option.map_some] using source)
  obtain ⟨after, live, data, frame, _, _⟩ := run_refines (extra + 257) 128 defaultSplitLimit context GetPatternBody.program entry
    _ _ actual_call_program_profile (entry_agrees before closure arguments) old
  refine ⟨restoreCaller (callCaller before) after,
    invoke_from_run _ _ context before handle closure arguments _ after inputs.toCallableInputs live, ?_⟩
  refine ⟨?_, returned_frame before closure arguments after frame⟩
  change PatternCache.MissContract before.data (callerData before.data after.data) context input .null
  rw [data]
  simpa only [entry, entry_caller_data] using miss_caller_data before.data entry.data _ context input .null contract

theorem invoke_terminal_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : TerminalInputs before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject) :
    ∃ after, invoke (extra + 257) defaultSplitLimit context handle arguments before =
        .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) after ∧
      TerminalContract before after context name lower upper next cache object constructor.prototype
        (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  let entry := callEntry before closure arguments
  have ready := entry_terminal_inputs before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject inputs
  obtain ⟨source, contract⟩ := GetPatternBody.source_terminal_satisfies extra entry.data context name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject ready
  have old : runPatternCache (extra + 257) defaultSplitLimit context GetPatternBody.program entry.data =
      .ok (.array (before.data.base.regexp.ambient.heap.length + 1),
        PatternCacheTerminal.resultState entry.data context name lower upper next cache object constructor.prototype) :=
    Option.some.inj (by simpa only [GetPatternBody.sourceBody, GetPatternBody.parses_body, Option.map_some, entry, entry_arrays] using source)
  obtain ⟨after, live, data, frame, _, _⟩ := run_refines (extra + 257) 128 defaultSplitLimit context GetPatternBody.program entry
    _ _ actual_call_program_profile (entry_agrees before closure arguments) old
  refine ⟨restoreCaller (callCaller before) after,
    invoke_from_run _ _ context before handle closure arguments _ after inputs.toHeaderInputs.toCallableInputs live, ?_⟩
  refine ⟨?_, returned_frame before closure arguments after frame⟩
  change PatternCacheTerminal.Contract before.data (callerData before.data after.data) context name lower upper next cache object constructor.prototype _
  rw [data]
  simpa only [entry, entry_caller_data, entry_arrays] using terminal_caller_data before.data entry.data _ context name lower upper next cache object constructor.prototype _ contract

def moduleWorld (functionPrototype : Nat) (before : Runtime) : Runtime :=
  {before with
    data := cacheWithAmbient before.data {before.data.base.regexp.ambient with
      environment := ("getPattern", .object (before.data.base.regexp.ambient.objects.length + 1)) ::
        ("patternCache", .object before.data.base.regexp.ambient.objects.length) :: before.data.base.regexp.ambient.environment
      objects := before.data.base.regexp.ambient.objects ++ [emptyLiteralObject, arrowObject GetPatternBody.declaration functionPrototype]}
    cells := before.cells ++
      [⟨.constant, some (.object before.data.base.regexp.ambient.objects.length)⟩,
       ⟨.constant, some (.object (before.data.base.regexp.ambient.objects.length + 1))⟩]
    environments := before.environments ++
      [⟨[("patternCache", before.cells.length)], some before.current⟩,
       ⟨[("getPattern", before.cells.length + 1)], some before.environments.length⟩]
    closures := before.closures ++
      [⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
        before.data.base.regexp.ambient.objects.length + 1⟩]
    current := before.environments.length + 1}

theorem initialize_module (functionPrototype : Nat) (before : Runtime) (root functionRoot : OrdinaryObject)
    (inputs : SetupInputs before functionPrototype root functionRoot) :
    initializeModule PatternCache.initProgram GetPatternBody.declaration functionPrototype before =
      .ok (⟨before.closures.length⟩, moduleWorld functionPrototype before) := by
  have functionFound : (before.data.base.regexp.ambient.objects ++ [emptyLiteralObject])[functionPrototype]? = some functionRoot :=
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp inputs.functionPrototype).1).trans inputs.functionPrototype
  simp [initializeModule, PatternCache.initProgram, reserveConstant, createLiteralObject,
    inputs.objectPrototype, finishConstant, initializeCell, createArrow, functionFound, functionObject,
    withAmbient, withData, cacheWithAmbient, moduleWorld, GetPatternBody.declaration,
    List.set_append_right, List.append_assoc]

theorem module_contract (functionPrototype : Nat) (before : Runtime) :
    SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ := by
  constructor
  case exportCell =>
    refine ⟨before.cells.length + 1, .constant, 0, ?_, ?_, ?_⟩
    · exact .here (frame := ⟨[("getPattern", before.cells.length + 1)], some before.environments.length⟩)
        (by simp [moduleWorld]) rfl
    · simp [moduleWorld]
    · simp [moduleWorld]
  case cacheCell =>
    refine ⟨before.cells.length, .constant, 1, ?_, ?_, ?_⟩
    · refine .parent (frame := ⟨[("getPattern", before.cells.length + 1)], some before.environments.length⟩)
        (by simp [moduleWorld]) rfl rfl ?_
      exact .here (frame := ⟨[("patternCache", before.cells.length)], some before.current⟩)
        (by simp [moduleWorld]) rfl
    · simp [moduleWorld]
    · simp [moduleWorld]
  case metadata => exact arrow_object_metadata functionPrototype
  all_goals rfl

theorem source_setup_satisfies (functionPrototype : Nat) (before : Runtime) (root functionRoot : OrdinaryObject)
    (inputs : SetupInputs before functionPrototype root functionRoot) :
    sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
    SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ := by
  exact ⟨by rw [source_setup_runtime, initialize_module functionPrototype before root functionRoot inputs],
    module_contract functionPrototype before⟩

theorem module_callable (functionPrototype : Nat) (before : Runtime) :
    CallableInputs (moduleWorld functionPrototype before) ⟨before.closures.length⟩
      ⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
        before.data.base.regexp.ambient.objects.length + 1⟩ := by
  exact ⟨by simp [moduleWorld], rfl⟩

private theorem find_fresh_closure (closures : List ArrowClosure) (reference : Nat) (closure : ArrowClosure)
    (different : ∀ previous ∈ closures, previous.objectReference ≠ reference)
    (identity : closure.objectReference = reference) :
    findClosureReference (closures ++ [closure]) reference = some closures.length := by
  induction closures with
  | nil => simp [findClosureReference, identity]
  | cons previous tail ih =>
    have first := different previous (by simp)
    have rest : ∀ entry ∈ tail, entry.objectReference ≠ reference := by
      intro entry member
      exact different entry (by simp [member])
    simp [findClosureReference, first, ih rest, List.length_cons]

/-- The newly exported ordinary-object value resolves to the exact closure
created by this source. Initial allocated-closure identities exclude an older
out-of-heap reference impersonating the new object. -/
theorem module_value_callable (functionPrototype : Nat) (before : Runtime) (root functionRoot : OrdinaryObject)
    (inputs : SetupInputs before functionPrototype root functionRoot) :
    resolveArrowValue (moduleWorld functionPrototype before) (.object (before.data.base.regexp.ambient.objects.length + 1)) =
      .ok ⟨before.closures.length⟩ := by
  have different : ∀ previous ∈ before.closures,
      previous.objectReference ≠ before.data.base.regexp.ambient.objects.length + 1 := by
    intro previous member
    have bounded := inputs.closuresAllocated previous member
    omega
  simp only [resolveArrowValue, moduleWorld]
  rw [find_fresh_closure before.closures _ _ different rfl]

/-- Source export lookup and ordinary-object callability are derived before
using the internal handle API; neither successful invocation nor body execution
is supplied to this bridge. -/
theorem module_export_call (fuel limit functionPrototype : Nat) (before : Runtime) (root functionRoot : OrdinaryObject)
    (context : PatternCacheContext) (arguments : List Value) (inputs : SetupInputs before functionPrototype root functionRoot) :
    invokeBinding fuel limit context (before.environments.length + 1) "getPattern" arguments (moduleWorld functionPrototype before) =
      invoke fuel limit context ⟨before.closures.length⟩ arguments (moduleWorld functionPrototype before) := by
  have binding := cell_value_reads _ _ _ _ (module_contract functionPrototype before).exportCell
  simp only [(module_contract functionPrototype before).current] at binding
  simp [invokeBinding, binding, invokeValue, module_value_callable functionPrototype before root functionRoot inputs]

theorem module_realm (functionPrototype : Nat) (before : Runtime) (context : LabelMatchContext)
    (realm : LabelRealm before.data context) : LabelRealm (moduleWorld functionPrototype before).data context := by
  constructor
  case stringFound =>
    obtain ⟨object, found, own⟩ := realm.stringFound
    exact ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case regexpFound =>
    obtain ⟨object, found, own⟩ := realm.regexpFound
    exact ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case symbolOwners =>
    intro entry member
    have bound := realm.symbolOwners entry member
    change entry.1 < (before.data.base.regexp.ambient.objects ++
      [emptyLiteralObject, arrowObject GetPatternBody.declaration functionPrototype]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  all_goals cases realm <;> assumption

theorem module_cache_path (functionPrototype : Nat) (before : Runtime) (property : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (path : NodeCaptureGuard.DescriptorPath before.data.base.regexp.ambient.objects property ordinaryObjectPrototype descriptor depth) :
    NodeCaptureGuard.DescriptorPath (moduleWorld functionPrototype before).data.base.regexp.ambient.objects property
      before.data.base.regexp.ambient.objects.length descriptor (depth + 1) := by
  have rootPath := NodeCaptureGuard.descriptor_path_append before.data.base.regexp.ambient.objects
    [emptyLiteralObject, arrowObject GetPatternBody.declaration functionPrototype] property ordinaryObjectPrototype descriptor depth path
  have fresh : (moduleWorld functionPrototype before).data.base.regexp.ambient.objects[before.data.base.regexp.ambient.objects.length]? = some emptyLiteralObject := by
    simp [moduleWorld, cacheWithAmbient]
  exact .parent fresh rfl rfl rootPath

theorem module_cell_value (functionPrototype : Nat) (before : Runtime) (name : String) (value : Value)
    (cacheDifferent : name ≠ "patternCache") (exportDifferent : name ≠ "getPattern")
    (inputs : CellValue before before.current name value) :
    CellValue (moduleWorld functionPrototype before) (before.environments.length + 1) name value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  refine ⟨cell, kind, depth + 1 + 1, ?_, ?_, ?_⟩
  · refine .parent (frame := ⟨[("getPattern", before.cells.length + 1)], some before.environments.length⟩)
      (by simp [moduleWorld]) (by simp [exportDifferent]) rfl ?_
    refine .parent (frame := ⟨[("patternCache", before.cells.length)], some before.current⟩)
      (by simp [moduleWorld]) (by simp [cacheDifferent]) rfl ?_
    exact binding_path_append before.environments _ name before.current cell depth path
  · simp only [moduleWorld, List.length_append, List.length_cons, List.length_nil]
    omega
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

end HonoLean.Upstream.GetPatternInvocation
