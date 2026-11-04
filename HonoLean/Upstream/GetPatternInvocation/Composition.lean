import HonoLean.Upstream.GetPatternInvocation.Correctness

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternInvocation
open SourceSubset hiding pinnedSource
open ECMA2025 LexicalArrow

theorem binding_path_frame (before after : Runtime) (frame : CallFrame before after) (name : String)
    (environment cell depth : Nat) (path : BindingPath before.environments name environment cell depth) :
    BindingPath after.environments name environment cell depth := by
  induction path with
  | here found lookup =>
    exact .here ((frame.oldEnvironments _ (List.getElem?_eq_some_iff.mp found).1).trans found) lookup
  | parent found lookup parent path ih =>
    exact .parent ((frame.oldEnvironments _ (List.getElem?_eq_some_iff.mp found).1).trans found) lookup parent ih

theorem cell_value_frame (before after : Runtime) (frame : CallFrame before after)
    (environment : Nat) (name : String) (value : Value) (inputs : CellValue before environment name value) :
    CellValue after environment name value := by
  obtain ⟨cell, kind, depth, path, bound, found⟩ := inputs
  refine ⟨cell, kind, depth, binding_path_frame before after frame name environment cell depth path, ?_,
    (frame.oldCells _ (List.getElem?_eq_some_iff.mp found).1).trans found⟩
  have length := frame.environmentLength
  omega

theorem callable_frame (before after : Runtime) (frame : CallFrame before after) (handle : ArrowHandle) (closure : ArrowClosure)
    (inputs : CallableInputs before handle closure) : CallableInputs after handle closure :=
  ⟨by rw [frame.closures]; exact inputs.found, inputs.program⟩

private theorem realm_from_frame (before after : LabelMatchState) (context : LabelMatchContext) (cache : Nat)
    (realm : LabelRealm before context) (differentString : context.stringPrototype ≠ cache) (differentRegExp : context.regexpPrototype ≠ cache)
    (functions : after.base.regexp.ambient.functions = before.base.regexp.ambient.functions)
    (symbols : after.symbols = before.symbols) (accessors : after.accessors = before.accessors)
    (objects : ∀ reference, reference ≠ cache → reference < before.base.regexp.ambient.objects.length →
      after.base.regexp.ambient.objects[reference]? = before.base.regexp.ambient.objects[reference]?)
    (growth : before.base.regexp.ambient.objects.length ≤ after.base.regexp.ambient.objects.length) : LabelRealm after context := by
  constructor
  case stringFound =>
    obtain ⟨object, found, own⟩ := realm.stringFound
    exact ⟨object, (objects _ differentString (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case regexpFound =>
    obtain ⟨object, found, own⟩ := realm.regexpFound
    exact ⟨object, (objects _ differentRegExp (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case symbolOwners =>
    intro entry member
    rw [symbols] at member
    have bound := realm.symbolOwners entry member
    omega
  case noArgBefore => rw [functions]; exact realm.noArgBefore
  case oldNoArg => rw [functions]; exact realm.oldNoArg
  case symbol => rw [symbols]; exact realm.symbol
  case accessors => rw [accessors]; exact realm.accessors
  all_goals cases realm <;> assumption

theorem terminal_result_realm (before after : Runtime) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) (returned : Value)
    (realm : LabelRealm before.data context.label) (contract : TerminalContract before after context name lower upper next cache object prototype returned)
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    LabelRealm after.data context.label := by
  have growth : before.data.base.regexp.ambient.objects.length ≤ after.data.base.regexp.ambient.objects.length := by
    rw [contract.data.objects, List.length_set, List.length_append]
    simp
  exact realm_from_frame before.data after.data context.label cache realm differentString differentRegExp
    contract.data.frames.functions contract.data.frames.labelSymbols contract.data.frames.accessors contract.data.otherObjects growth

theorem terminal_result_warm_inputs (before after : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : TerminalInputs before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject)
    (contract : TerminalContract before after context name lower upper next cache object constructor.prototype (.array (before.data.base.regexp.ambient.heap.length + 1)))
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    ∃ updated enumerable configurable,
      WarmInputs after context handle closure arguments (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))
        next cache updated (.array (before.data.base.regexp.ambient.heap.length + 1)) true enumerable configurable 1 := by
  obtain ⟨updated, enumerable, configurable, found, own, _, _⟩ := contract.data.cacheOwn
  refine ⟨updated, enumerable, configurable, ⟨⟨callable_frame before after contract.caller handle closure inputs.toHeaderInputs.toCallableInputs,
    inputs.arguments, terminal_result_realm before after context name lower upper next cache object constructor.prototype _ inputs.realm contract differentString differentRegExp,
    inputs.label, cell_value_frame before after contract.caller closure.environment "patternCache" _ inputs.cacheCell,
    found, .own found own, by decide⟩, rfl⟩⟩

theorem invoke_terminal_then_warm_satisfies (extraFirst extraSecond : Nat) (before : Runtime) (context : PatternCacheContext)
    (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : TerminalInputs before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject)
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    ∃ first second,
      invoke (extraFirst + 257) defaultSplitLimit context handle arguments before = .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) first ∧
      invoke (extraSecond + 257) defaultSplitLimit context handle arguments first = .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) second ∧
      TerminalContract before first context name lower upper next cache object constructor.prototype (.array (before.data.base.regexp.ambient.heap.length + 1)) ∧
      WarmContract first second context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))
        cache (.array (before.data.base.regexp.ambient.heap.length + 1)) (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨first, called, contract⟩ := invoke_terminal_satisfies extraFirst before context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject inputs
  obtain ⟨updated, enumerable, configurable, ready⟩ := terminal_result_warm_inputs before first context handle closure arguments name lower upper next cache object descriptor depth constructorHandle constructor prototypeObject inputs contract differentString differentRegExp
  obtain ⟨second, warmed, warm⟩ := invoke_warm_satisfies extraSecond first context handle closure arguments _ name _ next cache updated _ true enumerable configurable 1 ready
  exact ⟨first, second, called, warmed, contract, warm⟩

theorem source_setup_wildcard_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (functionPrototype : Nat) (root functionRoot : OrdinaryObject) (arguments : List Value)
    (inputs : SetupInputs before functionPrototype root functionRoot) (label : argument arguments 0 = GetPatternBody.star) :
    ∃ after,
      sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
      invokeBinding (extra + 5) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments
        (moduleWorld functionPrototype before) = .returned GetPatternBody.star after ∧
      SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ ∧
      WildcardContract (moduleWorld functionPrototype before) after GetPatternBody.star := by
  let closure : ArrowClosure := ⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
    before.data.base.regexp.ambient.objects.length + 1⟩
  have ready : WildcardInputs (moduleWorld functionPrototype before) ⟨before.closures.length⟩ closure arguments :=
    ⟨module_callable functionPrototype before, label⟩
  obtain ⟨called, contract⟩ := invoke_wildcard_satisfies extra defaultSplitLimit context (moduleWorld functionPrototype before)
    ⟨before.closures.length⟩ closure arguments ready
  refine ⟨_, (source_setup_satisfies functionPrototype before root functionRoot inputs).1, ?_,
    module_contract functionPrototype before, contract⟩
  rw [module_export_call _ _ functionPrototype before root functionRoot context arguments inputs]
  exact called

theorem source_setup_miss_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext)
    (functionPrototype : Nat) (root functionRoot : OrdinaryObject) (arguments : List Value) (input : JSString)
    (inputs : SetupInputs before functionPrototype root functionRoot) (realm : LabelRealm before.data context.label)
    (label : argument arguments 0 = .string input) (nonstar : input ≠ [42]) (absent : ¬ ∃ name body, LabelRegExp.Label input name body) :
    ∃ after,
      sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
      invokeBinding (extra + 257) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments
        (moduleWorld functionPrototype before) = .returned .null after ∧
      SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ ∧
      MissContract (moduleWorld functionPrototype before) after context input .null := by
  let closure : ArrowClosure := ⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
    before.data.base.regexp.ambient.objects.length + 1⟩
  have ready : MissInputs (moduleWorld functionPrototype before) context ⟨before.closures.length⟩ closure arguments input :=
    ⟨module_callable functionPrototype before, label, module_realm functionPrototype before context.label realm, nonstar, absent⟩
  obtain ⟨after, called, contract⟩ := invoke_miss_satisfies extra (moduleWorld functionPrototype before) context ⟨before.closures.length⟩ closure arguments input ready
  refine ⟨after, (source_setup_satisfies functionPrototype before root functionRoot inputs).1, ?_,
    module_contract functionPrototype before, contract⟩
  rw [module_export_call _ _ functionPrototype before root functionRoot context arguments inputs]
  exact called

theorem module_plain_inputs (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (input name : JSString) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : InitialPlainInputs before context functionPrototype arguments input name next root functionRoot descriptor depth) :
    PlainInputs (moduleWorld functionPrototype before) context ⟨before.closures.length⟩
      ⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
        before.data.base.regexp.ambient.objects.length + 1⟩ arguments input name next
      before.data.base.regexp.ambient.objects.length emptyLiteralObject descriptor (depth + 1) := by
  refine ⟨⟨module_callable functionPrototype before, inputs.arguments,
    module_realm functionPrototype before context.label inputs.realm, inputs.label,
    (module_contract functionPrototype before).cacheCell, ?_,
    module_cache_path functionPrototype before _ descriptor depth inputs.rootPath, inputs.pathBound⟩,
    inputs.falsy, ⟨inputs.dataWritable, Or.inl ⟨rfl, rfl⟩⟩⟩
  simp [moduleWorld, cacheWithAmbient]

theorem module_terminal_inputs (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitialTerminalInputs before context functionPrototype arguments name lower upper next root functionRoot
      descriptor depth constructorHandle constructor prototypeObject) :
    TerminalInputs (moduleWorld functionPrototype before) context ⟨before.closures.length⟩
      ⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
        before.data.base.regexp.ambient.objects.length + 1⟩ arguments name lower upper next
      before.data.base.regexp.ambient.objects.length emptyLiteralObject descriptor (depth + 1)
      constructorHandle constructor prototypeObject := by
  refine ⟨⟨module_callable functionPrototype before, inputs.arguments,
    module_realm functionPrototype before context.label inputs.realm,
    LabelMatch.safe_range_label name lower upper inputs.validName inputs.lowerSafe inputs.upperSafe,
    (module_contract functionPrototype before).cacheCell, ?_,
    module_cache_path functionPrototype before _ descriptor depth inputs.rootPath, inputs.pathBound⟩,
    inputs.terminal, inputs.validName, inputs.lowerSafe, inputs.upperSafe, inputs.ordered,
    inputs.falsy, ⟨inputs.dataWritable, Or.inl ⟨rfl, rfl⟩⟩,
    module_cell_value functionPrototype before "RegExp" _ (by decide) (by decide) inputs.constructorCell,
    inputs.handleBound, inputs.identity, ?_⟩
  · simp [moduleWorld, cacheWithAmbient]
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp inputs.prototypeFound).1).trans inputs.prototypeFound

theorem source_setup_plain_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (input name : JSString) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : InitialPlainInputs before context functionPrototype arguments input name next root functionRoot descriptor depth) :
    ∃ after,
      sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
      invokeBinding (extra + 257) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments
        (moduleWorld functionPrototype before) = .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) after ∧
      SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ ∧
      PlainContract (moduleWorld functionPrototype before) after context input name next
        before.data.base.regexp.ambient.objects.length emptyLiteralObject (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨after, called, contract⟩ := invoke_plain_satisfies extra (moduleWorld functionPrototype before) context
    ⟨before.closures.length⟩ _ arguments input name next _ emptyLiteralObject descriptor (depth + 1)
    (module_plain_inputs before context functionPrototype arguments input name next root functionRoot descriptor depth inputs)
  refine ⟨after, (source_setup_satisfies functionPrototype before root functionRoot inputs.setup).1, ?_,
    module_contract functionPrototype before, contract⟩
  rw [module_export_call _ _ functionPrototype before root functionRoot context arguments inputs.setup]
  exact called

theorem source_setup_terminal_satisfies (extra : Nat) (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitialTerminalInputs before context functionPrototype arguments name lower upper next root functionRoot
      descriptor depth constructorHandle constructor prototypeObject) :
    ∃ after,
      sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
      invokeBinding (extra + 257) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments
        (moduleWorld functionPrototype before) = .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) after ∧
      SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ ∧
      TerminalContract (moduleWorld functionPrototype before) after context name lower upper next
        before.data.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype
        (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨after, called, contract⟩ := invoke_terminal_satisfies extra (moduleWorld functionPrototype before) context
    ⟨before.closures.length⟩ _ arguments name lower upper next _ emptyLiteralObject descriptor (depth + 1)
    constructorHandle constructor prototypeObject
    (module_terminal_inputs before context functionPrototype arguments name lower upper next root functionRoot descriptor depth constructorHandle constructor prototypeObject inputs)
  refine ⟨after, (source_setup_satisfies functionPrototype before root functionRoot inputs.setup).1, ?_,
    module_contract functionPrototype before, contract⟩
  rw [module_export_call _ _ functionPrototype before root functionRoot context arguments inputs.setup]
  exact called

theorem module_export_call_frame (fuel limit functionPrototype : Nat) (before after : Runtime)
    (root functionRoot : OrdinaryObject) (context : PatternCacheContext) (arguments : List Value)
    (inputs : SetupInputs before functionPrototype root functionRoot) (frame : CallFrame (moduleWorld functionPrototype before) after) :
    invokeBinding fuel limit context (before.environments.length + 1) "getPattern" arguments after =
      invoke fuel limit context ⟨before.closures.length⟩ arguments after := by
  have exportCell := cell_value_frame (moduleWorld functionPrototype before) after frame _ "getPattern" _
    (module_contract functionPrototype before).exportCell
  have binding := cell_value_reads _ _ _ _ exportCell
  change getBindingValue (after.environments.length + 1) after (before.environments.length + 1) "getPattern" =
    .ok (.object (before.data.base.regexp.ambient.objects.length + 1)) at binding
  have callable : resolveArrowValue after (.object (before.data.base.regexp.ambient.objects.length + 1)) = .ok ⟨before.closures.length⟩ := by
    simpa only [resolveArrowValue, frame.closures] using module_value_callable functionPrototype before root functionRoot inputs
  simp [invokeBinding, binding, invokeValue, callable]

/-- One actual setup, then two value-resolved calls to the SAME export, with
the complete first returned runtime supplied to the second call. No cache,
lexical environment, constructor readiness or realm is reset between calls. -/
theorem source_setup_terminal_warm_satisfies (extraFirst extraSecond : Nat) (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitialTerminalInputs before context functionPrototype arguments name lower upper next root functionRoot
      descriptor depth constructorHandle constructor prototypeObject) :
    ∃ first second,
      sourceSetup functionPrototype before = some (.ok (⟨before.closures.length⟩, moduleWorld functionPrototype before)) ∧
      invokeBinding (extraFirst + 257) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments
        (moduleWorld functionPrototype before) = .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) first ∧
      invokeBinding (extraSecond + 257) defaultSplitLimit context (before.environments.length + 1) "getPattern" arguments first =
        .returned (.array (before.data.base.regexp.ambient.heap.length + 1)) second ∧
      SetupContract before (moduleWorld functionPrototype before) functionPrototype ⟨before.closures.length⟩ ∧
      TerminalContract (moduleWorld functionPrototype before) first context name lower upper next before.data.base.regexp.ambient.objects.length
        emptyLiteralObject constructor.prototype (.array (before.data.base.regexp.ambient.heap.length + 1)) ∧
      WarmContract first second context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))
        before.data.base.regexp.ambient.objects.length (.array (before.data.base.regexp.ambient.heap.length + 1)) (.array (before.data.base.regexp.ambient.heap.length + 1)) := by
  have differentString : context.label.stringPrototype ≠ before.data.base.regexp.ambient.objects.length := by
    obtain ⟨object, found, _⟩ := inputs.realm.stringFound
    have bound := (List.getElem?_eq_some_iff.mp found).1
    omega
  have differentRegExp : context.label.regexpPrototype ≠ before.data.base.regexp.ambient.objects.length := by
    obtain ⟨object, found, _⟩ := inputs.realm.regexpFound
    have bound := (List.getElem?_eq_some_iff.mp found).1
    omega
  obtain ⟨first, second, called, warmed, contract, warm⟩ := invoke_terminal_then_warm_satisfies extraFirst extraSecond
    (moduleWorld functionPrototype before) context ⟨before.closures.length⟩ _ arguments name lower upper next _ emptyLiteralObject descriptor
    (depth + 1) constructorHandle constructor prototypeObject
    (module_terminal_inputs before context functionPrototype arguments name lower upper next root functionRoot descriptor depth constructorHandle constructor prototypeObject inputs)
    differentString differentRegExp
  refine ⟨first, second, (source_setup_satisfies functionPrototype before root functionRoot inputs.setup).1, ?_, ?_,
    module_contract functionPrototype before, contract, warm⟩
  · rw [module_export_call _ _ functionPrototype before root functionRoot context arguments inputs.setup]
    exact called
  · rw [module_export_call_frame _ _ functionPrototype before first root functionRoot context arguments inputs.setup contract.caller]
    exact warmed

end HonoLean.Upstream.GetPatternInvocation
