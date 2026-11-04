import HonoLean.Upstream.PatternCacheTerminal.Contract

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.PatternCacheTerminal
open SourceSubset ECMA2025 PatternCache

theorem eval_next_condition (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (next : Option JSString)
    (binding : before.base.regexp.ambient.environment.lookup "next" = some (nextValue next)) (terminal : TerminalNext next) :
    ∃ value, evalPatternCacheExpr (extra + 10) defaultSplitLimit context nextCondition before = .ok (value, before) ∧ truthy value = false := by
  rcases terminal with rfl | rfl | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩
  · exact ⟨.undefined, by simp [nextCondition, nextExpr, evalPatternCacheExpr, evalExpression, lookupVariable, binding, nextValue,
      cacheWithAmbient, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure, truthy], rfl⟩
  · exact ⟨.string [], by simp [nextCondition, nextExpr, evalPatternCacheExpr, evalExpression, lookupVariable, binding, nextValue,
      cacheWithAmbient, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure, truthy], rfl⟩
  · exact ⟨.boolean false, by simp [nextCondition, nextExpr, evalPatternCacheExpr, evalExpression, lookupVariable, binding, nextValue,
      cacheWithAmbient, cacheReadProperty, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure, truthy], rfl⟩
  · exact ⟨.boolean false, by simp [nextCondition, nextExpr, evalPatternCacheExpr, evalExpression, lookupVariable, binding, nextValue,
      cacheWithAmbient, cacheReadProperty, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure, truthy], rfl⟩

theorem eval_terminal_template (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (matched : Nat) (values : List Value) (lower upper : UInt16)
    (binding : before.base.regexp.ambient.environment.lookup "match" = some (.array matched))
    (found : before.base.regexp.ambient.heap[matched]? = some values)
    (body : values[2]? = some (.string (PatternConstruct.rawBody lower upper))) :
    evalPatternCacheExpr (extra + 7) defaultSplitLimit context terminalTemplate before =
      .ok (.string (PatternConstruct.assembledSource lower upper), before) := by
  have read := PatternConstruct.eval_index (extra + 1) before.base.regexp matched 2 values (.string (PatternConstruct.rawBody lower upper)) binding found body
  change evalExpression (extra + 5) defaultSplitLimit (.index (.variable "match") (.number 2)) before.base.regexp.ambient = _ at read
  change evalPatternCacheExpr ((extra + 5) + 2) defaultSplitLimit context terminalTemplate before = _
  simp only [terminalTemplate, evalPatternCacheExpr, evalPatternCacheTemplate]
  rw [read]
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure, cachePrimitiveToString, cacheWithAmbient]
  rfl

theorem eval_terminal_constructor (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (input name : JSString) (matched handle : Nat) (values : List Value) (lower upper : UInt16)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : PatternConstruct.Inputs before.base.regexp context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject) :
    evalPatternCacheExpr (extra + 8) defaultSplitLimit context (.construct (.variable "RegExp") terminalTemplate) before =
      .ok (.object before.base.regexp.ambient.objects.length, rangeState before constructor.prototype lower upper) := by
  have callee : evalExpression (extra + 7) defaultSplitLimit (.variable "RegExp") before.base.regexp.ambient = .ok (.function handle, before.base.regexp.ambient) := by
    simp [evalExpression, lookupVariable, inputs.constructorBinding]
    rfl
  have template := eval_terminal_template extra before context matched values lower upper inputs.matchBinding inputs.matchedFound inputs.bodyFound
  have identity : constructorAt context.label.iterators.constructors.constructors (.function handle) = some constructor := by
    simp [constructorAt, inputs.handleBound, inputs.identity]
  have invoked := invokeRegExpConstructor_range context.label.iterators.constructors (.function handle) before.base.regexp constructor prototypeObject lower upper
    (PatternConstruct.tables_separated _ _ _ _ _ _ _ _ _ _ _ inputs) identity inputs.prototypeFound inputs.lowerSafe inputs.upperSafe inputs.ordered
  change invokeRegExpConstructor context.label.iterators.constructors (.function handle) (.string (PatternConstruct.assembledSource lower upper)) before.base.regexp = _ at invoked
  rw [evalPatternCacheExpr, callee]
  dsimp only [Except.mapError, Except.map, bind, Except.bind]
  change (do
    let (argument, after) ← evalPatternCacheExpr (extra + 7) defaultSplitLimit context terminalTemplate before
    let (value, constructed) ← (invokeRegExpConstructor context.label.iterators.constructors (.function handle) argument after.base.regexp).mapError PatternCacheError.constructor
    pure (value, {after with base := {after.base with regexp := constructed}})) = _
  rw [template]
  dsimp only [bind, Except.bind]
  rw [invoked]
  rfl

theorem inputs_array_stage (before : LabelMatchState) (context : RegExpConstructContext) (input name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (contents : List Value) (inputs : PatternConstruct.Inputs before.base.regexp context input name matched handle values lower upper constructor prototypeObject) :
    PatternConstruct.Inputs (cacheArrayCellState before contents).base.regexp context input name matched handle values lower upper constructor prototypeObject :=
  PatternConstruct.inputs_tupleStage _ _ _ _ _ _ _ _ _ _ _ contents inputs

theorem eval_terminal_tuple (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (input name : JSString) (matched handle : Nat) (values : List Value) (lower upper : UInt16)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : PatternConstruct.Inputs before.base.regexp context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject) :
    evalPatternCacheExpr (extra + 12) defaultSplitLimit context terminalTuple before =
      .ok (.array before.base.regexp.ambient.heap.length, tupleState before constructor.prototype lower upper input name) := by
  have label := evalPatternCache_variable (extra + 8) defaultSplitLimit context (cacheArrayCellState before []) "label" (.string input) inputs.labelBinding
  have stage1 := inputs_array_stage before _ input name matched handle values lower upper constructor prototypeObject [.string input] inputs
  have nameRead := eval_match_index (extra + 6) (cacheArrayCellState before [.string input]) context matched 1 values stage1.matchBinding stage1.matchedFound
  rw [inputs.nameFound] at nameRead
  dsimp only [Option.getD] at nameRead
  have stage2 := inputs_array_stage before _ input name matched handle values lower upper constructor prototypeObject [.string input, .string name] inputs
  have created := eval_terminal_constructor extra (cacheArrayCellState before [.string input, .string name]) context input name matched handle values lower upper constructor prototypeObject stage2
  change evalPatternCacheExpr ((extra + 7) + 5) defaultSplitLimit context (.arrayLiteral [labelExpr, nameExpr, .construct (.variable "RegExp") terminalTemplate]) before = _
  rw [evalPatternCache_array3]
  change evalPatternCacheExpr (extra + 10) defaultSplitLimit context labelExpr (cacheEmptyArray before) = _ at label
  rw [label]
  dsimp only [bind, Except.bind]
  rw [cacheAppendElement_fresh]
  dsimp only [bind, Except.bind, List.nil_append]
  change evalPatternCacheExpr (extra + 9) defaultSplitLimit context nameExpr (cacheArrayCellState before [.string input]) = _ at nameRead
  rw [nameRead]
  dsimp only [bind, Except.bind]
  rw [cacheAppendElement_fresh]
  dsimp only [bind, Except.bind, List.cons_append, List.nil_append]
  rw [created]
  dsimp only [bind, Except.bind]
  have appended := cacheAppendElement_fresh (rangeState before constructor.prototype lower upper) [.string input, .string name] (.object before.base.regexp.ambient.objects.length)
  change cacheAppendElement before.base.regexp.ambient.heap.length (.object before.base.regexp.ambient.objects.length)
    (rangeState (cacheArrayCellState before [.string input, .string name]) constructor.prototype lower upper) = _ at appended
  change (do
    let after ← cacheAppendElement before.base.regexp.ambient.heap.length (.object before.base.regexp.ambient.objects.length)
      (rangeState (cacheArrayCellState before [.string input, .string name]) constructor.prototype lower upper)
    pure (Value.array before.base.regexp.ambient.heap.length, after)) = _
  rw [appended]
  rfl

end HonoLean.Upstream.PatternCacheTerminal
