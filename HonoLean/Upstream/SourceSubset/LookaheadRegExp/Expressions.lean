import HonoLean.Upstream.GetPatternLookahead.Correctness
import HonoLean.Upstream.PatternConstruct.Correctness

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.SourceSubset.LookaheadRegExp
open ECMA2025
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

def tupleStage (before : State) (contents : List Value) : State :=
  withBase before (cacheArrayCellState before.base contents)

/-- Independent local endpoint. The real lookahead branch puts the computed
cache KEY in slot0, not the label used by the terminal branch. -/
def tupleState (before : State) (key name : JSString) (prototype : Nat)
    (lower upper : UInt16) (next : JSString) : State :=
  constructedState (tupleStage before [.string key, .string name,
    .object before.base.base.regexp.ambient.objects.length]) prototype (compiledRecord lower upper next)

theorem coherent_tupleStage (before : State) (contents : List Value) (coherent : Coherent before) :
    Coherent (tupleStage before contents) := ⟨coherent.allocated, coherent.unique⟩

theorem operand_inputs_stage (before : State) (context : RegExpConstructContext) (input name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor)
    (prototypeObject : OrdinaryObject) (contents : List Value)
    (inputs : PatternConstruct.Inputs before.base.base.regexp context input name matched handle values lower upper constructor prototypeObject) :
    PatternConstruct.Inputs (tupleStage before contents).base.base.regexp context input name matched handle values lower upper constructor prototypeObject :=
  PatternConstruct.inputs_tupleStage before.base.base.regexp context input name matched handle values lower upper constructor prototypeObject contents inputs

theorem eval_variable (extra limit : Nat) (context : PatternCacheContext) (before : State)
    (name : String) (value : Value) (binding : before.base.base.regexp.ambient.environment.lookup name = some value) :
    evalExpr (extra + 2) limit context (.ordinary (.variable name)) before = .ok (value, before) := by
  simp [evalExpr, evalExpression, lookupVariable, binding, withAmbient, withBase, cacheWithAmbient]

theorem eval_name (extra : Nat) (before : State) (context : PatternCacheContext) (matched : Nat)
    (values : List Value) (name : JSString)
    (binding : before.base.base.regexp.ambient.environment.lookup "match" = some (.array matched))
    (found : before.base.base.regexp.ambient.heap[matched]? = some values) (atIndex : values[1]? = some (.string name)) :
    evalExpr (extra + 4) defaultSplitLimit context PatternCache.nameExpr before = .ok (.string name, before) := by
  simp [evalExpr, PatternCache.nameExpr, PatternCache.matchExpr, evalExpression, lookupVariable, binding,
    cacheReadProperty, found, atIndex, withAmbient, withBase, cacheWithAmbient]

/-- Local operand facts are supplied only by the proved earlier label producer
in source composition; no source-level theorem accepts staged captures. -/
theorem eval_positive_template (extra : Nat) (before : State) (context : PatternCacheContext) (input name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor)
    (prototypeObject : OrdinaryObject) (next : JSString)
    (inputs : PatternConstruct.Inputs before.base.base.regexp context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject)
    (nextBinding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next)) :
    evalExpr (extra + 8) defaultSplitLimit context PatternCache.lookaheadTemplate before =
      .ok (.string (LiteralLookahead.rawSource lower upper next), before) := by
  have body := PatternConstruct.eval_index (extra + 2) before.base.base.regexp matched 2 values
    (.string (PatternConstruct.rawBody lower upper)) inputs.matchBinding inputs.matchedFound inputs.bodyFound
  change evalExpression (extra + 6) defaultSplitLimit (.index (.variable "match") (.number 2))
    before.base.base.regexp.ambient = .ok (.string (PatternConstruct.rawBody lower upper), before.base.base.regexp.ambient) at body
  have substituted : evalPatternCacheExpr (extra + 8) defaultSplitLimit context PatternCache.lookaheadTemplate before.base =
      .ok (.string (LiteralLookahead.rawSource lower upper next), before.base) := by
    rw [PatternCache.lookaheadTemplate, evalPatternCacheExpr, evalPatternCacheTemplate, body]
    simp [evalPatternCacheTemplate, evalExpression, lookupVariable, nextBinding,
      cachePrimitiveToString, cacheWithAmbient, LiteralLookahead.rawSource, PatternConstruct.rawBody] <;> rfl
  rw [show PatternCache.lookaheadTemplate = .template [94]
    [(.index (.variable "match") (.number 2), [40,63,61,47]), (.variable "next", [41])] from rfl]
  rw [template_refines (extra + 7)]
  change ((evalPatternCacheExpr (extra + 8) defaultSplitLimit context PatternCache.lookaheadTemplate before.base).mapError Error.pattern).map
    (fun (value, base) => (value, withBase before base)) = _
  rw [substituted]
  rfl

theorem eval_positive_constructor (extra : Nat) (before : State) (context : PatternCacheContext) (input name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor)
    (prototypeObject : OrdinaryObject) (next : JSString)
    (inputs : PatternConstruct.Inputs before.base.base.regexp context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject)
    (coherent : Coherent before)
    (nextBinding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next))
    (safeNext : LiteralLookahead.SafeNext next) :
    evalExpr (extra + 9) defaultSplitLimit context (.construct (.variable "RegExp") PatternCache.lookaheadTemplate) before =
      .ok (.object before.base.base.regexp.ambient.objects.length,
        constructedState before constructor.prototype (compiledRecord lower upper next)) := by
  have callee : evalExpression (extra + 8) defaultSplitLimit (.variable "RegExp") before.base.base.regexp.ambient =
      .ok (.function handle, before.base.base.regexp.ambient) := by
    simp [evalExpression, lookupVariable, inputs.constructorBinding]
  have template := eval_positive_template extra before context input name matched handle values lower upper constructor prototypeObject next inputs nextBinding
  have argument : evalExpr (extra + 8) defaultSplitLimit context PatternCache.lookaheadTemplate
      (withAmbient before before.base.base.regexp.ambient) =
      .ok (.string (LiteralLookahead.rawSource lower upper next), before) := template
  have saved := construct_saved (extra + 8) defaultSplitLimit context (.variable "RegExp") PatternCache.lookaheadTemplate
    before (.function handle) before.base.base.regexp.ambient (.string (LiteralLookahead.rawSource lower upper next)) before callee argument
  have constructorInputs : GetPatternLookahead.ConstructorInputs before context.label.iterators.constructors handle constructor prototypeObject lower upper next :=
    ⟨coherent, inputs.noArgBefore, inputs.methodsBefore, inputs.functionsBefore, inputs.membersBefore, inputs.builtinsBefore,
      inputs.handleBound, inputs.identity, inputs.prototypeFound, inputs.lowerSafe, inputs.upperSafe, inputs.ordered, safeNext⟩
  exact saved.trans (GetPatternLookahead.constructor_satisfies before context.label.iterators.constructors handle constructor prototypeObject lower upper next constructorInputs).1

def appendElement (reference : Nat) (value : Value) (before : State) : Except Error State :=
  ((cacheAppendElement reference value before.base).mapError Error.pattern).map (withBase before)

theorem append_tupleStage (before : State) (contents : List Value) (value : Value) :
    appendElement before.base.base.regexp.ambient.heap.length value (tupleStage before contents) =
      .ok (tupleStage before (contents ++ [value])) := by
  simp [appendElement, tupleStage, cacheAppendElement_fresh, withBase]

private theorem map_as_bind {ε α β : Type} (operation : Except ε α) (mapValue : α → β) :
    operation.map mapValue = operation >>= (fun value => pure (mapValue value)) := by
  cases operation <;> rfl

theorem eval_array3 (fuel limit : Nat) (context : PatternCacheContext)
    (first second third : PatternCacheExpr) (before : State) :
    evalExpr (fuel + 5) limit context (.arrayLiteral [first, second, third]) before =
      (do
        let (firstValue, after) ← evalExpr (fuel + 3) limit context first (tupleStage before [])
        let after ← appendElement before.base.base.regexp.ambient.heap.length firstValue after
        let (secondValue, after) ← evalExpr (fuel + 2) limit context second after
        let after ← appendElement before.base.base.regexp.ambient.heap.length secondValue after
        let (thirdValue, after) ← evalExpr (fuel + 1) limit context third after
        let after ← appendElement before.base.base.regexp.ambient.heap.length thirdValue after
        pure (.array before.base.base.regexp.ambient.heap.length, after)) := by
  rw [evalExpr]
  simp only [evalElements, appendElement, map_as_bind, bind_assoc, pure_bind]
  rfl

theorem append_constructed_stage (before : State) (prototype : Nat) (record : Record)
    (contents : List Value) (value : Value) :
    appendElement before.base.base.regexp.ambient.heap.length value (constructedState (tupleStage before contents) prototype record) =
      .ok (constructedState (tupleStage before (contents ++ [value])) prototype record) := by
  have appended := append_tupleStage (constructedState before prototype record) contents value
  simpa only [constructedState, tupleStage, withBase, withAmbient, cacheArrayCellState, cacheWithAmbient] using appended

theorem eval_positive_tuple (extra : Nat) (before : State) (context : PatternCacheContext) (input name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor)
    (prototypeObject : OrdinaryObject) (next key : JSString)
    (inputs : PatternConstruct.Inputs before.base.base.regexp context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject)
    (coherent : Coherent before)
    (nextBinding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next))
    (safeNext : LiteralLookahead.SafeNext next)
    (keyBinding : before.base.base.regexp.ambient.environment.lookup "cacheKey" = some (.string key)) :
    evalExpr (extra + 13) defaultSplitLimit context PatternCache.lookaheadTuple before =
      .ok (.array before.base.base.regexp.ambient.heap.length, tupleState before key name constructor.prototype lower upper next) := by
  have stage1 := operand_inputs_stage before context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject [.string key] inputs
  have stage2 := operand_inputs_stage before context.label.iterators.constructors input name matched handle values lower upper constructor prototypeObject [.string key, .string name] inputs
  have first := eval_variable (extra + 9) defaultSplitLimit context (tupleStage before []) "cacheKey" (.string key) keyBinding
  have second := eval_name (extra + 6) (tupleStage before [.string key]) context matched values name
    stage1.matchBinding stage1.matchedFound stage1.nameFound
  have third := eval_positive_constructor extra (tupleStage before [.string key, .string name]) context input name matched handle values lower upper constructor prototypeObject next stage2
    (coherent_tupleStage before _ coherent) nextBinding safeNext
  rw [PatternCache.lookaheadTuple, eval_array3 (extra + 8)]
  change (do
    let (firstValue, after) ← evalExpr (extra + 11) defaultSplitLimit context PatternCache.keyExpr (tupleStage before [])
    let after ← appendElement before.base.base.regexp.ambient.heap.length firstValue after
    let (secondValue, after) ← evalExpr (extra + 10) defaultSplitLimit context PatternCache.nameExpr after
    let after ← appendElement before.base.base.regexp.ambient.heap.length secondValue after
    let (thirdValue, after) ← evalExpr (extra + 9) defaultSplitLimit context (.construct (.variable "RegExp") PatternCache.lookaheadTemplate) after
    let after ← appendElement before.base.base.regexp.ambient.heap.length thirdValue after
    pure (Value.array before.base.base.regexp.ambient.heap.length, after)) = _
  change evalExpr (extra + 11) defaultSplitLimit context PatternCache.keyExpr (tupleStage before []) = _ at first
  rw [first]
  dsimp only [bind, Except.bind]
  rw [append_tupleStage]
  dsimp only [bind, Except.bind]
  simp only [List.nil_append]
  rw [second]
  dsimp only [bind, Except.bind]
  rw [append_tupleStage]
  dsimp only [bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [third]
  dsimp only [bind, Except.bind]
  rw [show (tupleStage before [.string key, .string name]).base.base.regexp.ambient.objects.length =
    before.base.base.regexp.ambient.objects.length from rfl]
  rw [append_constructed_stage]
  rfl

end HonoLean.Upstream.SourceSubset.LookaheadRegExp
