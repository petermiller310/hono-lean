import HonoLean.Upstream.SourceSubset.PatternCache

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Primitive key formula, independent of cache lookup/write or tuple output. -/
def PatternCacheKeyContract (label : JSString) (next : Value) (key : JSString) : Prop :=
  ∃ suffix, cachePrimitiveToString next = .ok suffix ∧ key = label ++ [35] ++ suffix

theorem patternCacheKey_iff (label : JSString) (next : Value) (key : JSString) :
    patternCacheKey label next = .ok key ↔ PatternCacheKeyContract label next key := by
  unfold patternCacheKey PatternCacheKeyContract
  cases converted : cachePrimitiveToString next <;> simp [Except.map, eq_comm]

theorem undefined_string_key_collision (label : JSString) :
    patternCacheKey label .undefined = patternCacheKey label (.string (cacheAscii "undefined")) := rfl

theorem raw_separator_key_collision (left right suffix : JSString) :
    patternCacheKey (left ++ [35] ++ right) (.string suffix) =
      patternCacheKey left (.string (right ++ [35] ++ suffix)) := by
  simp [patternCacheKey, cachePrimitiveToString, Except.map, List.append_assoc]

theorem evalPatternCache_key (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState)
    (label : JSString) (next : Value)
    (labelFound : before.base.regexp.ambient.environment.lookup "label" = some (.string label))
    (nextFound : before.base.regexp.ambient.environment.lookup "next" = some next) :
    evalPatternCacheExpr (extra + 4) limit context (.template [] [(.variable "label", [35]), (.variable "next", [])]) before =
      (patternCacheKey label next).map (fun key => (.string key, before)) := by
  have labelConverted : cachePrimitiveToString (.string label) = .ok label := rfl
  simp only [evalPatternCacheExpr, evalPatternCacheTemplate, evalExpression, lookupVariable,
    labelFound, nextFound, cacheWithAmbient, patternCacheKey, labelConverted,
    Except.mapError, bind, Except.bind, pure, Except.pure, Except.map]
  cases cachePrimitiveToString next <;> simp

/-- Exact delegation of actual const initializer source60 to the existing
current-method/literal/@@match/flags/exec machine. No match oracle is added. -/
theorem evalPatternCache_labelMatch (fuel limit : Nat) (context : PatternCacheContext)
    (receiver : Expr) (method : String) (literal : LabelRegExpLiteral) (before : LabelMatchState) :
    evalPatternCacheExpr (fuel + 1) limit context (.labelMatch receiver method literal) before =
      (runLabelMatch fuel limit context.label ⟨"", receiver, method, literal⟩ before).mapError .label := rfl

theorem evalPatternCache_ordinary (fuel limit : Nat) (context : PatternCacheContext) (expression : Expr) (before : LabelMatchState) :
    evalPatternCacheExpr (fuel + 1) limit context (.ordinary expression) before =
      ((evalExpression fuel limit expression before.base.regexp.ambient).mapError PatternCacheError.evaluation).map
        (fun (value, after) => (value, cacheWithAmbient before after)) := rfl

theorem cache_string_index (value : JSString) (index : Nat) (before : State) :
    cacheReadProperty (.string value) (.number index) before =
      .ok ((value[index]?).map (fun unit => Value.string [unit]) |>.getD .undefined) := rfl

theorem evalPatternCache_index (fuel limit : Nat) (context : PatternCacheContext) (base key : PatternCacheExpr)
    (before baseState keyState : LabelMatchState) (baseValue keyValue : Value)
    (baseEval : evalPatternCacheExpr fuel limit context base before = .ok (baseValue, baseState))
    (keyEval : evalPatternCacheExpr fuel limit context key baseState = .ok (keyValue, keyState)) :
    evalPatternCacheExpr (fuel + 1) limit context (.index base key) before =
      ((cacheReadProperty baseValue keyValue keyState.base.regexp.ambient).mapError PatternCacheError.evaluation).map
        (fun value => (value, keyState)) := by
  simp [evalPatternCacheExpr, baseEval, keyEval, bind, Except.bind, pure, Except.pure, Except.map]

theorem evalPatternCache_conditional (fuel limit : Nat) (context : PatternCacheContext)
    (condition yes no : PatternCacheExpr) (before after : LabelMatchState) (value : Value)
    (evaluated : evalPatternCacheExpr fuel limit context condition before = .ok (value, after)) :
    evalPatternCacheExpr (fuel + 1) limit context (.conditional condition yes no) before =
      evalPatternCacheExpr fuel limit context (if truthy value then yes else no) after := by
  simp [evalPatternCacheExpr, evaluated, bind, Except.bind]

/-- Captured reference and post-RHS Set are explicit. These hypotheses are
individual operand evaluations, not a desired cache tuple/write/read outcome. -/
theorem executePatternCacheAssignment_reference (fuel limit : Nat) (context : PatternCacheContext)
    (base key value : PatternCacheExpr) (before baseState keyState rhsState : LabelMatchState)
    (reference : Nat) (property : JSString) (returned : Value)
    (baseEval : evalPatternCacheExpr fuel limit context base before = .ok (.object reference, baseState))
    (keyEval : evalPatternCacheExpr fuel limit context key baseState = .ok (.string property, keyState))
    (rhsEval : evalPatternCacheExpr fuel limit context value keyState = .ok (returned, rhsState)) :
    executePatternCacheAssignment fuel limit context (.index base key) value before =
      ((setProperty propertyFuel rhsState.base.regexp.ambient.objects reference property returned).mapError
        (PatternCacheError.evaluation ∘ EvalError.objectError)).map
        (fun objects => cacheWithAmbient rhsState {rhsState.base.regexp.ambient with objects}) := by
  simp [executePatternCacheAssignment, baseEval, keyEval, rhsEval, bind, Except.bind, pure, Except.pure, Except.map]

def initializedPatternCacheState (declaration : PatternCacheInit) (before : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with
    objects := before.base.regexp.ambient.objects ++ [emptyLiteralObject]
    environment := (declaration.name, .object before.base.regexp.ambient.objects.length) :: before.base.regexp.ambient.environment}

theorem initializePatternCache_empty (extra limit : Nat) (context : PatternCacheContext) (declaration : PatternCacheInit)
    (before : LabelMatchState) (root : OrdinaryObject) (empty : declaration.initializer = .emptyObject)
    (rootFound : before.base.regexp.ambient.objects[ordinaryObjectPrototype]? = some root) :
    initializePatternCache (extra + 2) limit context declaration before = .ok (initializedPatternCacheState declaration before) := by
  simp [initializePatternCache, empty, evalPatternCacheExpr, createLiteralObject, rootFound,
    initializedPatternCacheState, cacheWithAmbient, Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]

/-- Restoring selected call locals preserves the exact persistent ordinary
cache object, arrays, brands/metadata and all other ambient components. -/
theorem runPatternCache_restores_caller (fuel limit : Nat) (context : PatternCacheContext)
    (program : List PatternCacheStmt) (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (executed : executePatternCache fuel limit context program before = .ok (.returned value after)) :
    runPatternCache fuel limit context program before =
      .ok (value, cacheWithAmbient after {after.base.regexp.ambient with environment := before.base.regexp.ambient.environment}) := by
  simp [runPatternCache, executed, cacheRestoreEnvironment, bind, Except.bind, pure, Except.pure]

/-- Full declaration-prefix bridge to the existing actual label producer,
without a successful-output hypothesis or re-proving its flags/exec protocol. -/
theorem executePatternCache_declare_label (fuel limit : Nat) (context : PatternCacheContext)
    (name method : String) (receiver : Expr) (literal : LabelRegExpLiteral)
    (tail : List PatternCacheStmt) (before : LabelMatchState) :
    executePatternCache (fuel + 2) limit context (.declare name (.labelMatch receiver method literal) :: tail) before =
      (do
        let after ← (executeLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before).mapError PatternCacheError.label
        executePatternCache (fuel + 1) limit context tail after) := by
  have same : runLabelMatch fuel limit context.label ⟨"", receiver, method, literal⟩ before =
      runLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before := rfl
  simp only [executePatternCache, evalPatternCacheExpr, executeLabelMatch]
  rw [same]
  cases runLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before <;> rfl

def cacheArrayCellState (before : LabelMatchState) (values : List Value) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with heap := before.base.regexp.ambient.heap ++ [values]}

theorem cacheAppendElement_fresh (before : LabelMatchState) (values : List Value) (value : Value) :
    cacheAppendElement before.base.regexp.ambient.heap.length value (cacheArrayCellState before values) =
      .ok (cacheArrayCellState before (values ++ [value])) := by
  simp [cacheAppendElement, cacheArrayCellState, cacheWithAmbient, appendLiteralElements, Except.mapError, Except.map]

theorem evalPatternCache_variable (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState)
    (name : String) (value : Value) (found : before.base.regexp.ambient.environment.lookup name = some value) :
    evalPatternCacheExpr (extra + 2) limit context (.ordinary (.variable name)) before = .ok (value, before) := by
  simp [evalPatternCacheExpr, evalExpression, lookupVariable, found, Except.mapError, Except.map, cacheWithAmbient] <;> rfl

theorem evalPatternCache_own_cache (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState)
    (reference : Nat) (key : JSString) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool)
    (cacheFound : before.base.regexp.ambient.environment.lookup "patternCache" = some (.object reference))
    (keyFound : before.base.regexp.ambient.environment.lookup "cacheKey" = some (.string key))
    (objectFound : before.base.regexp.ambient.objects[reference]? = some object)
    (own : object.own.lookup key = some (.data value writable enumerable configurable)) :
    evalPatternCacheExpr (extra + 4) limit context
      (.index (.ordinary (.variable "patternCache")) (.ordinary (.variable "cacheKey"))) before = .ok (value, before) := by
  have read := getProperty_data before.base.regexp.ambient.objects reference 31 key object value writable enumerable configurable objectFound own
  change getProperty propertyFuel before.base.regexp.ambient.objects reference key = .ok value at read
  simp [evalPatternCacheExpr, evalExpression, lookupVariable, cacheFound, keyFound, cacheReadProperty,
    read, Except.mapError, Except.map, cacheWithAmbient, bind, Except.bind, pure, Except.pure]

/-- Exact three-element evaluation/fuel equation. All operand reads occur in
current states after literal allocation and each previous own element creation. -/
theorem evalPatternCache_array3 (fuel limit : Nat) (context : PatternCacheContext)
    (first second third : PatternCacheExpr) (before : LabelMatchState) :
    evalPatternCacheExpr (fuel + 5) limit context (.arrayLiteral [first, second, third]) before =
      (do
        let (firstValue, after) ← evalPatternCacheExpr (fuel + 3) limit context first (cacheEmptyArray before)
        let after ← cacheAppendElement before.base.regexp.ambient.heap.length firstValue after
        let (secondValue, after) ← evalPatternCacheExpr (fuel + 2) limit context second after
        let after ← cacheAppendElement before.base.regexp.ambient.heap.length secondValue after
        let (thirdValue, after) ← evalPatternCacheExpr (fuel + 1) limit context third after
        let after ← cacheAppendElement before.base.regexp.ambient.heap.length thirdValue after
        pure (.array before.base.regexp.ambient.heap.length, after)) := by
  rw [evalPatternCacheExpr]
  simp only [evalPatternCacheElements, bind_assoc]
  rfl

end HonoLean.Upstream.SourceSubset
