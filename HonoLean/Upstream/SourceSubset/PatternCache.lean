import HonoLean.Upstream.SourceSubset.PatternCacheSyntax
import HonoLean.Upstream.SourceSubset.LabelMatchRealm

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

structure PatternCacheContext where
  label : LabelMatchContext
  deriving Repr
inductive PatternCacheError where
  | evaluation (error : EvalError)
  | label (error : LabelMatchError)
  | constructor (error : RegExpConstructError)
  | coercionDomain | exhausted
  deriving Repr, DecidableEq
inductive PatternCacheCompletion where
  | normal (state : LabelMatchState)
  | returned (value : Value) (state : LabelMatchState)
  deriving Repr

def cacheAscii (value : String) : JSString := value.toList.map (fun unit => UInt16.ofNat unit.toNat)

/-- Primitive ToString specialization. Exact modeled safe integers use decimal
notation; signed zero/fraction/NaN/infinity and object coercion stay open. -/
def cachePrimitiveToString : Value → Except PatternCacheError JSString
  | .string value => .ok value
  | .undefined => .ok (cacheAscii "undefined")
  | .null => .ok (cacheAscii "null")
  | .boolean true => .ok (cacheAscii "true")
  | .boolean false => .ok (cacheAscii "false")
  | .number value => if value.natAbs ≤ maximumSafeInteger then .ok (cacheAscii (toString value)) else .error .coercionDomain
  | _ => .error .coercionDomain

def patternCacheKey (label : JSString) (next : Value) : Except PatternCacheError JSString :=
  (cachePrimitiveToString next).map (fun suffix => label ++ [35] ++ suffix)

def cacheWithAmbient (before : LabelMatchState) (ambient : State) : LabelMatchState :=
  {before with base := {before.base with regexp := {before.base.regexp with ambient}}}

def cacheReadProperty (base key : Value) (before : State) : Except EvalError Value :=
  match base, key with
  | .string value, .number (.ofNat index) => .ok ((value[index]?).map (fun unit => Value.string [unit]) |>.getD .undefined)
  | _, _ => readProperty base key before

def cacheEmptyArray (before : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with heap := before.base.regexp.ambient.heap ++ [[]]}

def cacheAppendElement (reference : Nat) (value : Value) (before : LabelMatchState) : Except PatternCacheError LabelMatchState :=
  ((appendLiteralElements reference [value] before.base.regexp.ambient).mapError .evaluation).map (cacheWithAmbient before)

mutual
  def evalPatternCacheExpr : Nat → Nat → PatternCacheContext → PatternCacheExpr → LabelMatchState →
      Except PatternCacheError (Value × LabelMatchState)
    | 0, _, _, _, _ => .error .exhausted
    | fuel + 1, limit, context, expression, before => do
      match expression with
      | .ordinary value =>
        ((evalExpression fuel limit value before.base.regexp.ambient).mapError .evaluation).map
          (fun (value, after) => (value, cacheWithAmbient before after))
      | .index base key =>
        let (base, after) ← evalPatternCacheExpr fuel limit context base before
        let (key, after) ← evalPatternCacheExpr fuel limit context key after
        let value ← (cacheReadProperty base key after.base.regexp.ambient).mapError .evaluation
        pure (value, after)
      | .logicalNot value =>
        let (value, after) ← evalPatternCacheExpr fuel limit context value before
        pure (.boolean (!truthy value), after)
      | .logicalAnd left right =>
        let (left, after) ← evalPatternCacheExpr fuel limit context left before
        if truthy left then evalPatternCacheExpr fuel limit context right after else pure (left, after)
      | .strictEqual left right =>
        let (left, after) ← evalPatternCacheExpr fuel limit context left before
        let (right, after) ← evalPatternCacheExpr fuel limit context right after
        pure (.boolean (decide (left = right)), after)
      | .strictNotEqual left right =>
        let (left, after) ← evalPatternCacheExpr fuel limit context left before
        let (right, after) ← evalPatternCacheExpr fuel limit context right after
        pure (.boolean (decide (left ≠ right)), after)
      | .conditional condition yes no =>
        let (condition, after) ← evalPatternCacheExpr fuel limit context condition before
        evalPatternCacheExpr fuel limit context (if truthy condition then yes else no) after
      | .template head substitutions =>
        let (tail, after) ← evalPatternCacheTemplate fuel limit substitutions before
        pure (.string (head ++ tail), after)
      | .construct callee argument =>
        let (saved, ambient) ← (evalExpression fuel limit callee before.base.regexp.ambient).mapError .evaluation
        let (argument, after) ← evalPatternCacheExpr fuel limit context argument (cacheWithAmbient before ambient)
        let (value, constructed) ← (invokeRegExpConstructor context.label.iterators.constructors saved argument after.base.regexp).mapError .constructor
        pure (value, {after with base := {after.base with regexp := constructed}})
      | .arrayLiteral elements =>
        let reference := before.base.regexp.ambient.heap.length
        let after ← evalPatternCacheElements fuel limit context reference elements (cacheEmptyArray before)
        pure (.array reference, after)
      | .emptyObject =>
        ((createLiteralObject before.base.regexp.ambient).mapError .evaluation).map
          (fun (value, ambient) => (value, cacheWithAmbient before ambient))
      | .labelMatch receiver method literal =>
        (runLabelMatch fuel limit context.label ⟨"", receiver, method, literal⟩ before).mapError .label
  def evalPatternCacheTemplate : Nat → Nat → List (Expr × JSString) → LabelMatchState →
      Except PatternCacheError (JSString × LabelMatchState)
    | 0, _, _, _ => .error .exhausted
    | _ + 1, _, [], before => .ok ([], before)
    | fuel + 1, limit, (operand, literal) :: rest, before => do
      let (value, ambient) ← (evalExpression fuel limit operand before.base.regexp.ambient).mapError .evaluation
      let text ← cachePrimitiveToString value
      let (tail, after) ← evalPatternCacheTemplate fuel limit rest (cacheWithAmbient before ambient)
      pure (text ++ literal ++ tail, after)
  def evalPatternCacheElements : Nat → Nat → PatternCacheContext → Nat → List PatternCacheExpr → LabelMatchState →
      Except PatternCacheError LabelMatchState
    | 0, _, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, _, [], before => .ok before
    | fuel + 1, limit, context, reference, head :: rest, before => do
      let (value, after) ← evalPatternCacheExpr fuel limit context head before
      let after ← cacheAppendElement reference value after
      evalPatternCacheElements fuel limit context reference rest after
end

/-- Save the ordinary base/key reference BEFORE RHS, then use post-RHS strict
ordinary Set. No direct CreateDataProperty, hidden cache map or guessed tuple.
Only object/primitive-string references have native interpretation here. -/
def executePatternCacheAssignment (fuel limit : Nat) (context : PatternCacheContext)
    (target value : PatternCacheExpr) (before : LabelMatchState) : Except PatternCacheError LabelMatchState := do
  let (base, key, after) ← match target with
    | .index base key => do
      let (base, after) ← evalPatternCacheExpr fuel limit context base before
      let (key, after) ← evalPatternCacheExpr fuel limit context key after
      pure (base, key, after)
    | _ => .error (.evaluation .unsupported)
  let (value, after) ← evalPatternCacheExpr fuel limit context value after
  let objects ← match base, key with
    | .object reference, .string key =>
      (setProperty propertyFuel after.base.regexp.ambient.objects reference key value).mapError
        (PatternCacheError.evaluation ∘ EvalError.objectError)
    | _, _ => .error (.evaluation .unsupported)
  pure (cacheWithAmbient after {after.base.regexp.ambient with objects})

def cacheRestoreEnvironment (environment : List (String × Value)) : PatternCacheCompletion → PatternCacheCompletion
  | .normal after => .normal (cacheWithAmbient after {after.base.regexp.ambient with environment})
  | .returned value after => .returned value (cacheWithAmbient after {after.base.regexp.ambient with environment})

/-- Parser admission excludes outer lexical writes/callbacks; restoring a
branch's environment therefore drops only its fresh consts. All heap/private/
regexp effects remain. This is not general live lexical-cell block semantics. -/
def executePatternCache : Nat → Nat → PatternCacheContext → List PatternCacheStmt → LabelMatchState →
    Except PatternCacheError PatternCacheCompletion
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, [], before => .ok (.normal before)
  | fuel + 1, limit, context, head :: tail, before => do
    match head with
    | .declare name initializer =>
      let (value, after) ← evalPatternCacheExpr fuel limit context initializer before
      let after := cacheWithAmbient after {after.base.regexp.ambient with environment := (name, value) :: after.base.regexp.ambient.environment}
      executePatternCache fuel limit context tail after
    | .assign target value =>
      let after ← executePatternCacheAssignment fuel limit context target value before
      executePatternCache fuel limit context tail after
    | .ret value =>
      let (value, after) ← evalPatternCacheExpr fuel limit context value before
      pure (.returned value after)
    | .branch condition yes no =>
      let (condition, after) ← evalPatternCacheExpr fuel limit context condition before
      let completion ← executePatternCache fuel limit context (if truthy condition then yes else no) after
      match cacheRestoreEnvironment after.base.regexp.ambient.environment completion with
      | .normal after => executePatternCache fuel limit context tail after
      | .returned value after => pure (.returned value after)

def runPatternCache (fuel limit : Nat) (context : PatternCacheContext) (program : List PatternCacheStmt) (before : LabelMatchState) :
    Except PatternCacheError (Value × LabelMatchState) := do
  let result ← executePatternCache fuel limit context program before
  match cacheRestoreEnvironment before.base.regexp.ambient.environment result with
  | .normal after => pure (.undefined, after)
  | .returned value after => pure (value, after)

def initializePatternCache (fuel limit : Nat) (context : PatternCacheContext) (declaration : PatternCacheInit) (before : LabelMatchState) :
    Except PatternCacheError LabelMatchState := do
  let (value, after) ← evalPatternCacheExpr fuel limit context declaration.initializer before
  pure (cacheWithAmbient after {after.base.regexp.ambient with environment := (declaration.name, value) :: after.base.regexp.ambient.environment})

end HonoLean.Upstream.SourceSubset
