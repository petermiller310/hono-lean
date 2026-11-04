import HonoLean.Upstream.ECMA2025.LiteralLookahead.VM
import HonoLean.Upstream.PatternCache.Source

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.SourceSubset.LookaheadRegExp
open ECMA2025

structure Record where
  originalSource : JSString
  originalFlags : JSString := []
  compiled : List LiteralLookahead.Instruction
  deriving Repr, DecidableEq

/-- Additive metadata uses the SAME ordinary objects, arrays and exec views as
the frozen source VM. No new instruction is disguised as a range instruction. -/
structure State where
  base : LabelMatchState
  records : List (Nat × Record) := []
  deriving Repr

inductive TaggedRecord where
  | lookahead (record : Record)
  | label (record : LabelRegExpRecord)
  | range (record : RangeRegExpRecord)
  deriving Repr

def taggedEntries (before : State) : List (Nat × TaggedRecord) :=
  before.records.map (fun (reference, record) => (reference, .lookahead record)) ++
  before.base.brands.map (fun (reference, record) => (reference, .label record)) ++
  before.base.base.regexp.brands.map (fun (reference, record) => (reference, .range record))

/-- Initial representation facts: all three stores describe allocated objects
and each object has exactly one authoritative record. These are not future
constructor/exec outcomes. The runtime checks this domain at those operations. -/
structure Coherent (before : State) : Prop where
  allocated : ∀ entry ∈ taggedEntries before, entry.1 < before.base.base.regexp.ambient.objects.length
  unique : ((taggedEntries before).map Prod.fst).Nodup

def wellFormed (before : State) : Bool :=
  (taggedEntries before).all (fun entry => decide (entry.1 < before.base.base.regexp.ambient.objects.length)) &&
  decide (((taggedEntries before).map Prod.fst).Nodup)

def recordAt (before : State) (reference : Nat) : Option TaggedRecord :=
  (taggedEntries before).lookup reference

inductive Error where
  | pattern (error : PatternCacheError)
  | constructor (error : RegExpConstructError)
  | exec (error : RegExpCallError)
  | recordKind
  deriving Repr, DecidableEq

def withBase (before : State) (base : LabelMatchState) : State := {before with base}
def withAmbient (before : State) (ambient : SourceSubset.State) : State :=
  withBase before (cacheWithAmbient before.base ambient)

def initializeRecord (source flags : JSString) : Option Record := do
  if !flags.isEmpty then none else
  let ast ← LiteralLookahead.parse source
  let compiled ← LiteralLookahead.compile ast
  pure ⟨source, flags, compiled⟩

def allocatedState (before : State) (prototype : Nat) : State :=
  withAmbient before {before.base.base.regexp.ambient with
    objects := before.base.base.regexp.ambient.objects ++ [uninitializedRegExpObject prototype]}

def constructedState (before : State) (prototype : Nat) (record : Record) : State :=
  {withAmbient before {before.base.base.regexp.ambient with
    objects := before.base.base.regexp.ambient.objects ++ [initializedRegExpObject prototype]} with
    records := (before.base.base.regexp.ambient.objects.length, record) :: before.records}

/-- Allocation has already happened. Initialization parses/compiles the actual
raw string and performs the shared ordinary strict Set(lastIndex,0). Except
does not retain intermediate error state and implies no rollback theorem. -/
def initializeAllocated (reference : Nat) (source : JSString) (before : State) : Except Error (Value × State) := do
  let record ← match initializeRecord source [] with
    | some record => .ok record | none => .error (.constructor .grammarDomain)
  let objects ← (setProperty propertyFuel before.base.base.regexp.ambient.objects reference lastIndexKey (.number 0)).mapError
    (Error.constructor ∘ RegExpConstructError.evaluation ∘ EvalError.objectError)
  pure (.object reference, {withAmbient before {before.base.base.regexp.ambient with objects} with
    records := (reference, record) :: before.records})

/-- This closed constructor directly handles the new grammar. It never invokes
the old range constructor and never catches/replays an old grammar failure. -/
def invokeConstructor (context : RegExpConstructContext) (callee argument : Value) (before : State) : Except Error (Value × State) := do
  if !wellFormed before || !constructorTablesSeparated context before.base.base.regexp.ambient then
    throw (.constructor .representation) else do
  let constructor ← match constructorAt context.constructors callee with
    | some constructor => .ok constructor | none => .error (.constructor .constructorDomain)
  let _ ← match before.base.base.regexp.ambient.objects[constructor.prototype]? with
    | some object => .ok object | none => .error (.constructor .prototypeDomain)
  let allocated := allocatedState before constructor.prototype
  let source ← match argument with
    | .string source => .ok source | _ => .error (.constructor .coercionDomain)
  initializeAllocated before.base.base.regexp.ambient.objects.length source allocated

/-- Closed default, nonglobal builtin exec for the NEW record kind. Method Get,
custom exec callbacks and search/source156 integration remain separate work. -/
def invokeExec (receiver : Value) (arguments : List Value) (before : State) : Except Error (Value × State) := do
  if !wellFormed before then throw (.exec .representation) else do
  let (reference, record) ← match receiver with
    | .object reference => match recordAt before reference with
      | some (.lookahead record) => .ok (reference, record)
      | some _ => .error .recordKind
      | none => .error (.exec .unbrandedReceiver)
    | _ => .error (.exec .unbrandedReceiver)
  let input ← match arguments.headD .undefined with
    | .string input => .ok input | _ => .error (.exec .unsupportedCoercion)
  let last ← (getProperty propertyFuel before.base.base.regexp.ambient.objects reference lastIndexKey).mapError
    (Error.exec ∘ RegExpCallError.evaluation ∘ EvalError.objectError)
  let _ ← (numericToLength last).mapError Error.exec
  if !record.originalFlags.isEmpty then throw (.exec .unsupportedFlags) else do
  match LiteralLookahead.execute record.compiled input with
  | .exhausted => throw (.exec .exhausted)
  | .noMatch => pure (.null, before)
  | .matched matched =>
    if matched.captures.isEmpty && decide (matched.start ≤ matched.stop ∧ matched.stop ≤ input.length) then
      let (value, after) := materializeRegExpMatch before.base.base.regexp input matched
      pure (value, withBase before {before.base with base := {before.base.base with regexp := after}})
    else throw (.exec .representation)

mutual
  /-- Additive expression evaluator over the actual frozen PatternCacheExpr.
  The selected source67 tuple uses ordinary/index/multi-template/construct/array
  cases. A constructor saves its current callee before evaluating its argument.
  Full cache statements and lexical arrow invocation are not implemented here. -/
  def evalExpr : Nat → Nat → PatternCacheContext → PatternCacheExpr → State → Except Error (Value × State)
    | 0, _, _, _, _ => .error (.pattern .exhausted)
    | fuel + 1, limit, context, expression, before => do
      match expression with
      | .ordinary expression =>
        let (value, ambient) ← (evalExpression fuel limit expression before.base.base.regexp.ambient).mapError (Error.pattern ∘ PatternCacheError.evaluation)
        pure (value, withAmbient before ambient)
      | .index base key =>
        let (base, after) ← evalExpr fuel limit context base before
        let (key, after) ← evalExpr fuel limit context key after
        let value ← (cacheReadProperty base key after.base.base.regexp.ambient).mapError (Error.pattern ∘ PatternCacheError.evaluation)
        pure (value, after)
      | .logicalNot expression =>
        let (value, after) ← evalExpr fuel limit context expression before
        pure (.boolean (!truthy value), after)
      | .logicalAnd left right =>
        let (value, after) ← evalExpr fuel limit context left before
        if truthy value then evalExpr fuel limit context right after else pure (value, after)
      | .strictEqual left right =>
        let (left, after) ← evalExpr fuel limit context left before
        let (right, after) ← evalExpr fuel limit context right after
        pure (.boolean (decide (left = right)), after)
      | .strictNotEqual left right =>
        let (left, after) ← evalExpr fuel limit context left before
        let (right, after) ← evalExpr fuel limit context right after
        pure (.boolean (decide (left ≠ right)), after)
      | .conditional condition yes no =>
        let (value, after) ← evalExpr fuel limit context condition before
        evalExpr fuel limit context (if truthy value then yes else no) after
      | .template head substitutions =>
        let (tail, base) ← (evalPatternCacheTemplate fuel limit substitutions before.base).mapError Error.pattern
        pure (.string (head ++ tail), withBase before base)
      | .construct callee argument =>
        let (saved, ambient) ← (evalExpression fuel limit callee before.base.base.regexp.ambient).mapError (Error.pattern ∘ PatternCacheError.evaluation)
        let (argument, after) ← evalExpr fuel limit context argument (withAmbient before ambient)
        invokeConstructor context.label.iterators.constructors saved argument after
      | .arrayLiteral elements =>
        let reference := before.base.base.regexp.ambient.heap.length
        let after ← evalElements fuel limit context reference elements (withBase before (cacheEmptyArray before.base))
        pure (.array reference, after)
      | .emptyObject =>
        let (value, ambient) ← (createLiteralObject before.base.base.regexp.ambient).mapError (Error.pattern ∘ PatternCacheError.evaluation)
        pure (value, withAmbient before ambient)
      | .labelMatch receiver method literal =>
        let (value, base) ← (runLabelMatch fuel limit context.label ⟨"", receiver, method, literal⟩ before.base).mapError (Error.pattern ∘ PatternCacheError.label)
        pure (value, withBase before base)
  def evalElements : Nat → Nat → PatternCacheContext → Nat → List PatternCacheExpr → State → Except Error State
    | 0, _, _, _, _, _ => .error (.pattern .exhausted)
    | _ + 1, _, _, _, [], before => .ok before
    | fuel + 1, limit, context, reference, expression :: rest, before => do
      let (value, after) ← evalExpr fuel limit context expression before
      let base ← (cacheAppendElement reference value after.base).mapError Error.pattern
      evalElements fuel limit context reference rest (withBase after base)
end

/-- Selected real declaration semantics, retaining its new value binding. This
does not run a body wrapper that would restore/drop that binding. -/
def executeDeclaration (fuel limit : Nat) (context : PatternCacheContext) (statement : PatternCacheStmt) (before : State) : Except Error State := do
  match statement with
  | .declare name initializer =>
    let (value, after) ← evalExpr fuel limit context initializer before
    pure (withAmbient after {after.base.base.regexp.ambient with
      environment := (name, value) :: after.base.base.regexp.ambient.environment})
  | _ => .error (.pattern (.evaluation .unsupported))

end HonoLean.Upstream.SourceSubset.LookaheadRegExp
