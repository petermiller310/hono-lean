import HonoLean.Upstream.PatternCache.Composition
import HonoLean.Upstream.LabelMatch.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.PatternCacheTerminal
open SourceSubset ECMA2025
open PatternCache

/-- Exactly the typed next values selecting source68. The suffix is arbitrary
UTF16; the actual short-circuit condition, not a supplied Boolean, is proved. -/
def TerminalNext (next : Option JSString) : Prop :=
  next = none ∨ next = some [] ∨ (∃ suffix, next = some (58 :: suffix)) ∨ (∃ suffix, next = some (42 :: suffix))

/-- All facts are BEFORE source60. In particular no capture array, tuple,
compiled record, successful Set or future Get appears in this domain. -/
structure Inputs (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop
    extends HeaderInputs before context (LabelMatch.safeRangeLabel name lower upper) name
      (some (PatternConstruct.rawBody lower upper)) next cache object descriptor depth where
  terminal : TerminalNext next
  validName : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ truthy value = false
  writable : WritableData object (key (LabelMatch.safeRangeLabel name lower upper) next) descriptor
  constructorBinding : before.base.regexp.ambient.environment.lookup "RegExp" = some (.function handle)
  handleBound : context.label.iterators.constructors.constructors.base ≤ handle
  identity : context.label.iterators.constructors.constructors.entries[handle - context.label.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

def rangeState (before : LabelMatchState) (prototype : Nat) (lower upper : UInt16) : LabelMatchState :=
  {before with base := {before.base with regexp := regExpConstructedState before.base.regexp prototype (constructedRangeRecord lower upper)}}

def tupleValues (before : LabelMatchState) (input name : JSString) : List Value :=
  [.string input, .string name, .object before.base.regexp.ambient.objects.length]
def tupleState (before : LabelMatchState) (prototype : Nat) (lower upper : UInt16) (input name : JSString) : LabelMatchState :=
  rangeState (cacheArrayCellState before (tupleValues before input name)) prototype lower upper
def storedState (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) : LabelMatchState :=
  let input := LabelMatch.safeRangeLabel name lower upper
  let rhs := tupleState (keyedState before context input next) prototype lower upper input name
  cacheWithAmbient rhs {rhs.base.regexp.ambient with
    objects := rhs.base.regexp.ambient.objects.set cache
      (updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1)))}
def resultState (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) : LabelMatchState :=
  resetCaller before (storedState before context name lower upper next cache object prototype)

/-- Terminal construction adds a RANGE brand; the previous plain-cache Frames
predicate intentionally cannot be reused since it frames that list unchanged. -/
structure Frames (before after : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (lower upper : UInt16) : Prop where
  environment : after.base.regexp.ambient.environment = before.base.regexp.ambient.environment
  functions : after.base.regexp.ambient.functions = before.base.regexp.ambient.functions
  privates : after.base.regexp.ambient.privates = before.base.regexp.ambient.privates
  sets : after.base.regexp.ambient.sets = before.base.regexp.ambient.sets
  thisValue : after.base.regexp.ambient.thisValue = before.base.regexp.ambient.thisValue
  rangeBrands : after.base.regexp.brands = (before.base.regexp.ambient.objects.length + 1, constructedRangeRecord lower upper) :: before.base.regexp.brands
  rangeResults : after.base.regexp.results = before.base.regexp.results
  iteratorSymbols : after.base.symbols = before.base.symbols
  iterators : after.base.iterators = before.base.iterators
  iteratorTrace : after.base.trace = before.base.trace
  labelSymbols : after.symbols = before.symbols
  accessors : after.accessors = before.accessors
  labelBrands : after.brands = (before.base.regexp.ambient.objects.length, labelLiteralRecord) :: before.brands
  labelResults : after.results = (before.base.regexp.ambient.heap.length, ⟨0, input⟩) :: before.results
  trace : after.trace = before.trace ++ LabelMatch.sourceEvents before context.label input

/-- Independent terminal tuple/cache/initialized-regexp relation. Cache aliases
observe the write; all other old objects and all old arrays are preserved. -/
structure Contract (before after : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) (returned : Value) : Prop where
  resultValue : returned = .array (before.base.regexp.ambient.heap.length + 1)
  arrays : after.base.regexp.ambient.heap = before.base.regexp.ambient.heap ++
    [LabelMatch.captures (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)),
     [.string (LabelMatch.safeRangeLabel name lower upper), .string name, .object (before.base.regexp.ambient.objects.length + 1)]]
  objects : after.base.regexp.ambient.objects =
    (before.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype, initializedRegExpObject prototype]).set cache
      (updatedObject object (key (LabelMatch.safeRangeLabel name lower upper) next) returned)
  cacheOwn : ∃ updated enumerable configurable, after.base.regexp.ambient.objects[cache]? = some updated ∧
    updated.own.lookup (key (LabelMatch.safeRangeLabel name lower upper) next) = some (.data returned true enumerable configurable) ∧
    updated.prototype = object.prototype ∧ updated.extensible = object.extensible
  regexFound : after.base.regexp.ambient.objects[before.base.regexp.ambient.objects.length + 1]? = some (initializedRegExpObject prototype)
  lastIndex : (initializedRegExpObject prototype).own.lookup lastIndexKey = some (.data (.number 0) true false false)
  internal : after.base.regexp.brands.lookup (before.base.regexp.ambient.objects.length + 1) = some (constructedRangeRecord lower upper)
  source : (constructedRangeRecord lower upper).originalSource = PatternConstruct.assembledSource lower upper
  flags : (constructedRangeRecord lower upper).originalFlags = []
  compiled : (constructedRangeRecord lower upper).compiled = RangeRegExp.code lower upper
  language : ∀ input, RangeRegExp.execute (constructedRangeRecord lower upper).compiled input =
    if RangeRegExp.Accepted lower upper input then .matched ⟨0, input.length, []⟩ else .noMatch
  otherObjects : ∀ reference, reference ≠ cache → reference < before.base.regexp.ambient.objects.length →
    after.base.regexp.ambient.objects[reference]? = before.base.regexp.ambient.objects[reference]?
  oldArrays : ∀ reference, reference < before.base.regexp.ambient.heap.length → after.base.regexp.ambient.heap[reference]? = before.base.regexp.ambient.heap[reference]?
  frames : Frames before after context (LabelMatch.safeRangeLabel name lower upper) lower upper

end HonoLean.Upstream.PatternCacheTerminal
