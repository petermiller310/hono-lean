import HonoLean.Upstream.PatternCache.Source
import HonoLean.Upstream.NodeCaptureGuard.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.PatternCache
open SourceSubset ECMA2025

def nextValue : Option JSString → Value | none => .undefined | some next => .string next
def nextText : Option JSString → JSString | none => [117,110,100,101,102,105,110,101,100] | some next => next
def key (input : JSString) (next : Option JSString) : JSString := input ++ [35] ++ nextText next

def resetCaller (before after : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient after {after.base.regexp.ambient with environment := before.base.regexp.ambient.environment}
def matchedState (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) : LabelMatchState :=
  LabelMatch.resultState before context.label input

def plainValues (input name : JSString) : List Value := [.string input, .string name, .boolean true]
def plainArray (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) : LabelMatchState :=
  let matched := matchedState before context input
  cacheWithAmbient matched {matched.base.regexp.ambient with heap := matched.base.regexp.ambient.heap ++ [plainValues input name]}

def updatedObject (object : OrdinaryObject) (key : JSString) (value : Value) : OrdinaryObject :=
  match object.own.lookup key with
  | some (.data _ true enumerable configurable) =>
    {object with own := putOwn key (.data value true enumerable configurable) object.own}
  | _ => newDataObject object key value

def WritableData (object : OrdinaryObject) (key : JSString) (descriptor : Option PropertyDescriptor) : Prop :=
  (descriptor = none ∨ ∃ previous enumerable configurable, descriptor = some (.data previous true enumerable configurable)) ∧
  ((object.own.lookup key = none ∧ object.extensible = true) ∨
    ∃ previous enumerable configurable, object.own.lookup key = some (.data previous true enumerable configurable))

/-- Real cache/key inputs BEFORE source60. The computed match is not staged.
The next optional-string domain is the source's ordinary typed-input slice;
other primitive/coercion behaviors remain separate interpreter controls. -/
structure HeaderInputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop where
  source : LabelMatch.Inputs before context.label input
  label : LabelRegExp.Label input name body
  nextBinding : before.base.regexp.ambient.environment.lookup "next" = some (nextValue next)
  cacheBinding : before.base.regexp.ambient.environment.lookup "patternCache" = some (.object cache)
  cacheFound : before.base.regexp.ambient.objects[cache]? = some object
  path : NodeCaptureGuard.DescriptorPath before.base.regexp.ambient.objects (key input next) cache descriptor depth
  pathBound : depth ≤ propertyFuel

/-- Any truthy DATA value is retained: no tuple validation, match-index/cold
constructor readiness, extensibility or writable-slot premise is supplied. -/
structure WarmInputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat) : Prop
    extends HeaderInputs before context input name body next cache object (some (.data value writable enumerable configurable)) depth where
  truthy : SourceSubset.truthy value = true

/-- Missing/inherited writable or existing writable DATA permits ordinary Set.
No successful Set, post-cache object, future return lookup or tuple is an input. -/
structure PlainInputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop
    extends HeaderInputs before context input name none next cache object descriptor depth where
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  writable : WritableData object (key input next) descriptor


/-- Minimal actual440B warm-entry domain: no match binding or producer realm is
needed because its cold branch is not evaluated. All reads derive from this
initial finite DATA path, not a future Get outcome. -/
structure BlockWarmInputs (before : LabelMatchState) (input : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat) : Prop where
  labelBinding : before.base.regexp.ambient.environment.lookup "label" = some (.string input)
  nextBinding : before.base.regexp.ambient.environment.lookup "next" = some (nextValue next)
  cacheBinding : before.base.regexp.ambient.environment.lookup "patternCache" = some (.object cache)
  cacheFound : before.base.regexp.ambient.objects[cache]? = some object
  path : NodeCaptureGuard.DescriptorPath before.base.regexp.ambient.objects (key input next) cache
    (some (.data value writable enumerable configurable)) depth
  pathBound : depth ≤ propertyFuel
  truthy : SourceSubset.truthy value = true

/-- Common unchanged caller and source-runtime components. Cache-object mutation
is handled separately, so aliases to that object observe the actual write. -/
structure Frames (before after : LabelMatchState) (context : PatternCacheContext) (input : JSString) : Prop where
  environment : after.base.regexp.ambient.environment = before.base.regexp.ambient.environment
  functions : after.base.regexp.ambient.functions = before.base.regexp.ambient.functions
  privates : after.base.regexp.ambient.privates = before.base.regexp.ambient.privates
  sets : after.base.regexp.ambient.sets = before.base.regexp.ambient.sets
  thisValue : after.base.regexp.ambient.thisValue = before.base.regexp.ambient.thisValue
  rangeBrands : after.base.regexp.brands = before.base.regexp.brands
  rangeResults : after.base.regexp.results = before.base.regexp.results
  iteratorSymbols : after.base.symbols = before.base.symbols
  iterators : after.base.iterators = before.base.iterators
  iteratorTrace : after.base.trace = before.base.trace
  labelSymbols : after.symbols = before.symbols
  accessors : after.accessors = before.accessors
  labelBrands : after.brands = (before.base.regexp.ambient.objects.length, labelLiteralRecord) :: before.brands
  labelResults : ((∃ name body, LabelRegExp.Label input name body) →
    after.results = (before.base.regexp.ambient.heap.length, ⟨0, input⟩) :: before.results) ∧
    ((¬ ∃ name body, LabelRegExp.Label input name body) → after.results = before.results)
  trace : after.trace = before.trace ++ LabelMatch.sourceEvents before context.label input

structure WarmContract (before after : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (cache : Nat) (retained returned : Value) : Prop where
  returned : returned = retained
  cacheObject : after.base.regexp.ambient.objects[cache]? = before.base.regexp.ambient.objects[cache]?
  captures : after.base.regexp.ambient.heap = before.base.regexp.ambient.heap ++ [LabelMatch.captures input name body]
  objects : after.base.regexp.ambient.objects = before.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype]
  oldArrays : ∀ reference, reference < before.base.regexp.ambient.heap.length → after.base.regexp.ambient.heap[reference]? = before.base.regexp.ambient.heap[reference]?
  frames : Frames before after context input

structure PlainContract (before after : LabelMatchState) (context : PatternCacheContext) (input name : JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (returned : Value) : Prop where
  returned : returned = .array (before.base.regexp.ambient.heap.length + 1)
  captures : after.base.regexp.ambient.heap = before.base.regexp.ambient.heap ++ [LabelMatch.captures input name none, plainValues input name]
  objects : after.base.regexp.ambient.objects =
    (before.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype]).set cache
      (updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1)))
  cacheOwn : ∃ updated, after.base.regexp.ambient.objects[cache]? = some updated ∧
    ∃ enumerable configurable, updated.own.lookup (key input next) =
      some (.data (.array (before.base.regexp.ambient.heap.length + 1)) true enumerable configurable) ∧
      updated.prototype = object.prototype ∧ updated.extensible = object.extensible
  otherObjects : ∀ reference, reference ≠ cache → reference < before.base.regexp.ambient.objects.length →
    after.base.regexp.ambient.objects[reference]? = before.base.regexp.ambient.objects[reference]?
  oldArrays : ∀ reference, reference < before.base.regexp.ambient.heap.length → after.base.regexp.ambient.heap[reference]? = before.base.regexp.ambient.heap[reference]?
  frames : Frames before after context input

structure MissContract (before after : LabelMatchState) (context : PatternCacheContext) (input : JSString) (returned : Value) : Prop where
  returned : returned = .null
  arrays : after.base.regexp.ambient.heap = before.base.regexp.ambient.heap
  objects : after.base.regexp.ambient.objects = before.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype]
  frames : Frames before after context input

end HonoLean.Upstream.PatternCache
