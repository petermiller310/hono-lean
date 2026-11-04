import HonoLean.Upstream.SourceSubset.LookaheadRegExp.Rules
import HonoLean.Upstream.PatternCacheTerminal.Activation

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternLookahead
open SourceSubset hiding pinnedSource State
open ECMA2025

/-- Initial constructor/table/prototype and raw-source grammar facts. No
compiled record, successful constructor call, Set or future heap is an input. -/
structure ConstructorInputs (before : LookaheadRegExp.State) (context : RegExpConstructContext) (handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next : JSString) : Prop where
  coherent : LookaheadRegExp.Coherent before
  noArgBefore : before.base.base.regexp.ambient.functions.length ≤ context.constructors.base
  methodsBefore : context.methods.base + context.methods.entries.length ≤ context.constructors.base
  functionsBefore : context.functions.base + context.functions.entries.length ≤ context.constructors.base
  membersBefore : context.members.base + context.members.entries.length ≤ context.constructors.base
  builtinsBefore : context.builtins.base + context.builtins.entries.length ≤ context.constructors.base
  handleBound : context.constructors.base ≤ handle
  identity : context.constructors.entries[handle - context.constructors.base]? = some constructor
  prototypeFound : before.base.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  nextSafe : LiteralLookahead.SafeNext next

structure ConstructionContract (before after : LookaheadRegExp.State) (returned : Value) (prototype : Nat)
    (lower upper : UInt16) (next : JSString) : Prop where
  returned : returned = .object before.base.base.regexp.ambient.objects.length
  base : after.base = cacheWithAmbient before.base {before.base.base.regexp.ambient with
    objects := before.base.base.regexp.ambient.objects ++ [initializedRegExpObject prototype]}
  records : after.records = (before.base.base.regexp.ambient.objects.length, LookaheadRegExp.compiledRecord lower upper next) :: before.records
  object : after.base.base.regexp.ambient.objects[before.base.base.regexp.ambient.objects.length]? = some (initializedRegExpObject prototype)
  lastIndex : (initializedRegExpObject prototype).own.lookup lastIndexKey = some (.data (.number 0) true false false)
  oldObjects : ∀ reference, reference < before.base.base.regexp.ambient.objects.length →
    after.base.base.regexp.ambient.objects[reference]? = before.base.base.regexp.ambient.objects[reference]?
  coherent : LookaheadRegExp.Coherent after

/-- This observes an already initialized tagged record and CURRENT own numeric
lastIndex. Construction-to-exec composition derives every one of these facts. -/
structure ExecInputs (before : LookaheadRegExp.State) (reference : Nat) (object : OrdinaryObject) (last : Int) (writable : Bool)
    (lower upper : UInt16) (next : JSString) : Prop where
  coherent : LookaheadRegExp.Coherent before
  record : before.records.lookup reference = some (LookaheadRegExp.compiledRecord lower upper next)
  objectFound : before.base.base.regexp.ambient.objects[reference]? = some object
  lastIndex : object.own.lookup lastIndexKey = some (.data (.number last) writable false false)
  safeLast : last.natAbs ≤ SourceSubset.maximumSafeInteger
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  nextSafe : LiteralLookahead.SafeNext next

def prefixState (before : LookaheadRegExp.State) (input taken : JSString) : LookaheadRegExp.State :=
  LookaheadRegExp.withBase before {before.base with base := {before.base.base with regexp := {before.base.base.regexp with
    ambient := {before.base.base.regexp.ambient with heap := before.base.base.regexp.ambient.heap ++ [[.string taken]]}
    results := (before.base.base.regexp.ambient.heap.length, ⟨0, input⟩) :: before.base.base.regexp.results}}}

/-- The slash/next assertion does not belong to the returned match. A success
consumes a nonempty range prefix, records index0 and the complete original input,
and permits an arbitrary suffix after the asserted literal. No VM result or
parser/compiler outcome occurs in this independent contract. -/
def ExecContract (before after : LookaheadRegExp.State) (returned : Value) (lower upper : UInt16) (next input : JSString) : Prop :=
  (returned = .null ∧ after = before ∧ ¬ LiteralLookahead.Accepted lower upper next input) ∨
  ∃ taken suffix, input = taken ++ (47 :: next ++ suffix) ∧ taken ≠ [] ∧
    (∀ unit ∈ taken, RangeRegExp.InRange lower upper unit) ∧
    returned = .array before.base.base.regexp.ambient.heap.length ∧ after = prefixState before input taken

/-- Independent selected-path endpoint: the label language supplies its three
capture values, the raw key supplies tuple slot0, and the assertion's compiled
record occupies a distinct freshly allocated object. No source VM is called. -/
def selectedState (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (prototype : Nat) : LookaheadRegExp.State :=
  let input := LabelMatch.safeRangeLabel name lower upper
  let matched := PatternCacheTerminal.matchedSnapshot before.base context input name (some (PatternConstruct.rawBody lower upper))
  let keyed := cacheWithAmbient matched {matched.base.regexp.ambient with
    environment := ("cacheKey", .string (PatternCache.key input (some next))) :: matched.base.regexp.ambient.environment}
  let tuple := cacheArrayCellState keyed [.string (PatternCache.key input (some next)), .string name,
    .object (before.base.base.regexp.ambient.objects.length + 1)]
  LookaheadRegExp.constructedState ⟨tuple, before.records⟩ prototype (LookaheadRegExp.compiledRecord lower upper next)

structure SelectedContract (before after : LookaheadRegExp.State) (returned : Value) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (prototype : Nat) : Prop where
  state : after = selectedState before context name lower upper next prototype
  returned : returned = .array (before.base.base.regexp.ambient.heap.length + 1)
  tuple : after.base.base.regexp.ambient.heap[before.base.base.regexp.ambient.heap.length + 1]? =
    some [.string (PatternCache.key (LabelMatch.safeRangeLabel name lower upper) (some next)), .string name,
      .object (before.base.base.regexp.ambient.objects.length + 1)]
  matcher : after.base.base.regexp.ambient.objects[before.base.base.regexp.ambient.objects.length + 1]? = some (initializedRegExpObject prototype)
  record : after.records.lookup (before.base.base.regexp.ambient.objects.length + 1) = some (LookaheadRegExp.compiledRecord lower upper next)
  coherent : LookaheadRegExp.Coherent after

/-- Public selected-source inputs are BEFORE source60. Neither the capture
array nor the source62 cacheKey nor a future constructor/query result is given. -/
structure Inputs (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16) (next : JSString)
    (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop where
  source : LabelMatch.Inputs before.base context.label (LabelMatch.safeRangeLabel name lower upper)
  coherent : LookaheadRegExp.Coherent before
  nameValid : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  nextSafe : LiteralLookahead.SafeNext next
  nextBinding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next)
  constructorBinding : before.base.base.regexp.ambient.environment.lookup "RegExp" = some (.function handle)
  handleBound : context.label.iterators.constructors.constructors.base ≤ handle
  identity : context.label.iterators.constructors.constructors.entries[handle - context.label.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.base.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

end HonoLean.Upstream.GetPatternLookahead
