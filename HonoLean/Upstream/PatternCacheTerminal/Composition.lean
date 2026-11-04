import HonoLean.Upstream.PatternCacheTerminal.Correctness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.PatternCacheTerminal
open SourceSubset ECMA2025 PatternCache

/-- BEFORE source50: the real inherited root path controls the future fresh
cache's first lookup. Empty own storage does not imply inherited absence. -/
structure InitInputs (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop where
  source : LabelMatch.Inputs before context.label (LabelMatch.safeRangeLabel name lower upper)
  validName : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  terminal : TerminalNext next
  nextBinding : before.base.regexp.ambient.environment.lookup "next" = some (nextValue next)
  rootFound : before.base.regexp.ambient.objects[ordinaryObjectPrototype]? = some root
  rootPath : NodeCaptureGuard.DescriptorPath before.base.regexp.ambient.objects
    (key (LabelMatch.safeRangeLabel name lower upper) next) ordinaryObjectPrototype descriptor depth
  pathBound : depth + 1 ≤ propertyFuel
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ truthy value = false
  dataWritable : descriptor = none ∨ ∃ value enumerable configurable, descriptor = some (.data value true enumerable configurable)
  constructorBinding : before.base.regexp.ambient.environment.lookup "RegExp" = some (.function handle)
  handleBound : context.label.iterators.constructors.constructors.base ≤ handle
  identity : context.label.iterators.constructors.constructors.entries[handle - context.label.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

theorem initialized_inputs (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitInputs before context name lower upper next root descriptor depth handle constructor prototypeObject) :
    Inputs (initializedPatternCacheState initProgram before) context name lower upper next before.base.regexp.ambient.objects.length
      emptyLiteralObject descriptor (depth + 1) handle constructor prototypeObject := by
  refine ⟨⟨initialized_label_inputs before context _ inputs.source,
    LabelMatch.safe_range_label name lower upper inputs.validName inputs.lowerSafe inputs.upperSafe, ?_, rfl, ?_,
    initialized_path before _ descriptor depth inputs.rootPath, inputs.pathBound⟩,
    inputs.terminal, inputs.validName, inputs.lowerSafe, inputs.upperSafe, inputs.ordered,
    inputs.falsy, ⟨inputs.dataWritable, Or.inl ⟨rfl, rfl⟩⟩, ?_, inputs.handleBound, inputs.identity, ?_⟩
  · change List.lookup "next" (("patternCache", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  · simp [initializedPatternCacheState, cacheWithAmbient]
  · change List.lookup "RegExp" (("patternCache", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.constructorBinding
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp inputs.prototypeFound).1).trans inputs.prototypeFound

/-- Actual50 and the actual533B body use the SAME object. This explicit
module/function activation handoff does not prove closure/module lifetime. -/
theorem source_init_then_terminal_satisfies (extraInit extraCall : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (name : JSString) (lower upper : UInt16) (next : Option JSString) (root : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitInputs before context name lower upper next root descriptor depth handle constructor prototypeObject) :
    sourceInit (extraInit + 2) context before = some (.ok (initializedPatternCacheState initProgram before)) ∧
    sourceCall (extraCall + 256) context (initializedPatternCacheState initProgram before) =
      some (.ok (.array (before.base.regexp.ambient.heap.length + 1),
        resultState (initializedPatternCacheState initProgram before) context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype)) ∧
    InitContract before (initializedPatternCacheState initProgram before) ∧
    Contract (initializedPatternCacheState initProgram before)
      (resultState (initializedPatternCacheState initProgram before) context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype)
      context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype (.array (before.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨initialized, allocation⟩ := source_init_satisfies extraInit before context root inputs.rootFound
  obtain ⟨called, contract⟩ := source_terminal_satisfies extraCall _ context name lower upper next _ emptyLiteralObject descriptor (depth + 1) handle constructor prototypeObject
    (initialized_inputs before context name lower upper next root descriptor depth handle constructor prototypeObject inputs)
  exact ⟨initialized, called, allocation, contract⟩

/-- Realm preservation is derived for caches distinct from the actual old
String/RegExp intrinsic prototypes. The broad single-call domain permits these
aliases; it would be false to assume a second standard-realm call for them. -/
theorem result_realm (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat)
    (inputs : LabelRealm before context.label)
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    LabelRealm (resultState before context name lower upper next cache object prototype) context.label := by
  have produced := LabelMatch.result_contract before context.label (LabelMatch.safeRangeLabel name lower upper)
  have objects := produced.objects
  constructor
  case stringFound =>
    obtain ⟨foundObject, found, own⟩ := inputs.stringFound
    refine ⟨foundObject, ?_, own⟩
    change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject prototype]).set cache _)[context.label.stringPrototype]? = _
    rw [List.getElem?_set_ne (Ne.symm differentString)]
    have old := (List.getElem?_eq_some_iff.mp found).1
    have matched := (produced.oldObjects context.label.stringPrototype old).trans found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp matched).1).trans matched
  case regexpFound =>
    obtain ⟨foundObject, found, own⟩ := inputs.regexpFound
    refine ⟨foundObject, ?_, own⟩
    change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject prototype]).set cache _)[context.label.regexpPrototype]? = _
    rw [List.getElem?_set_ne (Ne.symm differentRegExp)]
    have old := (List.getElem?_eq_some_iff.mp found).1
    have matched := (produced.oldObjects context.label.regexpPrototype old).trans found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp matched).1).trans matched
  case symbolOwners =>
    intro entry member
    change entry ∈ (LabelMatch.resultState before context.label (LabelMatch.safeRangeLabel name lower upper)).symbols at member
    rw [produced.symbols] at member
    have bound := inputs.symbolOwners entry member
    have count : (resultState before context name lower upper next cache object prototype).base.regexp.ambient.objects.length = before.base.regexp.ambient.objects.length + 2 := by
      change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject prototype]).set cache _).length = _
      rw [List.length_set]
      rw [List.length_append, List.length_singleton]
      change (LabelMatch.resultState before context.label _).base.regexp.ambient.objects.length + 1 = _
      rw [objects]
      simp
    rw [count]
    omega
  case noArgBefore =>
    change (LabelMatch.resultState before context.label _).base.regexp.ambient.functions.length ≤ _
    rw [produced.functions]
    exact inputs.noArgBefore
  case oldNoArg =>
    change (LabelMatch.resultState before context.label _).base.regexp.ambient.functions.length ≤ _
    rw [produced.functions]
    exact inputs.oldNoArg
  case symbol =>
    change ((LabelMatch.resultState before context.label _).symbols.lookup _).bind _ = _
    rw [produced.symbols]
    exact inputs.symbol
  case accessors =>
    change (LabelMatch.resultState before context.label _).accessors = _
    rw [produced.accessors]
    exact inputs.accessors
  all_goals cases inputs <;> assumption

theorem result_warm_inputs (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject)
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    ∃ updated enumerable configurable,
      WarmInputs (resultState before context name lower upper next cache object constructor.prototype) context (LabelMatch.safeRangeLabel name lower upper) name
        (some (PatternConstruct.rawBody lower upper)) next cache updated (.array (before.base.regexp.ambient.heap.length + 1)) true enumerable configurable 1 := by
  have contract := terminal_contract before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs
  obtain ⟨updated, enumerable, configurable, found, own, _, _⟩ := contract.cacheOwn
  refine ⟨updated, enumerable, configurable, ⟨⟨?_, inputs.label, ?_, ?_, found, .own found own, by decide⟩, rfl⟩⟩
  · exact ⟨result_realm before context name lower upper next cache object constructor.prototype inputs.source.toLabelRealm differentString differentRegExp,
      by rw [contract.frames.environment]; exact inputs.source.labelBinding⟩
  · rw [contract.frames.environment]; exact inputs.nextBinding
  · rw [contract.frames.environment]; exact inputs.cacheBinding

/-- Persistent same-heap reuse. The second full533B call still computes its
own match, then returns the FIRST tuple identity without invoking RegExp again. -/
theorem source_terminal_then_warm_satisfies (extraFirst extraSecond : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject)
    (differentString : context.label.stringPrototype ≠ cache) (differentRegExp : context.label.regexpPrototype ≠ cache) :
    let after := resultState before context name lower upper next cache object constructor.prototype
    sourceCall (extraFirst + 256) context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), after)) ∧
    sourceCall (extraSecond + 256) context after = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), warmState after context (LabelMatch.safeRangeLabel name lower upper))) ∧
    Contract before after context name lower upper next cache object constructor.prototype (.array (before.base.regexp.ambient.heap.length + 1)) ∧
    WarmContract after (warmState after context (LabelMatch.safeRangeLabel name lower upper)) context (LabelMatch.safeRangeLabel name lower upper) name
      (some (PatternConstruct.rawBody lower upper)) cache (.array (before.base.regexp.ambient.heap.length + 1)) (.array (before.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨first, contract⟩ := source_terminal_satisfies extraFirst before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs
  obtain ⟨updated, enumerable, configurable, ready⟩ := result_warm_inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs differentString differentRegExp
  obtain ⟨second, warm⟩ := source_warm_satisfies extraSecond _ context _ name _ next cache updated _ true enumerable configurable 1 ready
  exact ⟨first, second, contract, warm⟩

/-- One actual50 allocation, then two full source calls on the same persistent
cache and heap. Fresh50 separation derives preservation of the old standard
intrinsic realm; no second-call realm or future lookup is an input. -/
theorem source_init_then_terminal_then_warm_satisfies (extraInit extraFirst extraSecond : Nat)
    (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : InitInputs before context name lower upper next root descriptor depth handle constructor prototypeObject) :
    let initialized := initializedPatternCacheState initProgram before
    let after := resultState initialized context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype
    sourceInit (extraInit + 2) context before = some (.ok initialized) ∧
    sourceCall (extraFirst + 256) context initialized = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), after)) ∧
    sourceCall (extraSecond + 256) context after = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), warmState after context (LabelMatch.safeRangeLabel name lower upper))) ∧
    InitContract before initialized ∧
    Contract initialized after context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype (.array (before.base.regexp.ambient.heap.length + 1)) ∧
    WarmContract after (warmState after context (LabelMatch.safeRangeLabel name lower upper)) context (LabelMatch.safeRangeLabel name lower upper) name
      (some (PatternConstruct.rawBody lower upper)) before.base.regexp.ambient.objects.length (.array (before.base.regexp.ambient.heap.length + 1)) (.array (before.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨initialized, allocation⟩ := source_init_satisfies extraInit before context root inputs.rootFound
  obtain ⟨stringObject, stringFound, _⟩ := inputs.source.stringFound
  obtain ⟨regexpObject, regexpFound, _⟩ := inputs.source.regexpFound
  have stringBound := (List.getElem?_eq_some_iff.mp stringFound).1
  have regexpBound := (List.getElem?_eq_some_iff.mp regexpFound).1
  obtain ⟨first, second, contract, warm⟩ := source_terminal_then_warm_satisfies extraFirst extraSecond _ context name lower upper next _ emptyLiteralObject descriptor (depth + 1) handle constructor prototypeObject
    (initialized_inputs before context name lower upper next root descriptor depth handle constructor prototypeObject inputs) (by omega) (by omega)
  exact ⟨initialized, first, second, allocation, contract, warm⟩

end HonoLean.Upstream.PatternCacheTerminal
