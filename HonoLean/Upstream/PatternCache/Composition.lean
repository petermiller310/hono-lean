import HonoLean.Upstream.PatternCache.Correctness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.PatternCache
open SourceSubset ECMA2025

/-- Actual50 creates an ordinary Object.prototype-linked cache. Empty own keys
are not a promise that inherited lookup is absent. All prior runtime components
remain, including the complete existing array/regexp/iterator metadata. -/
structure InitContract (before after : LabelMatchState) : Prop where
  environment : after.base.regexp.ambient.environment = ("patternCache", .object before.base.regexp.ambient.objects.length) :: before.base.regexp.ambient.environment
  objects : after.base.regexp.ambient.objects = before.base.regexp.ambient.objects ++ [emptyLiteralObject]
  fresh : after.base.regexp.ambient.objects[before.base.regexp.ambient.objects.length]? = some emptyLiteralObject
  ownEmpty : emptyLiteralObject.own = []
  prototype : emptyLiteralObject.prototype = some ordinaryObjectPrototype
  extensible : emptyLiteralObject.extensible = true
  oldObjects : ∀ reference, reference < before.base.regexp.ambient.objects.length → after.base.regexp.ambient.objects[reference]? = before.base.regexp.ambient.objects[reference]?
  arrays : after.base.regexp.ambient.heap = before.base.regexp.ambient.heap
  functions : after.base.regexp.ambient.functions = before.base.regexp.ambient.functions
  privates : after.base.regexp.ambient.privates = before.base.regexp.ambient.privates
  thisValue : after.base.regexp.ambient.thisValue = before.base.regexp.ambient.thisValue
  sets : after.base.regexp.ambient.sets = before.base.regexp.ambient.sets
  rangeBrands : after.base.regexp.brands = before.base.regexp.brands
  rangeResults : after.base.regexp.results = before.base.regexp.results
  iteratorSymbols : after.base.symbols = before.base.symbols
  iterators : after.base.iterators = before.base.iterators
  iteratorTrace : after.base.trace = before.base.trace
  labelBrands : after.brands = before.brands
  labelResults : after.results = before.results
  symbols : after.symbols = before.symbols
  accessors : after.accessors = before.accessors
  trace : after.trace = before.trace

theorem init_contract (before : LabelMatchState) : InitContract before (initializedPatternCacheState initProgram before) := by
  constructor
  case fresh => simp [initializedPatternCacheState, cacheWithAmbient]
  case oldObjects => intro reference bound; exact List.getElem?_append_left bound
  all_goals rfl

theorem source_init_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (root : OrdinaryObject)
    (rootFound : before.base.regexp.ambient.objects[ordinaryObjectPrototype]? = some root) :
    sourceInit (extra + 2) context before = some (.ok (initializedPatternCacheState initProgram before)) ∧
    InitContract before (initializedPatternCacheState initProgram before) := by
  constructor
  · rw [sourceInit, parses_init]
    dsimp only [Option.map]
    rw [initializePatternCache_empty extra defaultSplitLimit context initProgram before root rfl rootFound]
  · exact init_contract before

theorem initialized_realm (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context) :
    LabelRealm (initializedPatternCacheState initProgram before) context := by
  constructor
  case stringFound =>
    obtain ⟨object, found, own⟩ := realm.stringFound
    exact ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case regexpFound =>
    obtain ⟨object, found, own⟩ := realm.regexpFound
    exact ⟨object, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found, own⟩
  case symbolOwners =>
    intro entry member
    have bound := realm.symbolOwners entry member
    change entry.1 < (before.base.regexp.ambient.objects ++ [emptyLiteralObject]).length
    simp only [List.length_append, List.length_singleton]
    omega
  all_goals cases realm <;> assumption

theorem initialized_label_inputs (before : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) :
    LabelMatch.Inputs (initializedPatternCacheState initProgram before) context.label input := by
  refine ⟨initialized_realm before context.label inputs.toLabelRealm, ?_⟩
  change List.lookup "label" (("patternCache", _) :: before.base.regexp.ambient.environment) = _
  simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.labelBinding

/-- An actual BEFORE root path controls inherited lookup after fresh{}. This is
why empty own storage alone never implies a cold/missing cache lookup. -/
theorem initialized_path (before : LabelMatchState) (property : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (path : NodeCaptureGuard.DescriptorPath before.base.regexp.ambient.objects property ordinaryObjectPrototype descriptor depth) :
    NodeCaptureGuard.DescriptorPath (initializedPatternCacheState initProgram before).base.regexp.ambient.objects property
      before.base.regexp.ambient.objects.length descriptor (depth + 1) := by
  have rootPath := NodeCaptureGuard.descriptor_path_append before.base.regexp.ambient.objects [emptyLiteralObject] property ordinaryObjectPrototype descriptor depth path
  have fresh : (initializedPatternCacheState initProgram before).base.regexp.ambient.objects[before.base.regexp.ambient.objects.length]? = some emptyLiteralObject := by
    simp [initializedPatternCacheState, cacheWithAmbient]
  exact .parent fresh rfl rfl rootPath

structure InitPlainInputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop where
  source : LabelMatch.Inputs before context.label input
  label : LabelRegExp.Label input name none
  nextBinding : before.base.regexp.ambient.environment.lookup "next" = some (nextValue next)
  rootFound : before.base.regexp.ambient.objects[ordinaryObjectPrototype]? = some root
  rootPath : NodeCaptureGuard.DescriptorPath before.base.regexp.ambient.objects (key input next) ordinaryObjectPrototype descriptor depth
  pathBound : depth + 1 ≤ propertyFuel
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  dataWritable : descriptor = none ∨ ∃ value enumerable configurable, descriptor = some (.data value true enumerable configurable)

theorem initialized_plain_inputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : InitPlainInputs before context input name next root descriptor depth) :
    PlainInputs (initializedPatternCacheState initProgram before) context input name next before.base.regexp.ambient.objects.length emptyLiteralObject descriptor (depth + 1) := by
  refine ⟨⟨initialized_label_inputs before context input inputs.source, inputs.label, ?_, rfl, ?_,
    initialized_path before (key input next) descriptor depth inputs.rootPath, inputs.pathBound⟩,
    inputs.falsy, inputs.dataWritable, Or.inl ⟨rfl, rfl⟩⟩
  · change List.lookup "next" (("patternCache", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  · simp [initializedPatternCacheState, cacheWithAmbient]

/-- Actual typed52B initialization followed by full533B call, on the same heap
and SAME freshly allocated cache pointer. Closure creation/module activation is
an explicit handoff; no cache reset, staged capture or future lookup is used. -/
theorem source_init_then_plain_satisfies (extraInit extraCall : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (input name : JSString) (next : Option JSString) (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : InitPlainInputs before context input name next root descriptor depth) :
    sourceInit (extraInit + 2) context before = some (.ok (initializedPatternCacheState initProgram before)) ∧
    sourceCall (extraCall + 256) context (initializedPatternCacheState initProgram before) =
      some (.ok (.array (before.base.regexp.ambient.heap.length + 1),
        plainState (initializedPatternCacheState initProgram before) context input name next before.base.regexp.ambient.objects.length emptyLiteralObject)) ∧
    InitContract before (initializedPatternCacheState initProgram before) ∧
    PlainContract (initializedPatternCacheState initProgram before)
      (plainState (initializedPatternCacheState initProgram before) context input name next before.base.regexp.ambient.objects.length emptyLiteralObject)
      context input name next before.base.regexp.ambient.objects.length emptyLiteralObject (.array (before.base.regexp.ambient.heap.length + 1)) := by
  obtain ⟨initialized, allocation⟩ := source_init_satisfies extraInit before context root inputs.rootFound
  obtain ⟨called, contract⟩ := source_plain_satisfies extraCall (initializedPatternCacheState initProgram before) context input name next
    before.base.regexp.ambient.objects.length emptyLiteralObject descriptor (depth + 1)
    (initialized_plain_inputs before context input name next root descriptor depth inputs)
  exact ⟨initialized, called, allocation, contract⟩

end HonoLean.Upstream.PatternCache
