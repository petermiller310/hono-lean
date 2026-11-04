import HonoLean.Upstream.GetPatternBody.Correctness
import HonoLean.Upstream.PatternCacheTerminal.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternBody
open SourceSubset hiding pinnedSource
open ECMA2025

theorem label_nonstar (input name : JSString) (body : Option JSString) (valid : LabelRegExp.Label input name body) :
    Value.string input ≠ star := by
  cases body with
  | none => obtain ⟨_, rfl⟩ := valid; simp [star]
  | some body => obtain ⟨_, _, rfl⟩ := valid; simp [star]

theorem source_nonstar_cache (extra : Nat) (context : PatternCacheContext) (before : LabelMatchState) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup "label" = some value) (different : value ≠ star) :
    sourceBody (extra + 257) context before = PatternCache.sourceCall (extra + 256) context before := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using source_nonstar (extra + 252) context before value binding different

/-- Unlike the earlier post-wildcard miss, this complete-body contract must
exclude the literal star. A star has no Label match but returns star early. -/
theorem source_miss_satisfies (extra : Nat) (context : PatternCacheContext) (before : LabelMatchState) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) (different : input ≠ [42])
    (absent : ¬ ∃ name body, LabelRegExp.Label input name body) :
    sourceBody (extra + 257) context before = some (.ok (.null, PatternCache.warmState before context input)) ∧
    PatternCache.MissContract before (PatternCache.warmState before context input) context input .null := by
  have notStar : Value.string input ≠ star := by simpa [star] using different
  rw [source_nonstar_cache extra context before (.string input) inputs.labelBinding notStar]
  exact PatternCache.source_miss_satisfies extra before context input inputs absent

theorem source_warm_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : PatternCache.WarmInputs before context input name body next cache object value writable enumerable configurable depth) :
    sourceBody (extra + 257) context before = some (.ok (value, PatternCache.warmState before context input)) ∧
    PatternCache.WarmContract before (PatternCache.warmState before context input) context input name body cache value value := by
  rw [source_nonstar_cache extra context before (.string input) inputs.source.labelBinding (label_nonstar input name body inputs.label)]
  exact PatternCache.source_warm_satisfies extra before context input name body next cache object value writable enumerable configurable depth inputs

theorem source_plain_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PatternCache.PlainInputs before context input name next cache object descriptor depth) :
    sourceBody (extra + 257) context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), PatternCache.plainState before context input name next cache object)) ∧
    PatternCache.PlainContract before (PatternCache.plainState before context input name next cache object) context input name next cache object
      (.array (before.base.regexp.ambient.heap.length + 1)) := by
  rw [source_nonstar_cache extra context before (.string input) inputs.source.labelBinding (label_nonstar input name none inputs.label)]
  exact PatternCache.source_plain_satisfies extra before context input name next cache object descriptor depth inputs

theorem source_terminal_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : PatternCacheTerminal.Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    sourceBody (extra + 257) context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1),
      PatternCacheTerminal.resultState before context name lower upper next cache object constructor.prototype)) ∧
    PatternCacheTerminal.Contract before (PatternCacheTerminal.resultState before context name lower upper next cache object constructor.prototype)
      context name lower upper next cache object constructor.prototype (.array (before.base.regexp.ambient.heap.length + 1)) := by
  rw [source_nonstar_cache extra context before _ inputs.source.labelBinding (label_nonstar _ name _ inputs.label)]
  exact PatternCacheTerminal.source_terminal_satisfies extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs

/-- Actual source50 once, then TWO complete576B body activations carrying the
same state/cache. This remains an explicit activation handoff, not a function
object/lexical-closure/module-instantiation theorem. -/
theorem source_init_terminal_warm_satisfies (extraInit extraFirst extraSecond : Nat)
    (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (root : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : PatternCacheTerminal.InitInputs before context name lower upper next root descriptor depth handle constructor prototypeObject) :
    let initialized := initializedPatternCacheState PatternCache.initProgram before
    let after := PatternCacheTerminal.resultState initialized context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype
    PatternCache.sourceInit (extraInit + 2) context before = some (.ok initialized) ∧
    sourceBody (extraFirst + 257) context initialized = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), after)) ∧
    sourceBody (extraSecond + 257) context after = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), PatternCache.warmState after context (LabelMatch.safeRangeLabel name lower upper))) ∧
    PatternCache.InitContract before initialized ∧
    PatternCacheTerminal.Contract initialized after context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype (.array (before.base.regexp.ambient.heap.length + 1)) ∧
    PatternCache.WarmContract after (PatternCache.warmState after context (LabelMatch.safeRangeLabel name lower upper)) context (LabelMatch.safeRangeLabel name lower upper) name
      (some (PatternConstruct.rawBody lower upper)) before.base.regexp.ambient.objects.length (.array (before.base.regexp.ambient.heap.length + 1)) (.array (before.base.regexp.ambient.heap.length + 1)) := by
  dsimp only
  let initialized := initializedPatternCacheState PatternCache.initProgram before
  let after := PatternCacheTerminal.resultState initialized context name lower upper next before.base.regexp.ambient.objects.length emptyLiteralObject constructor.prototype
  have initialReady := PatternCacheTerminal.initialized_inputs before context name lower upper next root descriptor depth handle constructor prototypeObject inputs
  have contract := PatternCacheTerminal.terminal_contract initialized context name lower upper next _ emptyLiteralObject descriptor (depth + 1) handle constructor prototypeObject initialReady
  have nonstar := label_nonstar _ name _ initialReady.label
  have first := source_nonstar_cache extraFirst context initialized _ initialReady.source.labelBinding nonstar
  have secondBinding : after.base.regexp.ambient.environment.lookup "label" = some (.string (LabelMatch.safeRangeLabel name lower upper)) := by
    rw [contract.frames.environment]
    exact initialReady.source.labelBinding
  rw [first, source_nonstar_cache extraSecond context after _ secondBinding nonstar]
  exact PatternCacheTerminal.source_init_then_terminal_then_warm_satisfies extraInit extraFirst extraSecond before context name lower upper next root descriptor depth handle constructor prototypeObject inputs

end HonoLean.Upstream.GetPatternBody
