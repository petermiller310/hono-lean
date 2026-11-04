import HonoLean.Upstream.PatternCacheTerminal.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.PatternCacheTerminal
open SourceSubset ECMA2025 PatternCache

/-- An explicit caller activation changes only lexical bindings. This helper
is used for the separate cache/tuple alias and constructor-replacement witness;
it does not move a call across source statements or reset any heap component. -/
def callerEnvironment (before : LabelMatchState) (environment : List (String × Value)) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with environment}

theorem realm_caller_environment (before : LabelMatchState) (context : LabelMatchContext)
    (environment : List (String × Value)) (realm : LabelRealm before context) :
    LabelRealm (callerEnvironment before environment) context := by
  cases realm
  constructor <;> assumption

theorem inputs_caller_environment (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject)
    (environment : List (String × Value))
    (labelBinding : environment.lookup "label" = some (.string (LabelMatch.safeRangeLabel name lower upper)))
    (nextBinding : environment.lookup "next" = some (nextValue next))
    (cacheBinding : environment.lookup "patternCache" = some (.object cache))
    (constructorBinding : environment.lookup "RegExp" = some (.function handle)) :
    Inputs (callerEnvironment before environment) context name lower upper next cache object descriptor depth handle constructor prototypeObject := by
  refine ⟨⟨⟨realm_caller_environment before context.label environment inputs.source.toLabelRealm, labelBinding⟩,
    inputs.label, nextBinding, cacheBinding, inputs.cacheFound, inputs.path, inputs.pathBound⟩,
    inputs.terminal, inputs.validName, inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.falsy,
    inputs.writable, constructorBinding, inputs.handleBound, inputs.identity, inputs.prototypeFound⟩

theorem warm_caller_environment (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context input name body next cache object value writable enumerable configurable depth)
    (environment : List (String × Value))
    (labelBinding : environment.lookup "label" = some (.string input))
    (nextBinding : environment.lookup "next" = some (nextValue next))
    (cacheBinding : environment.lookup "patternCache" = some (.object cache)) :
    WarmInputs (callerEnvironment before environment) context input name body next cache object value writable enumerable configurable depth := by
  exact ⟨⟨⟨realm_caller_environment before context.label environment inputs.source.toLabelRealm, labelBinding⟩,
    inputs.label, nextBinding, cacheBinding, inputs.cacheFound, inputs.path, inputs.pathBound⟩, inputs.truthy⟩

/-- A compact structural endpoint for a proved source60 hit. Its heap values
come from the independent Label language; the equality below discharges the
actual VM/capture extraction before subsequent source execution is reduced. -/
def matchedSnapshot (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString) : LabelMatchState :=
  let fresh := labelFreshState before context.label labelLiteralRecord
    (before.trace ++ LabelMatch.sourceEvents before context.label input)
  {fresh with
    base := {fresh.base with regexp := {fresh.base.regexp with ambient := {fresh.base.regexp.ambient with
      environment := ("match", .array before.base.regexp.ambient.heap.length) :: before.base.regexp.ambient.environment
      heap := before.base.regexp.ambient.heap ++ [LabelMatch.captures input name body]}}}
    results := (before.base.regexp.ambient.heap.length, ⟨0, input⟩) :: before.results}

theorem matched_snapshot (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (valid : LabelRegExp.Label input name body) : matchedState before context input = matchedSnapshot before context input name body := by
  have hit := LabelRegExp.execute_label_hit input name body valid
  have values := LabelMatch.match_values input name body valid
  have start := (LabelRegExp.label_capture_bounds input name body valid).1
  simp only [matchedState, LabelMatch.resultState, labelEngineValue, labelEngineState, hit, values, start, matchedSnapshot]

end HonoLean.Upstream.PatternCacheTerminal
