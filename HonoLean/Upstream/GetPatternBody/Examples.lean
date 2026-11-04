import HonoLean.Upstream.GetPatternBody.Composition
import HonoLean.Upstream.PatternCache.Examples
import HonoLean.Upstream.PatternCacheTerminal.Examples

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternBody.Checks
open SourceSubset hiding pinnedSource
open ECMA2025

private def withLabel (before : LabelMatchState) (value : Value) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with environment := ("label", value) :: before.base.regexp.ambient.environment}

/-- The domain is inhabited for EVERY existing world and arbitrary context;
no allocation or intrinsic registry interpretation is needed by this branch. -/
theorem arbitrary_world_wildcard_domain (before : LabelMatchState) :
    WildcardInputs (withLabel before star) := rfl

theorem arbitrary_world_wildcard_exact_state (before : LabelMatchState) (context : PatternCacheContext) :
    sourceBody 5 context (withLabel before star) = some (.ok (star, withLabel before star)) ∧
    WildcardContract (withLabel before star) (withLabel before star) star :=
  source_wildcard_satisfies 0 context _ (arbitrary_world_wildcard_domain before)

theorem declaration_projection_wildcard_exact_state (before : LabelMatchState) (context : PatternCacheContext) :
    declarationBody 5 context (withLabel before star) = some (.ok (star, withLabel before star)) := by
  rw [declaration_body_source]
  exact (arbitrary_world_wildcard_exact_state before context).1

theorem arbitrary_nonstar_preserves_tail_errors_too (before : LabelMatchState) (context : PatternCacheContext) (value : Value)
    (different : value ≠ star) :
    sourceBody 257 context (withLabel before value) = PatternCache.sourceCall 256 context (withLabel before value) :=
  source_nonstar_cache 0 context _ value rfl different

/-- This world has zero allocated objects/arrays and deliberately invalid next,
cache and constructor values. The wildcard skips all of them. -/
private def unready : LabelMatchState :=
  {base := {regexp := {ambient := {environment := [("label",star),("next",.object 99),
    ("patternCache",.undefined),("RegExp",.number 17)]}}}}

theorem wildcard_needs_no_heap_next_cache_or_constructor :
    sourceBody 5 ⟨labelStandardContext⟩ unready = some (.ok (star, unready)) ∧
    unready.base.regexp.ambient.objects = [] ∧ unready.base.regexp.ambient.heap = [] := by
  exact ⟨(source_wildcard_satisfies 0 ⟨labelStandardContext⟩ unready rfl).1, rfl, rfl⟩

theorem star_is_not_the_complete_body_miss_case :
    (¬ ∃ name body, LabelRegExp.Label [42] name body) ∧
    sourceBody 5 ⟨labelStandardContext⟩ unready = some (.ok (.string [42], unready)) := by
  constructor
  · rintro ⟨name, body, valid⟩
    have input := LabelRegExp.label_input [42] name body valid
    cases input
  · exact (source_wildcard_satisfies 0 ⟨labelStandardContext⟩ unready rfl).1

/-- Reuse of the earlier inhabited initial domain supplies an actual witness
world; no match or completed cache result is a parameter of this theorem. -/
theorem arbitrary_plain_has_complete_body_witness (name : JSString) (next : Option JSString) (validName : LabelRegExp.Name name) :
    ∃ before context object,
      PatternCache.PlainInputs before context (58 :: name) name next 7 object none 2 ∧
      sourceBody 257 context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), PatternCache.plainState before context (58 :: name) name next 7 object)) ∧
      PatternCache.PlainContract before (PatternCache.plainState before context (58 :: name) name next 7 object) context (58 :: name) name next 7 object (.array (before.base.regexp.ambient.heap.length + 1)) := by
  have inputs := PatternCache.Checks.arbitrary_plain_domain_is_inhabited name next validName
  exact ⟨_, _, _, inputs, source_plain_satisfies 0 _ _ _ name next 7 _ none 2 inputs⟩

theorem arbitrary_warm_value_has_complete_body_witness (input name : JSString) (body : Option JSString) (next : Option JSString)
    (value : Value) (valid : LabelRegExp.Label input name body) (truthy : SourceSubset.truthy value = true) :
    ∃ before context object,
      PatternCache.WarmInputs before context input name body next 7 object value false false false 1 ∧
      sourceBody 257 context before = some (.ok (value, PatternCache.warmState before context input)) ∧
      PatternCache.WarmContract before (PatternCache.warmState before context input) context input name body 7 value value := by
  have inputs := PatternCache.Checks.arbitrary_warm_domain_is_inhabited input name body next value valid truthy
  exact ⟨_, _, _, inputs, source_warm_satisfies 0 _ _ input name body next 7 _ value false false false 1 inputs⟩

theorem arbitrary_terminal_has_complete_body_witness (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (lowerSafe : RangeRegExp.SafeEndpoint lower) (upperSafe : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (terminal : PatternCacheTerminal.TerminalNext next) :
    ∃ before context prototypeObject,
      PatternCacheTerminal.Inputs before context name lower upper next 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject ∧
      sourceBody 257 context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), PatternCacheTerminal.resultState before context name lower upper next 7 emptyLiteralObject 2)) ∧
      PatternCacheTerminal.Contract before (PatternCacheTerminal.resultState before context name lower upper next 7 emptyLiteralObject 2)
        context name lower upper next 7 emptyLiteralObject 2 (.array (before.base.regexp.ambient.heap.length + 1)) := by
  have inputs := PatternCacheTerminal.Checks.arbitrary_terminal_domain_is_inhabited name lower upper next validName lowerSafe upperSafe ordered terminal
  exact ⟨_, _, _, inputs, source_terminal_satisfies 0 _ _ name lower upper next 7 _ none 2 6 ⟨2⟩ _ inputs⟩

theorem arrow_metadata_and_real_body_are_retained :
    (parseExportedArrow pinnedDeclaration ambientBindings).map (fun arrow => (arrow.name, arrow.parameters.map (fun p => (p.name,p.optional)), arrow.innerSource)) =
      some ("getPattern", [("label",false),("next",true)], "\n" ++ pinnedLeadingComments ++ pinnedBody) ∧
    (parseExportedArrow pinnedDeclaration ambientBindings).map ExportedArrow.body = some program := by
  rw [parses_declaration]
  exact ⟨rfl, rfl⟩

theorem declaration_frontiers_and_comment_termination :
    (["export const f = (): Pattern | null => {//}",
      "export const f = (): Pattern | null => {//hello\u2028return '*'\nreturn null\n}",
      "export const f = (x?: string, y: string): Pattern | null => {return null}",
      "export const f = (x: string, x: string): Pattern | null => {return null}",
      "export const f = (x: string = '*'): Pattern | null => {return null}",
      "export const f = (): Pattern | null => {/*block*/return null}",
      "export const f = (): Pattern | null\n=> {return null}"] |>.all
      (fun text => (parseExportedArrow text ambientBindings).isNone)) = true ∧
    (parseExportedArrow "export const f = (): Pattern | null => {//ok\nreturn '*'\n}" ambientBindings).map ExportedArrow.body =
      some [.ret (.ordinary (.string [42]))] := by
  cbv <;> repeat' constructor

/-- Body validation still sees the actual body after its comment prefix and
rejects undeclared identifiers instead of manufacturing a canonical body. -/
theorem declaration_rejects_unbound_body_and_ambient_shadow :
    (parseExportedArrow "export const f = (): Pattern | null => {return hidden}" ambientBindings).isNone = true ∧
    (parseExportedArrow "export const f = (RegExp: string): Pattern | null => {return null}" ambientBindings).isNone = true := by
  cbv <;> repeat' constructor

/-- The earlier actual50 fixture is a derived witness, not a supplied future
world. Both executions below are the COMPLETE576B body on its carried state. -/
theorem arbitrary_terminal_initialization_and_reuse (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (lowerSafe : RangeRegExp.SafeEndpoint lower) (upperSafe : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (terminal : PatternCacheTerminal.TerminalNext next) :
    ∃ before context initialized after,
      PatternCache.sourceInit 2 context before = some (.ok initialized) ∧
      sourceBody 257 context initialized = some (.ok (.array 2, after)) ∧
      sourceBody 257 context after = some (.ok (.array 2, PatternCache.warmState after context (LabelMatch.safeRangeLabel name lower upper))) ∧
      PatternCache.InitContract before initialized ∧
      PatternCacheTerminal.Contract initialized after context name lower upper next 7 emptyLiteralObject 2 (.array 2) ∧
      PatternCache.WarmContract after (PatternCache.warmState after context (LabelMatch.safeRangeLabel name lower upper)) context
        (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) 7 (.array 2) (.array 2) := by
  have ready := PatternCacheTerminal.Checks.arbitrary_terminal_domain_is_inhabited name lower upper next validName lowerSafe upperSafe ordered terminal
  obtain ⟨initialized, first, second, allocation, constructed, warm⟩ :=
    PatternCacheTerminal.Checks.actual50_then_terminal_then_warm_same_heap name lower upper next validName lowerSafe upperSafe ordered terminal
  have nonstar := label_nonstar _ name _ ready.label
  have afterBinding := constructed.frames.environment
  have binding : _ := ready.source.labelBinding
  have finalBinding := congrArg (fun environment => environment.lookup "label") afterBinding
  rw [binding] at finalBinding
  refine ⟨_, _, _, _, initialized, ?_, ?_, allocation, constructed, warm⟩
  · rw [source_nonstar_cache 0 _ _ _ binding nonstar]
    exact first
  · rw [source_nonstar_cache 0 _ _ _ finalBinding nonstar]
    exact second

/-- info: 'HonoLean.Upstream.GetPatternBody.source_wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_wildcard_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.source_nonstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_nonstar
/-- info: 'HonoLean.Upstream.GetPatternBody.source_miss_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_miss_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.source_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_warm_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.source_plain_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_plain_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.source_terminal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_terminal_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.source_init_terminal_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_init_terminal_warm_satisfies
/-- info: 'HonoLean.Upstream.GetPatternBody.parses_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parses_declaration

end HonoLean.Upstream.GetPatternBody.Checks
