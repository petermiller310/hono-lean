import HonoLean.Upstream.GetPatternBody.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternBody
open SourceSubset hiding pinnedSource
open ECMA2025

theorem eval_guard (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup "label" = some value) :
    evalPatternCacheExpr (extra + 4) limit context guardExpr before = .ok (.boolean (decide (value = star)), before) := by
  simp [guardExpr, PatternCache.labelExpr, evalPatternCacheExpr, evalExpression, lookupVariable,
    binding, star, cacheWithAmbient, bind, Except.bind, pure, Except.pure, Except.map, Except.mapError]
  rfl

/-- Initial equality alone chooses the actual early return. The body after the
guard remains in the AST but is never evaluated. -/
theorem execute_wildcard (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState)
    (inputs : WildcardInputs before) :
    executePatternCache (extra + 5) limit context program before = .ok (.returned star before) := by
  have condition := eval_guard extra limit context before star inputs
  simp only [decide_true, star] at condition
  unfold program guardProgram
  rw [List.cons_append, List.nil_append, executePatternCache, condition]
  simp [executePatternCache, evalPatternCacheExpr, evalExpression, star,
    cacheRestoreEnvironment, cacheWithAmbient, truthy, bind, Except.bind, pure, Except.pure, Except.map, Except.mapError]

/-- Generic nonstar delegation retains every possible tail result, including
errors; no successful tail evaluation is an entry premise. -/
theorem execute_nonstar (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup "label" = some value) (different : value ≠ star) :
    executePatternCache (extra + 5) limit context program before =
      executePatternCache (extra + 4) limit context PatternCache.program before := by
  have condition := eval_guard extra limit context before value binding
  rw [show decide (value = star) = false from decide_eq_false different] at condition
  unfold program guardProgram
  rw [List.cons_append, List.nil_append, executePatternCache, condition]
  simp [truthy, executePatternCache, cacheRestoreEnvironment, cacheWithAmbient, bind, Except.bind]

theorem run_nonstar (extra limit : Nat) (context : PatternCacheContext) (before : LabelMatchState) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup "label" = some value) (different : value ≠ star) :
    runPatternCache (extra + 5) limit context program before =
      runPatternCache (extra + 4) limit context PatternCache.program before := by
  unfold runPatternCache
  rw [execute_nonstar extra limit context before value binding different]

theorem source_wildcard_satisfies (extra : Nat) (context : PatternCacheContext) (before : LabelMatchState)
    (inputs : WildcardInputs before) :
    sourceBody (extra + 5) context before = some (.ok (star, before)) ∧ WildcardContract before before star := by
  constructor
  · rw [sourceBody, parses_body]
    dsimp only [Option.map]
    rw [runPatternCache_restores_caller _ _ _ _ _ _ _ (execute_wildcard extra defaultSplitLimit context before inputs)]
    rfl
  · exact ⟨rfl, rfl⟩

theorem source_nonstar (extra : Nat) (context : PatternCacheContext) (before : LabelMatchState) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup "label" = some value) (different : value ≠ star) :
    sourceBody (extra + 5) context before = PatternCache.sourceCall (extra + 4) context before := by
  rw [sourceBody, parses_body, PatternCache.sourceCall, PatternCache.parses_source]
  dsimp only [Option.map]
  rw [run_nonstar extra defaultSplitLimit context before value binding different]

end HonoLean.Upstream.GetPatternBody
