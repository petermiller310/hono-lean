import HonoLean.Upstream.LexicalArrow.ExpressionCore
import HonoLean.Upstream.LexicalArrow.HostFrame

set_option autoImplicit false
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset

/-- The generic structural simulation is instantiated with the proved actual
closed constructor and label-operation frame laws. No future preservation law
or successful body execution is supplied by an invocation caller. -/
theorem expression_refines (fuel profileFuel limit : Nat) (context : PatternCacheContext)
    (expression : PatternCacheExpr) (before : Runtime) (value : Value) (data : LabelMatchState)
    (profile : expressionProfile profileFuel expression = true)
    (agreement : ReadsAgree before (expressionReads profileFuel expression))
    (old : evalPatternCacheExpr fuel limit context expression before.data = .ok (value, data)) :
    evalExpr fuel limit context expression before = .ok (value, withData before data) ∧
      data.base.regexp.ambient.environment = before.data.base.regexp.ambient.environment :=
  Core.expression_refines invokeRegExpConstructor_environment runResolvedLabelMatch_environment
    fuel profileFuel limit context expression before value data profile agreement old

end HonoLean.Upstream.LexicalArrow
