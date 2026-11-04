import HonoLean.Upstream.GetPatternBody.Source

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternBody
open SourceSubset hiding pinnedSource
open ECMA2025

/-- Literal-star readiness needs just this one current variable binding. No
allocated object, label matching realm, next/cache or constructor fact. -/
def WildcardInputs (before : LabelMatchState) : Prop :=
  before.base.regexp.ambient.environment.lookup "label" = some star

/-- Independent wildcard value and ENTIRE state frame. In particular there is
no literal/capture/tuple allocation or call/getter/iterator metadata change. -/
structure WildcardContract (before after : LabelMatchState) (returned : Value) : Prop where
  value : returned = star
  state : after = before

end HonoLean.Upstream.GetPatternBody
