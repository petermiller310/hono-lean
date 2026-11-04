import HonoLean.Upstream.NodePatternBinding.Generated
import HonoLean.Upstream.SourceSubset.ArrayBindingRules

set_option autoImplicit false
namespace HonoLean.Upstream.NodePatternBinding
open SourceSubset ECMA2025

def bindings : List String := ["pattern"]
def program : ArrayBindingDecl := ⟨[.elision, .binding "name", .binding "matcher"], .variable "pattern"⟩

theorem parses_source : parseArrayBinding pinnedSource bindings = some program := by cbv

/-- Exact declaration only, in a fresh selected activation. The initializer is
not an assumed private child.#pattern read or cache lookup. -/
def sourceBinding (fuel : Nat) (context : ArrayIteratorContext) (before : ArrayBindingState) :
    Option (Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState)) :=
  (parseArrayBinding pinnedSource bindings).map (fun declaration =>
    runArrayBinding fuel defaultSplitLimit context declaration before)

end HonoLean.Upstream.NodePatternBinding
