import HonoLean.Upstream.SourceSubset.Syntax

namespace HonoLean.Upstream.SourceSubset

/-- Values of the deliberately small source semantics. Heap addresses are
abstract identities, not JavaScript Number values. The constructor tag denotes
the standard realm builtin only, never an arbitrary object named `Object`. -/
inductive Value where
  | string (contents : JSString)
  | number (value : Int)
  | boolean (value : Bool)
  | array (reference : Nat)
  | undefined
  | null
  | object (reference : Nat)
  | objectConstructor
  | function (reference : Nat)
  | set (reference : Nat)
  | setConstructor
  deriving Repr, DecidableEq

end HonoLean.Upstream.SourceSubset
