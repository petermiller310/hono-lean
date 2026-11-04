import HonoLean.Upstream.ECMA2025.LiteralLookahead.Parser

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

inductive LiteralInstruction where
  | consumeUnit (unit : UInt16)
  | accept
  deriving Repr, DecidableEq

inductive Instruction where
  | assertStart
  | consumeRange (lower upper : UInt16)
  | repeatRange (lower upper : UInt16)
  | consumeUnit (unit : UInt16)
  | positive (child : List LiteralInstruction)
  | accept
  deriving Repr, DecidableEq

/-- The admitted positive assertion has literal-only child code. Other child
syntax is rejected rather than silently assigned literal semantics. -/
def compileAssertion : Syntax → Option (List LiteralInstruction)
  | .empty => some []
  | .atom (.literal unit) => some [.consumeUnit unit]
  | .sequence left right => do return (← compileAssertion left) ++ (← compileAssertion right)
  | _ => none

/-- Positive assertions compile a genuine child program ending in accept. -/
def compileFragment : Syntax → Option (List Instruction)
  | .empty => some []
  | .start => some [.assertStart]
  | .atom (.range lower upper) => some [.consumeRange lower upper]
  | .atom (.literal unit) => some [.consumeUnit unit]
  | .plus (.range lower upper) => some [.consumeRange lower upper, .repeatRange lower upper]
  | .plus (.literal _) => none
  | .sequence left right => do return (← compileFragment left) ++ (← compileFragment right)
  | .positive child => (compileAssertion child).map (fun code => [.positive (code ++ [.accept])])

def compile (ast : Syntax) : Option (List Instruction) :=
  (compileFragment ast).map (· ++ [.accept])

def literalCode (text : JSString) : List LiteralInstruction := text.map .consumeUnit

def code (lower upper : UInt16) (next : JSString) : List Instruction :=
  [.assertStart, .consumeRange lower upper, .repeatRange lower upper,
    .positive (literalCode (47 :: next) ++ [.accept]), .accept]

theorem compile_literal (text : JSString) : compileAssertion (literalSyntax text) = some (literalCode text) := by
  induction text with
  | nil => rfl
  | cons unit rest ih => simp [literalSyntax, compileAssertion, ih, literalCode, bind, Option.bind]

theorem compile_pattern (lower upper : UInt16) (next : JSString) :
    compile (pattern lower upper next) = some (code lower upper next) := by
  simp [compile, pattern, compileFragment, compile_literal, code, bind, Option.bind]

end HonoLean.Upstream.ECMA2025.LiteralLookahead
