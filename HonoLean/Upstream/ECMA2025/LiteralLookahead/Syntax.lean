import HonoLean.Upstream.ECMA2025.RangeRegExp

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

abbrev Match := RangeRegExp.Match
abbrev Outcome := RangeRegExp.Outcome

/-- The initial literal-next domain: nonempty ASCII letters/digits, with no
regex syntax, escapes, flags or URL-decoding interpretation. -/
def SafeNext (next : JSString) : Prop :=
  next ≠ [] ∧ ∀ unit ∈ next, RangeRegExp.SafeEndpoint unit
instance (next : JSString) : Decidable (SafeNext next) :=
  inferInstanceAs (Decidable (_ ∧ ∀ unit ∈ next, RangeRegExp.SafeEndpoint unit))

inductive Atom where
  | range (lower upper : UInt16)
  | literal (unit : UInt16)
  deriving Repr, DecidableEq

inductive Syntax where
  | empty | start
  | atom (value : Atom)
  | plus (value : Atom)
  | sequence (left right : Syntax)
  | positive (child : Syntax)
  deriving Repr, DecidableEq

def literalSyntax : JSString → Syntax
  | [] => .empty
  | unit :: rest => .sequence (.atom (.literal unit)) (literalSyntax rest)

def pattern (lower upper : UInt16) (next : JSString) : Syntax :=
  .sequence .start (.sequence (.plus (.range lower upper)) (.positive (literalSyntax (47 :: next))))

/-- Constructor input has a RAW slash. It is not a /delimited/ regex literal. -/
def rawSource (lower upper : UInt16) (next : JSString) : JSString :=
  [94, 91, lower, 45, upper, 93, 43, 40, 63, 61, 47] ++ next ++ [41]

/-- Separate expected source-display encoding for this admitted ASCII domain.
The native source getter and general EscapeRegExpPattern remain external. -/
def displaySource (lower upper : UInt16) (next : JSString) : JSString :=
  [94, 91, lower, 45, upper, 93, 43, 40, 63, 61, 92, 47] ++ next ++ [41]

def escapeSlashes (source : JSString) : JSString :=
  source.flatMap (fun unit => if unit == 47 then [92, 47] else [unit])

/-- Independent grammar: no parser/compiler/executor invocation. -/
inductive Grammar : JSString → Syntax → Prop where
  | lookahead (lower upper : UInt16) (next : JSString)
      (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
      (ordered : lower.toNat ≤ upper.toNat) (safeNext : SafeNext next) :
      Grammar (rawSource lower upper next) (pattern lower upper next)

/-- Independent language with an arbitrary suffix: the assertion introduces
neither an ending anchor nor a boundary after the literal next string. -/
def Accepted (lower upper : UInt16) (next input : JSString) : Prop :=
  ∃ taken suffix, input = taken ++ (47 :: next ++ suffix) ∧
    taken ≠ [] ∧ ∀ unit ∈ taken, RangeRegExp.InRange lower upper unit

/-- The asserted slash/next contributes no consumed characters. -/
def Matches (lower upper : UInt16) (next input : JSString) (result : Match) : Prop :=
  ∃ taken suffix, input = taken ++ (47 :: next ++ suffix) ∧
    taken ≠ [] ∧ (∀ unit ∈ taken, RangeRegExp.InRange lower upper unit) ∧
    result = ⟨0, taken.length, []⟩

end HonoLean.Upstream.ECMA2025.LiteralLookahead
