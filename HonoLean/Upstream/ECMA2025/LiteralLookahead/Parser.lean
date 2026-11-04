import HonoLean.Upstream.ECMA2025.LiteralLookahead.Syntax

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

/-- The closing parenthesis is admitted only as the final unit; next units
are independently checked ASCII alphanumerics. Empty next is rejected by parse. -/
def parseNext : JSString → Option JSString
  | [] => none
  | [unit] => if unit == 41 then some [] else none
  | unit :: rest =>
    if RangeRegExp.SafeEndpoint unit then (parseNext rest).map (unit :: ·) else none

def parse : JSString → Option Syntax
  | caret :: opening :: lower :: dash :: upper :: close :: plus :: left :: question :: equal :: slash :: rest => do
    if caret = 94 ∧ opening = 91 ∧ dash = 45 ∧ close = 93 ∧ plus = 43 ∧
        left = 40 ∧ question = 63 ∧ equal = 61 ∧ slash = 47 ∧
        RangeRegExp.SafeEndpoint lower ∧ RangeRegExp.SafeEndpoint upper ∧ lower.toNat ≤ upper.toNat then
      let next ← parseNext rest
      if next.isEmpty then none else some (pattern lower upper next)
    else none
  | _ => none

theorem parseNext_iff (text next : JSString) : parseNext text = some next ↔
    text = next ++ [41] ∧ ∀ unit ∈ next, RangeRegExp.SafeEndpoint unit := by
  induction text generalizing next with
  | nil => simp [parseNext]
  | cons unit rest ih =>
    cases rest with
    | nil =>
      cases next with
      | nil => simp [parseNext, beq_iff_eq]
      | cons first tail =>
        constructor
        · intro parsed
          simp [parseNext] at parsed
        · intro relation
          have lengths := congrArg List.length relation.1
          simp at lengths
    | cons second tail =>
      cases next with
      | nil => simp [parseNext]
      | cons first remaining =>
        constructor
        · intro parsed
          by_cases safe : RangeRegExp.SafeEndpoint unit
          · cases restResult : parseNext (second :: tail) with
            | none => simp [parseNext, safe, restResult] at parsed
            | some restValue =>
              simp [parseNext, safe, restResult] at parsed
              obtain ⟨rfl, rfl⟩ := parsed
              obtain ⟨shape, all⟩ := (ih restValue).mp restResult
              exact ⟨by simp [shape], by simpa using And.intro safe all⟩
          · simp [parseNext, safe] at parsed
        · intro relation
          have heads : unit = first ∧ second :: tail = remaining ++ [41] := List.cons.inj relation.1
          obtain ⟨rfl, shape⟩ := heads
          have safe : RangeRegExp.SafeEndpoint unit := relation.2 unit (by simp)
          have all : ∀ value ∈ remaining, RangeRegExp.SafeEndpoint value :=
            fun value member => relation.2 value (by simp [member])
          simp [parseNext, safe, (ih remaining).mpr ⟨shape, all⟩]

theorem parse_sound (text : JSString) (ast : Syntax) (parsed : parse text = some ast) : Grammar text ast := by
  unfold parse at parsed
  split at parsed
  · split at parsed
    · rename_i original caret opening lower dash upper close plus left question equal slash rest valid
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, safeLower, safeUpper, ordered⟩ := valid
      cases nextResult : parseNext rest with
      | none => simp [nextResult] at parsed
      | some next =>
        simp only [nextResult, bind, Option.bind] at parsed
        split at parsed
        · cases parsed
        · rename_i nonempty
          obtain ⟨rfl, safeNext⟩ := (parseNext_iff rest next).mp nextResult
          cases Option.some.inj parsed
          exact .lookahead lower upper next safeLower safeUpper ordered ⟨by simpa using nonempty, safeNext⟩
    · cases parsed
  · cases parsed

theorem parse_complete (text : JSString) (ast : Syntax) (grammar : Grammar text ast) : parse text = some ast := by
  cases grammar with
  | lookahead lower upper next safeLower safeUpper ordered safeNext =>
    have parsedNext : parseNext (next ++ [41]) = some next := (parseNext_iff _ _).mpr ⟨rfl, safeNext.2⟩
    simp [rawSource, parse, safeLower, safeUpper, ordered, parsedNext, safeNext.1]

theorem parse_iff (text : JSString) (ast : Syntax) : parse text = some ast ↔ Grammar text ast :=
  ⟨parse_sound text ast, parse_complete text ast⟩

end HonoLean.Upstream.ECMA2025.LiteralLookahead
