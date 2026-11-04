import HonoLean.Upstream.SourceSubset.Syntax

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LabelRegExp
open SourceSubset

inductive Atom where
  | literal (unit : UInt16)
  | excluded (units : JSString)
  | dot
  deriving Repr, DecidableEq
inductive Syntax where
  | atom (value : Atom)
  | start | finish
  | sequence (elements : List Syntax)
  | plus (atom : Atom)
  | optional (body : Syntax)
  | capture (index : Nat) (body : Syntax)
  | group (body : Syntax)
  deriving Repr

private def escaped : JSString → Option (UInt16 × JSString)
  | 92 :: unit :: rest =>
    if [58, 64, 123, 125, 47, 92, 46, 91, 93, 40, 41, 43, 63, 94, 36].contains unit then some (unit, rest) else none
  | _ => none

private def classUnits : Nat → JSString → Option (JSString × JSString)
  | 0, _ => none
  | _ + 1, 93 :: rest => some ([], rest)
  | fuel + 1, 92 :: unit :: rest => do
    let (value, rest) ← escaped (92 :: unit :: rest)
    let (tail, rest) ← classUnits fuel rest
    some (value :: tail, rest)
  | fuel + 1, unit :: rest => do
    if [91, 45, 10, 13, 8232, 8233].contains unit then none else
    let (tail, rest) ← classUnits fuel rest
    some (unit :: tail, rest)
  | _, [] => none

mutual
  private def parseSequence : Nat → Nat → JSString → Option (List Syntax × Nat × JSString)
    | 0, _, _ => none
    | fuel + 1, captures, units => do
      match units with
      | [] | 41 :: _ | 47 :: _ => some ([], captures, units)
      | _ =>
        let (head, captures, rest) ← parseTerm fuel captures units
        let (tail, captures, rest) ← parseSequence fuel captures rest
        some (head :: tail, captures, rest)

  private def parseTerm : Nat → Nat → JSString → Option (Syntax × Nat × JSString)
    | 0, _, _ => none
    | fuel + 1, captures, units => do
      let (ast, captures, rest) ← match units with
        | 94 :: rest => some (.start, captures, rest)
        | 36 :: rest => some (.finish, captures, rest)
        | 46 :: rest => some (.atom .dot, captures, rest)
        | 91 :: 94 :: rest => do
          let (excluded, rest) ← classUnits (rest.length + 1) rest
          if excluded.isEmpty then none else some (.atom (.excluded excluded), captures, rest)
        | 40 :: 63 :: 58 :: rest => do
          let (body, captures, rest) ← parseSequence fuel captures rest
          let rest ← match rest with | 41 :: rest => some rest | _ => none
          some (.group (.sequence body), captures, rest)
        | 40 :: rest => do
          let (body, capturesAfter, rest) ← parseSequence fuel (captures + 1) rest
          let rest ← match rest with | 41 :: rest => some rest | _ => none
          some (.capture captures (.sequence body), capturesAfter, rest)
        | 92 :: unit :: rest => do
          let (unit, rest) ← escaped (92 :: unit :: rest)
          some (.atom (.literal unit), captures, rest)
        | unit :: rest =>
          if [91, 93, 41, 43, 63, 42, 123, 125, 124, 47, 10, 13, 8232, 8233].contains unit then none
          else some (.atom (.literal unit), captures, rest)
        | [] => none
      match rest with
      | 43 :: rest => match ast with | .atom atom => some (.plus atom, captures, rest) | _ => none
      | 63 :: rest => match ast with
        | .start | .finish => none
        | _ => some (.optional ast, captures, rest)
      | _ => some (ast, captures, rest)
end

/-- Actual literal delimiters, no flags; real structural parser for the selected
constructs. No source-equality switch supplies an AST or match/capture result.
Alternation/lookarounds/ranges/nullable repetitions and other flags remain open. -/
def parseLiteral (units : JSString) : Option Syntax := do
  let rest ← match units with | 47 :: rest => some rest | _ => none
  let (elements, _, rest) ← parseSequence (units.length + 1) 0 rest
  if rest == [47] then some (.sequence elements) else none

def labelLiteral : JSString := [47, 94, 92, 58, 40, 91, 94, 92, 123, 92, 125, 93, 43, 41, 40, 63, 58, 92, 123, 40, 46, 43, 41, 92, 125, 41, 63, 36, 47]
def labelSyntax : Syntax := .sequence [.start, .atom (.literal 58),
  .capture 0 (.sequence [.plus (.excluded [123, 125])]),
  .optional (.group (.sequence [.atom (.literal 123), .capture 1 (.sequence [.plus .dot]), .atom (.literal 125)])), .finish]

/-- Independent fixed-source production for the actual literal profile. The
parser remains structural and admits other ASTs; this relation does not call it. -/
inductive LabelLiteralGrammar : JSString → Syntax → Prop where
  | actual : LabelLiteralGrammar
      [47, 94, 92, 58, 40, 91, 94, 92, 123, 92, 125, 93, 43, 41, 40, 63, 58, 92, 123, 40, 46, 43, 41, 92, 125, 41, 63, 36, 47]
      (.sequence [.start, .atom (.literal 58), .capture 0 (.sequence [.plus (.excluded [123, 125])]),
        .optional (.group (.sequence [.atom (.literal 123), .capture 1 (.sequence [.plus .dot]), .atom (.literal 125)])), .finish])

theorem parse_actual : parseLiteral labelLiteral = some labelSyntax := by rfl

theorem parse_label_complete (text : JSString) (ast : Syntax) (grammar : LabelLiteralGrammar text ast) : parseLiteral text = some ast := by
  cases grammar
  exact parse_actual

/-- Canonical exact-source parser provenance, not general soundness of every
other admitted source in the bounded structural frontend. -/
theorem parse_label_sound (text : JSString) (ast : Syntax) (source : text = labelLiteral)
    (parsed : parseLiteral text = some ast) : LabelLiteralGrammar text ast := by
  subst text
  rw [parse_actual] at parsed
  cases Option.some.inj parsed
  exact .actual

end HonoLean.Upstream.ECMA2025.LabelRegExp
