import HonoLean.Upstream.ECMA2025.LiteralLookahead.Compiler

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LiteralLookahead
open SourceSubset

def runLiteral : Nat → List LiteralInstruction → Nat → JSString → Outcome
  | 0, _, _, _ => .exhausted
  | _ + 1, [], _, _ => .noMatch
  | fuel + 1, instruction :: rest, cursor, input => match instruction with
    | .accept => .matched ⟨0, cursor, []⟩
    | .consumeUnit expected => match input with
      | [] => .noMatch
      | unit :: tail => if unit == expected then runLiteral fuel rest (cursor + 1) tail else .noMatch

/-- The assertion runs child code at saved cursor/input. A child success
resumes the parent with BOTH originals, without consuming the child's span.
Only the admitted slash-separated range profile gets the stated model-language correctness theorem;
this deterministic repeat machine is not general regex backtracking. -/
def run : Nat → List Instruction → Nat → JSString → Outcome
  | 0, _, _, _ => .exhausted
  | _ + 1, [], _, _ => .noMatch
  | fuel + 1, instruction :: rest, cursor, input =>
    match instruction with
    | .assertStart => if cursor = 0 then run fuel rest cursor input else .noMatch
    | .consumeRange lower upper => match input with
      | [] => .noMatch
      | unit :: tail => if RangeRegExp.InRange lower upper unit then run fuel rest (cursor + 1) tail else .noMatch
    | .repeatRange lower upper => match input with
      | [] => run fuel rest cursor []
      | unit :: tail => if RangeRegExp.InRange lower upper unit then run fuel (instruction :: rest) (cursor + 1) tail
        else run fuel rest cursor input
    | .consumeUnit expected => match input with
      | [] => .noMatch
      | unit :: tail => if unit == expected then run fuel rest (cursor + 1) tail else .noMatch
    | .positive child => match runLiteral fuel child cursor input with
      | .exhausted => .exhausted
      | .noMatch => .noMatch
      | .matched _ => run fuel rest cursor input
    | .accept => .matched ⟨0, cursor, []⟩

/-- Explicit bound for the admitted compiled program. Literal checking stops
on a mismatch or exhausted input, so the assertion costs at most input length.
This is a proof budget, not a native time/memory guarantee. -/
def execute (program : List Instruction) (input : JSString) : Outcome :=
  run (input.length + 8) program 0 input

def scanRange (lower upper : UInt16) : JSString → JSString × JSString
  | [] => ([], [])
  | unit :: rest =>
    if RangeRegExp.InRange lower upper unit then
      let (taken, suffix) := scanRange lower upper rest
      (unit :: taken, suffix)
    else ([], unit :: rest)

theorem positive_restores (fuel cursor : Nat) (child : List LiteralInstruction) (rest : List Instruction) (input : JSString) (result : Match)
    (succeeded : runLiteral fuel child cursor input = .matched result) :
    run (fuel + 1) (.positive child :: rest) cursor input = run fuel rest cursor input := by
  simp [run, succeeded]

theorem repeat_progress (unit : UInt16) (rest : JSString) : rest.length < (unit :: rest).length := by simp

end HonoLean.Upstream.ECMA2025.LiteralLookahead
