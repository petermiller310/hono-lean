import HonoLean.Upstream.SourceSubset.Syntax

set_option autoImplicit false

namespace HonoLean.Upstream.ECMA2025.RangeRegExp

open SourceSubset

/-- A small source syntax with explicit assertions, a consuming code-unit
range, plus and concatenation. General regexp grammar/flags remain future work. -/
inductive Syntax where
  | start
  | range (lower upper : UInt16)
  | plus (atom : Syntax)
  | finish
  | sequence (left right : Syntax)
  deriving Repr, DecidableEq

def anchoredPlus (lower upper : UInt16) : Syntax :=
  .sequence .start (.sequence (.plus (.range lower upper)) .finish)

/-- Endpoints are literal ASCII alphanumerics, avoiding escape/metacharacter
interpretation. The range BETWEEN them may include other code units. -/
def SafeEndpoint (unit : UInt16) : Prop :=
  (48 ≤ unit.toNat ∧ unit.toNat ≤ 57) ∨ (65 ≤ unit.toNat ∧ unit.toNat ≤ 90) ∨
    (97 ≤ unit.toNat ∧ unit.toNat ≤ 122)
instance (unit : UInt16) : Decidable (SafeEndpoint unit) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Independent source grammar. This relation does not call the parser. -/
inductive Grammar : JSString → Syntax → Prop where
  | anchored (lower upper : UInt16) (safeLower : SafeEndpoint lower) (safeUpper : SafeEndpoint upper)
      (ordered : lower.toNat ≤ upper.toNat) :
      Grammar [94, 91, lower, 45, upper, 93, 43, 36] (anchoredPlus lower upper)

def parse : JSString → Option Syntax
  | [caret, opening, lower, dash, upper, close, plus, dollar] =>
    if caret = 94 ∧ opening = 91 ∧ dash = 45 ∧ close = 93 ∧ plus = 43 ∧ dollar = 36 ∧
        SafeEndpoint lower ∧ SafeEndpoint upper ∧ lower.toNat ≤ upper.toNat then
      some (anchoredPlus lower upper) else none
  | _ => none

theorem parse_sound (text : JSString) (ast : Syntax) (parsed : parse text = some ast) : Grammar text ast := by
  unfold parse at parsed
  split at parsed
  · split at parsed
    · rename_i caret opening lower dash upper close plus dollar shape valid
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, safeLower, safeUpper, ordered⟩ := valid
      cases Option.some.inj parsed
      exact .anchored _ _ safeLower safeUpper ordered
    · cases parsed
  · cases parsed

theorem parse_complete (text : JSString) (ast : Syntax) (grammar : Grammar text ast) : parse text = some ast := by
  cases grammar with
  | anchored lower upper safeLower safeUpper ordered => simp [parse, safeLower, safeUpper, ordered]

theorem parse_iff (text : JSString) (ast : Syntax) : parse text = some ast ↔ Grammar text ast :=
  ⟨parse_sound text ast, parse_complete text ast⟩

inductive Instruction where
  | assertStart
  | consumeRange (lower upper : UInt16)
  | repeatRange (lower upper : UInt16)
  | assertEnd
  | accept
  deriving Repr, DecidableEq

/-- Plus is compiled only for a consuming range atom. Nullable repeated bodies
are rejected, so the repeat instruction cannot loop without input progress. -/
def compileFragment : Syntax → Option (List Instruction)
  | .start => some [.assertStart]
  | .range lower upper => some [.consumeRange lower upper]
  | .finish => some [.assertEnd]
  | .sequence left right => do return (← compileFragment left) ++ (← compileFragment right)
  | .plus (.range lower upper) => some [.consumeRange lower upper, .repeatRange lower upper]
  | .plus _ => none

def compile (ast : Syntax) : Option (List Instruction) :=
  (compileFragment ast).map (· ++ [.accept])

def code (lower upper : UInt16) : List Instruction :=
  [.assertStart, .consumeRange lower upper, .repeatRange lower upper, .assertEnd, .accept]

theorem compile_anchoredPlus (lower upper : UInt16) : compile (anchoredPlus lower upper) = some (code lower upper) := rfl

structure Match where
  start : Nat
  stop : Nat
  captures : List (Option (Nat × Nat))
  deriving Repr, DecidableEq

inductive Outcome where
  | exhausted
  | noMatch
  | matched (result : Match)
  deriving Repr, DecidableEq

def InRange (lower upper unit : UInt16) : Prop := lower.toNat ≤ unit.toNat ∧ unit.toNat ≤ upper.toNat
instance (lower upper unit : UInt16) : Decidable (InRange lower upper unit) := inferInstanceAs (Decidable (_ ∧ _))

/-- A small operational instruction machine. The repeat step consumes an
actual input head and advances cursor; a nonmember falls through to assertEnd.
Only compiled anchored-range programs receive the correctness theorem below;
this is not a general backtracking VM or whole-regexp adequacy assertion. -/
def run : Nat → List Instruction → Nat → JSString → Outcome
  | 0, _, _, _ => .exhausted
  | _ + 1, [], _, _ => .noMatch
  | fuel + 1, instruction :: rest, cursor, input =>
    match instruction with
    | .assertStart => if cursor = 0 then run fuel rest cursor input else .noMatch
    | .consumeRange lower upper =>
      match input with
      | [] => .noMatch
      | unit :: tail => if InRange lower upper unit then run fuel rest (cursor + 1) tail else .noMatch
    | .repeatRange lower upper =>
      match input with
      | [] => run fuel rest cursor []
      | unit :: tail => if InRange lower upper unit then run fuel (instruction :: rest) (cursor + 1) tail
        else run fuel rest cursor input
    | .assertEnd => if input.isEmpty then run fuel rest cursor input else .noMatch
    | .accept => .matched ⟨0, cursor, []⟩

/-- The budget covers all consumed units plus assertions/repeat exit/accept.
Exhaustion is distinct from a failed match; no wall-clock/memory/resource
adequacy claim follows from mathematical termination. -/
def execute (program : List Instruction) (input : JSString) : Outcome := run (input.length + 6) program 0 input

/-- Independent accepted language, with no evaluator/compiler/parser call. -/
def Accepted (lower upper : UInt16) (input : JSString) : Prop :=
  input ≠ [] ∧ ∀ unit ∈ input, InRange lower upper unit

instance (lower upper : UInt16) (input : JSString) : Decidable (Accepted lower upper input) :=
  inferInstanceAs (Decidable (_ ∧ ∀ unit ∈ input, InRange lower upper unit))

/-- Every taken quantified range transition consumes exactly one code unit.
This is the progress measure, independent of the extra machine fuel. -/
theorem repeat_progress (unit : UInt16) (tail : JSString) : tail.length < (unit :: tail).length := by simp

theorem repeat_step (fuel cursor : Nat) (lower upper unit : UInt16) (tail : JSString) (rest : List Instruction)
    (inside : InRange lower upper unit) :
    run (fuel + 1) (.repeatRange lower upper :: rest) cursor (unit :: tail) =
      run fuel (.repeatRange lower upper :: rest) (cursor + 1) tail ∧
    tail.length < (unit :: tail).length ∧ cursor < cursor + 1 := by
  exact ⟨by simp [run, inside], repeat_progress unit tail, by omega⟩

/-- The repeat suffix scans all remaining units, retaining actual cursor
progress and the end assertion. No desired match/span is an input premise. -/
theorem run_repeat (extra cursor : Nat) (lower upper : UInt16) (input : JSString) :
    run (extra + input.length + 4) [.repeatRange lower upper, .assertEnd, .accept] cursor input =
      if ∀ unit ∈ input, InRange lower upper unit then .matched ⟨0, cursor + input.length, []⟩ else .noMatch := by
  induction input generalizing extra cursor with
  | nil => simp [run]
  | cons unit tail ih =>
    by_cases inside : InRange lower upper unit
    · have recursive := ih extra (cursor + 1)
      have budget : extra + (unit :: tail).length + 4 = (extra + tail.length + 4) + 1 := by simp; omega
      rw [budget, run, ite_eq_left inside]
      simpa [List.mem_cons, inside, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using recursive
    · have budget : extra + (unit :: tail).length + 4 = (extra + tail.length + 3) + 2 := by simp; omega
      rw [budget]
      simp [run, inside]

theorem run_anchoredPlus (extra : Nat) (lower upper : UInt16) (input : JSString) :
    run (extra + input.length + 6) (code lower upper) 0 input =
      if Accepted lower upper input then .matched ⟨0, input.length, []⟩ else .noMatch := by
  cases input with
  | nil => simp [run, code, Accepted]
  | cons unit tail =>
    by_cases inside : InRange lower upper unit
    · have budget : extra + (unit :: tail).length + 6 = (extra + tail.length + 5) + 2 := by simp; omega
      rw [budget]
      simp only [code]
      rw [run, ite_eq_left rfl, run, ite_eq_left inside]
      have repeated := run_repeat (extra + 1) 1 lower upper tail
      simpa [Accepted, List.mem_cons, inside, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using repeated
    · have budget : extra + (unit :: tail).length + 6 = (extra + tail.length + 5) + 2 := by simp; omega
      rw [budget]
      simp [code, run, inside, Accepted]

theorem execute_anchoredPlus (lower upper : UInt16) (input : JSString) :
    execute (code lower upper) input =
      if Accepted lower upper input then .matched ⟨0, input.length, []⟩ else .noMatch := by
  simpa [execute] using run_anchoredPlus 0 lower upper input

theorem execute_ne_exhausted (lower upper : UInt16) (input : JSString) : execute (code lower upper) input ≠ .exhausted := by
  rw [execute_anchoredPlus]
  split <;> simp

theorem execute_success_iff (lower upper : UInt16) (input : JSString) :
    execute (code lower upper) input = .matched ⟨0, input.length, []⟩ ↔ Accepted lower upper input := by
  rw [execute_anchoredPlus]
  split <;> simp_all

theorem execute_matched_iff (lower upper : UInt16) (input : JSString) (result : Match) :
    execute (code lower upper) input = .matched result ↔
      Accepted lower upper input ∧ result = ⟨0, input.length, []⟩ := by
  rw [execute_anchoredPlus]
  split <;> simp_all [eq_comm]

/-- Parser provenance gives the actual compiled endpoint for every admitted
source, rather than only a separately supplied digit-pattern constant. -/
theorem parsed_execution (text input : JSString) (ast : Syntax) (parsed : parse text = some ast) :
    ∃ lower upper, Grammar text (anchoredPlus lower upper) ∧ ast = anchoredPlus lower upper ∧
      compile ast = some (code lower upper) ∧
      execute (code lower upper) input =
        (if Accepted lower upper input then .matched ⟨0, input.length, []⟩ else .noMatch) := by
  cases parse_sound text ast parsed with
  | anchored lower upper safeLower safeUpper ordered =>
    exact ⟨lower, upper, .anchored lower upper safeLower safeUpper ordered, rfl,
      compile_anchoredPlus lower upper, execute_anchoredPlus lower upper input⟩

theorem digits_success_iff (input : JSString) :
    execute (code 48 57) input = .matched ⟨0, input.length, []⟩ ↔
      input ≠ [] ∧ ∀ unit ∈ input, 48 ≤ unit.toNat ∧ unit.toNat ≤ 57 := by
  simpa [Accepted, InRange] using execute_success_iff 48 57 input

end HonoLean.Upstream.ECMA2025.RangeRegExp
