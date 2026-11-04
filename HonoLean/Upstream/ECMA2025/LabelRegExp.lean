import HonoLean.Upstream.ECMA2025.LabelRegExpSyntax

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LabelRegExp
open SourceSubset

inductive Code where
  | empty
  | test (atom : Atom)
  | assertStart | assertEnd
  | sequence (left right : Code)
  | greedyPlus (atom : Atom)
  | optional (body : Code)
  | saveBegin (index : Nat)
  | saveEnd (index : Nat)
  deriving Repr, DecidableEq

def compile : Syntax → Code
  | .atom atom => .test atom
  | .start => .assertStart
  | .finish => .assertEnd
  | .sequence elements => (elements.map compile).foldr Code.sequence .empty
  | .plus atom => .greedyPlus atom
  | .optional body => .optional (compile body)
  | .capture index body => .sequence (.saveBegin index) (.sequence (compile body) (.saveEnd index))
  | .group body => compile body

def labelCode : Code := compile labelSyntax

def captureSlots : Code → Nat
  | .sequence left right => max (captureSlots left) (captureSlots right)
  | .optional body => captureSlots body
  | .saveBegin index | .saveEnd index => index + 1
  | _ => 0

def atomMatches : Atom → UInt16 → Bool
  | .literal expected, actual => actual == expected
  | .excluded units, actual => !units.contains actual
  | .dot, actual => !([10, 13, 8232, 8233] : JSString).contains actual

/-- Independent character contract, rather than a call to the VM's test. -/
def AtomAccepts : Atom → UInt16 → Prop
  | .literal expected, actual => actual = expected
  | .excluded units, actual => actual ∉ units
  | .dot, actual => actual ≠ 10 ∧ actual ≠ 13 ∧ actual ≠ 8232 ∧ actual ≠ 8233
instance (atom : Atom) (unit : UInt16) : Decidable (AtomAccepts atom unit) := by
  cases atom <;> unfold AtomAccepts <;> infer_instance

theorem atomMatches_iff (atom : Atom) (unit : UInt16) : atomMatches atom unit = true ↔ AtomAccepts atom unit := by
  cases atom <;> simp [atomMatches, AtomAccepts]

/-- Consuming greedy scan. Its recursive candidate list precedes the shorter
one-unit alternative; every recursive step consumes exactly the actual head.
The VM later tries suffix code on these states, so this is real backtracking. -/
def greedySplits (atom : Atom) : JSString → List (JSString × JSString)
  | [] => []
  | unit :: rest =>
    if atomMatches atom unit then
      (greedySplits atom rest).map (fun (taken, suffix) => (unit :: taken, suffix)) ++ [([unit], rest)]
    else []

structure Thread where
  seen : JSString := []
  remaining : JSString
  opens : List Nat := [0, 0]
  captures : List (Option (Nat × Nat)) := [none, none]
  deriving Repr, DecidableEq

def consume (thread : Thread) (taken suffix : JSString) : Thread :=
  {thread with seen := thread.seen ++ taken, remaining := suffix}

/-- Structurally terminating instruction interpreter. Sequence tries all
states from its left program in order; optional tries CONSUMING body successes
before skip. RepeatMatcher with minimum0 rejects a successful zero-progress
attempt; skip uses the ORIGINAL cursor and capture snapshot. Capture
save instructions record actual cursor positions, not desired capture strings.
Only consuming atoms repeat. Native time/memory/allocation adequacy is open. -/
def run : Code → Thread → List Thread
  | .empty, thread => [thread]
  | .test atom, thread => match thread.remaining with
    | [] => []
    | unit :: rest => if atomMatches atom unit then [consume thread [unit] rest] else []
  | .assertStart, thread => if thread.seen.isEmpty then [thread] else []
  | .assertEnd, thread => if thread.remaining.isEmpty then [thread] else []
  | .sequence left right, thread => (run left thread).flatMap (run right)
  | .greedyPlus atom, thread => (greedySplits atom thread.remaining).map (fun (taken, suffix) => consume thread taken suffix)
  | .optional body, thread =>
    (run body thread).filter (fun after => thread.seen.length < after.seen.length) ++ [thread]
  | .saveBegin index, thread => [{thread with opens := thread.opens.set index thread.seen.length}]
  | .saveEnd index, thread => [{thread with captures := (thread.captures.set index
      (some (thread.opens[index]?.getD 0, thread.seen.length)))}]

structure Match where
  start : Nat
  stop : Nat
  captures : List (Option (Nat × Nat))
  deriving Repr, DecidableEq
inductive Outcome where
  | exhausted | noMatch | matched (result : Match)
  deriving Repr, DecidableEq

/-- Nonempty candidate set selects the first greedy/backtracking success.
No resource timeout is hidden as noMatch. Totality follows from Code's structural
recursion and greedySplits' strictly shorter input; exhausted is never produced. -/
def execute (program : Code) (input : JSString) : Outcome :=
  match run program ⟨[], input, List.replicate (captureSlots program) 0, List.replicate (captureSlots program) none⟩ with
  | [] => .noMatch
  | thread :: _ => .matched ⟨0, thread.seen.length, thread.captures⟩

theorem execute_ne_exhausted (program : Code) (input : JSString) : execute program input ≠ .exhausted := by
  unfold execute
  split <;> simp

theorem plus_progress (unit : UInt16) (rest : JSString) : rest.length < (unit :: rest).length := by simp

theorem greedySplits_mem (atom : Atom) (input taken suffix : JSString) :
    (taken, suffix) ∈ greedySplits atom input ↔
      input = taken ++ suffix ∧ taken ≠ [] ∧ ∀ unit ∈ taken, AtomAccepts atom unit := by
  induction input generalizing taken suffix with
  | nil =>
    cases taken <;> simp [greedySplits]
  | cons unit rest ih =>
    by_cases inside : atomMatches atom unit = true
    · have valid := (atomMatches_iff atom unit).mp inside
      rw [greedySplits, ite_eq_left inside]
      constructor
      · intro member
        rcases List.mem_append.mp member with long | short
        · obtain ⟨⟨part, ending⟩, member, equal⟩ := List.mem_map.mp long
          cases equal
          obtain ⟨parts, nonempty, accepts⟩ := (ih part suffix).mp member
          exact ⟨by simp [parts], by simp, by simpa using And.intro valid accepts⟩
        · have equal := List.mem_singleton.mp short
          cases equal
          exact ⟨rfl, by simp, by simpa using valid⟩
      · rintro ⟨parts, nonempty, accepts⟩
        cases taken with
        | nil => exact False.elim (nonempty rfl)
        | cons head tail =>
          have equal := List.cons.inj parts
          cases equal.1
          cases tail with
          | nil =>
            apply List.mem_append.mpr
            exact Or.inr (List.mem_singleton.mpr (by simp_all))
          | cons second remaining =>
            apply List.mem_append.mpr
            apply Or.inl
            apply List.mem_map.mpr
            refine ⟨(second :: remaining, suffix), (ih _ _).mpr ⟨equal.2, by simp, ?_⟩, rfl⟩
            intro value member
            exact accepts value (by simp [member])
    · have invalid : ¬ AtomAccepts atom unit := by
        intro valid
        exact inside ((atomMatches_iff atom unit).mpr valid)
      rw [greedySplits, ite_eq_right inside]
      constructor
      · intro member; cases member
      · rintro ⟨parts, nonempty, accepts⟩
        cases taken with
        | nil => exact False.elim (nonempty rfl)
        | cons head tail =>
          have equal := List.cons.inj parts
          cases equal.1
          exact False.elim (invalid (accepts unit (by simp)))

/-- Every supported instruction is forward-only. This justifies the strict
progress test used by minimum0 optional quantification, without admitting a
backward matching/lookbehind interpretation. -/
theorem run_cursor_monotone (program : Code) (before after : Thread) (member : after ∈ run program before) :
    before.seen.length ≤ after.seen.length := by
  induction program generalizing before after with
  | empty => cases List.mem_singleton.mp member; exact Nat.le_refl _
  | test atom =>
    cases remaining : before.remaining with
    | nil => simp [run, remaining] at member
    | cons unit rest =>
      by_cases valid : atomMatches atom unit = true
      · have equal : after = consume before [unit] rest := by simpa [run, remaining, valid] using member
        rw [equal]
        simp [consume]
      · simp [run, remaining, valid] at member
  | assertStart =>
    by_cases start : before.seen.isEmpty = true
    · cases (show after = before by simpa [run, start] using member); exact Nat.le_refl _
    · simp [run, start] at member
  | assertEnd =>
    by_cases finish : before.remaining.isEmpty = true
    · cases (show after = before by simpa [run, finish] using member); exact Nat.le_refl _
    · simp [run, finish] at member
  | sequence left right ihLeft ihRight =>
    obtain ⟨middle, fromLeft, fromRight⟩ := List.mem_flatMap.mp member
    exact Nat.le_trans (ihLeft before middle fromLeft) (ihRight middle after fromRight)
  | greedyPlus atom =>
    obtain ⟨⟨taken, suffix⟩, _, equal⟩ := List.mem_map.mp member
    cases equal
    simp [consume]
  | optional body ih =>
    rcases List.mem_append.mp member with consumed | skipped
    · exact ih before after (List.mem_filter.mp consumed).1
    · cases List.mem_singleton.mp skipped; exact Nat.le_refl _
  | saveBegin index => cases List.mem_singleton.mp member; exact Nat.le_refl _
  | saveEnd index => cases List.mem_singleton.mp member; exact Nat.le_refl _

theorem run_test_prefix_progress (atom : Atom) (rest : Code) (before after : Thread)
    (member : after ∈ run (.sequence (.test atom) rest) before) :
    before.seen.length < after.seen.length := by
  obtain ⟨middle, first, remaining⟩ := List.mem_flatMap.mp member
  cases input : before.remaining with
  | nil => simp [run, input] at first
  | cons unit tail =>
    by_cases accepted : atomMatches atom unit = true
    · have equal : middle = consume before [unit] tail := by simpa [run, input, accepted] using first
      subst middle
      have monotone := run_cursor_monotone rest _ after remaining
      simp only [consume, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at monotone
      omega
    · simp [run, input, accepted] at first

/-- Canonical brace groups start by consuming '{', so the min0 zero-progress
guard provably removes no candidate. This is derived from real instructions,
not assumed successful future execution or a frontend narrowing. -/
theorem run_optional_consuming_prefix (atom : Atom) (rest : Code) (before : Thread) :
    run (.optional (.sequence (.test atom) rest)) before =
      run (.sequence (.test atom) rest) before ++ [before] := by
  change (run (.sequence (.test atom) rest) before).filter _ ++ [before] = _
  rw [List.filter_eq_self.mpr]
  intro after member
  exact decide_eq_true (run_test_prefix_progress atom rest before after member)

/-- Discard every successful non-consuming attempt, including its capture
updates. The only remaining path is the ORIGINAL pre-attempt snapshot. -/
theorem run_optional_zero_only (body : Code) (before : Thread)
    (zero : ∀ after ∈ run body before, after.seen.length = before.seen.length) :
    run (.optional body) before = [before] := by
  change (run body before).filter _ ++ [before] = [before]
  have empty : (run body before).filter (fun after => before.seen.length < after.seen.length) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro after member
    simp [zero after member]
  rw [empty]
  rfl

end HonoLean.Upstream.ECMA2025.LabelRegExp
