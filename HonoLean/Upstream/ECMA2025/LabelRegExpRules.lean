import HonoLean.Upstream.ECMA2025.LabelRegExp

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025.LabelRegExp
open SourceSubset
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def Name (name : JSString) : Prop := name ≠ [] ∧ ∀ unit ∈ name, unit ≠ 123 ∧ unit ≠ 125
def Body (body : JSString) : Prop := body ≠ [] ∧ ∀ unit ∈ body, unit ≠ 10 ∧ unit ≠ 13 ∧ unit ≠ 8232 ∧ unit ≠ 8233

/-- Independent label grammar/captures: no VM/parser/compiler is called here.
Name may include every line terminator; only dot-body excludes the four LT. -/
def Label (input name : JSString) (body : Option JSString) : Prop :=
  Name name ∧ match body with
  | none => input = 58 :: name
  | some body => Body body ∧ input = 58 :: (name ++ 123 :: (body ++ [125]))

def labelMatch (name : JSString) (body : Option JSString) : Match :=
  match body with
  | none => ⟨0, 1 + name.length, [some (1, 1 + name.length), none]⟩
  | some body => ⟨0, name.length + body.length + 3,
      [some (1, 1 + name.length), some (name.length + 2, name.length + body.length + 2)]⟩

def MatchContract (input : JSString) (matched : Match) : Prop :=
  ∃ name body, Label input name body ∧ matched = labelMatch name body

def finalThread (input name : JSString) (body : Option JSString) : Thread :=
  {seen := input, remaining := [],
   opens := match body with | none => [1, 0] | some _ => [1, name.length + 2]
   captures := (labelMatch name body).captures}

-- First normalize the real instruction program; no desired capture is fed to it.
theorem run_label_iff (input : JSString) (thread : Thread) :
    thread ∈ run labelCode ⟨[], input, [0, 0], [none, none]⟩ ↔
      ∃ name body, Label input name body ∧ thread = finalThread input name body := by
  cases input with
  | nil =>
    simp only [labelCode, labelSyntax, compile, run, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      List.isEmpty_nil, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.not_mem_nil,
      false_iff]
    rintro ⟨name, body, valid, _⟩
    cases body <;> simp [Label] at valid
  | cons first tail =>
    by_cases colon : first = 58
    · subst first
      simp only [labelCode, labelSyntax, compile, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        run, List.isEmpty_nil, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil, atomMatches,
        beq_self_eq_true, consume, List.flatMap_map, List.flatMap_assoc]
      simp [List.mem_flatMap, greedySplits_mem, AtomAccepts]
      constructor
      · rintro ⟨name, ending, ⟨splitName, nameNonempty, nameChars⟩, branch⟩
        rcases branch with ⟨⟨⟨afterOpen, openMember, body, closing, ⟨splitBody, bodyNonempty, bodyChars⟩, closeMember⟩, _⟩, complete⟩ |
          ⟨rfl, threadEq⟩
        · cases ending with
          | nil => simp at openMember
          | cons opening rest =>
            by_cases openBrace : opening = 123
            · subst opening
              simp only [↓reduceIte, List.mem_singleton] at openMember
              cases openMember
              change rest = body ++ closing at splitBody
              cases closing with
              | nil => simp at closeMember
              | cons closing restClose =>
                by_cases closeBrace : closing = 125
                · subst closing
                  simp only [↓reduceIte, List.mem_singleton] at closeMember
                  cases closeMember
                  have noRest : restClose = [] := complete
                  subst restClose
                  refine ⟨name, some body, ⟨⟨nameNonempty, nameChars⟩, ⟨bodyNonempty, bodyChars⟩, ?_⟩, ?_⟩
                  · simp_all
                  · simp [finalThread, labelMatch, splitName, splitBody, List.append_assoc,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                · simp [closeBrace] at closeMember
            · simp [openBrace] at openMember
        · refine ⟨name, none, ⟨⟨nameNonempty, nameChars⟩, ?_⟩, ?_⟩
          · simp_all
          · simpa [finalThread, labelMatch, splitName, Nat.add_comm] using threadEq
      · rintro ⟨name, body, valid, threadEq⟩
        cases body with
        | none =>
          obtain ⟨⟨nameNonempty, nameChars⟩, equal⟩ := valid
          have equalTail : tail = name := List.cons.inj equal |>.2
          subst tail
          refine ⟨name, [], ⟨by simp, nameNonempty, nameChars⟩, Or.inr ⟨rfl, ?_⟩⟩
          simpa [finalThread, labelMatch, Nat.add_comm] using threadEq
        | some body =>
          obtain ⟨⟨nameNonempty, nameChars⟩, ⟨bodyNonempty, bodyChars⟩, equal⟩ := valid
          have equalTail : tail = name ++ 123 :: (body ++ [125]) := List.cons.inj equal |>.2
          subst tail
          subst thread
          refine ⟨name, 123 :: (body ++ [125]), ⟨rfl, nameNonempty, nameChars⟩, Or.inl ⟨?_, rfl⟩⟩
          constructor
          · refine ⟨{seen := 58 :: (name ++ [123]), remaining := body ++ [125], opens := [1, 0], captures := [some (1, name.length + 1), none]},
              by simp, body, [125], ⟨rfl, bodyNonempty, bodyChars⟩, ?_⟩
            simp [finalThread, labelMatch, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · simp [finalThread]
    · have empty : run labelCode ⟨[], first :: tail, [0, 0], [none, none]⟩ = [] := by
        simp [labelCode, labelSyntax, compile, run, atomMatches, colon]
      rw [empty]
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨name, body, valid, _⟩
      cases body <;> simp [Label, colon] at valid

def labelSuffix : Option JSString → JSString
  | none => []
  | some body => 123 :: (body ++ [125])

theorem label_input (input name : JSString) (body : Option JSString) (valid : Label input name body) :
    input = 58 :: (name ++ labelSuffix body) := by
  cases body with
  | none => simpa [Label, labelSuffix] using valid.2
  | some body => simpa [Label, labelSuffix] using valid.2.2

theorem name_boundary_unique (left right leftRest rightRest : JSString)
    (leftChars : ∀ unit ∈ left, unit ≠ 123) (rightChars : ∀ unit ∈ right, unit ≠ 123)
    (leftEnd : leftRest = [] ∨ ∃ rest, leftRest = 123 :: rest)
    (rightEnd : rightRest = [] ∨ ∃ rest, rightRest = 123 :: rest)
    (equal : left ++ leftRest = right ++ rightRest) : left = right ∧ leftRest = rightRest := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨rfl, equal⟩
    | cons head tail =>
      rcases leftEnd with rfl | ⟨rest, rfl⟩
      · simp at equal
      · have first : head = 123 := (List.cons.inj equal).1.symm
        exact False.elim (rightChars head (by simp) first)
  | cons head tail ih =>
    cases right with
    | nil =>
      rcases rightEnd with rfl | ⟨rest, rfl⟩
      · simp at equal
      · have first : head = 123 := (List.cons.inj equal).1
        exact False.elim (leftChars head (by simp) first)
    | cons other remaining =>
      have first := List.cons.inj equal
      cases first.1
      have recursive := ih remaining
        (fun unit member => leftChars unit (by simp [member]))
        (fun unit member => rightChars unit (by simp [member])) first.2
      exact ⟨congrArg (List.cons head) recursive.1, recursive.2⟩

theorem label_unique (input firstName secondName : JSString) (firstBody secondBody : Option JSString)
    (first : Label input firstName firstBody) (second : Label input secondName secondBody) :
    firstName = secondName ∧ firstBody = secondBody := by
  have firstInput := label_input input firstName firstBody first
  have secondInput := label_input input secondName secondBody second
  have equal := List.cons.inj (firstInput.symm.trans secondInput) |>.2
  have firstEnd : labelSuffix firstBody = [] ∨ ∃ rest, labelSuffix firstBody = 123 :: rest := by
    cases firstBody <;> simp [labelSuffix]
  have secondEnd : labelSuffix secondBody = [] ∨ ∃ rest, labelSuffix secondBody = 123 :: rest := by
    cases secondBody <;> simp [labelSuffix]
  have names := name_boundary_unique firstName secondName (labelSuffix firstBody) (labelSuffix secondBody)
    (fun unit member => (first.1.2 unit member).1) (fun unit member => (second.1.2 unit member).1) firstEnd secondEnd equal
  refine ⟨names.1, ?_⟩
  have suffixes := names.2
  cases firstBody <;> cases secondBody <;> simp_all [labelSuffix]

/-- Soundness/completeness for arbitrary UTF16 input, including raw invalid
future RegExp bodies. Capture spans come from the real save instructions. -/
theorem execute_label_iff (input : JSString) (matched : Match) :
    execute labelCode input = .matched matched ↔ MatchContract input matched := by
  have slots : captureSlots labelCode = 2 := by cbv
  unfold execute
  rw [slots]
  change (match run labelCode ⟨[], input, [0, 0], [none, none]⟩ with
    | [] => Outcome.noMatch
    | thread :: _ => Outcome.matched ⟨0, thread.seen.length, thread.captures⟩) = .matched matched ↔ _
  generalize candidatesEq : run labelCode ⟨[], input, [0, 0], [none, none]⟩ = candidates
  cases candidates with
  | nil =>
    constructor
    · intro impossible; cases impossible
    · rintro ⟨name, body, valid, _⟩
      have member := (run_label_iff input (finalThread input name body)).mpr ⟨name, body, valid, rfl⟩
      rw [candidatesEq] at member
      cases member
  | cons thread tail =>
    have member : thread ∈ run labelCode ⟨[], input, [0, 0], [none, none]⟩ := by rw [candidatesEq]; simp
    obtain ⟨name, body, valid, rfl⟩ := (run_label_iff input thread).mp member
    have lengths : (labelMatch name body).stop = input.length := by
      cases body <;> simp_all [Label, labelMatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have resultEq : (⟨0, (finalThread input name body).seen.length, (finalThread input name body).captures⟩ : Match) =
        labelMatch name body := by
      cases body <;> simp_all [finalThread, labelMatch]
    change Outcome.matched ⟨0, (finalThread input name body).seen.length, (finalThread input name body).captures⟩ = .matched matched ↔ _
    rw [resultEq]
    constructor
    · intro equal
      exact ⟨name, body, valid, (Outcome.matched.inj equal).symm⟩
    · rintro ⟨otherName, otherBody, otherValid, rfl⟩
      obtain ⟨rfl, rfl⟩ := label_unique input name otherName body otherBody valid otherValid
      rfl

theorem execute_label_miss_iff (input : JSString) :
    execute labelCode input = .noMatch ↔ ¬ ∃ name body, Label input name body := by
  constructor
  · intro miss ⟨name, body, valid⟩
    have hit := (execute_label_iff input (labelMatch name body)).mpr ⟨name, body, valid, rfl⟩
    rw [miss] at hit
    cases hit
  · intro none
    cases result : execute labelCode input with
    | exhausted => exact False.elim (execute_ne_exhausted labelCode input result)
    | noMatch => rfl
    | matched matched =>
      obtain ⟨name, body, valid, _⟩ := (execute_label_iff input matched).mp result
      exact False.elim (none ⟨name, body, valid⟩)

theorem match_unique (input : JSString) (first second : Match)
    (firstValid : MatchContract input first) (secondValid : MatchContract input second) : first = second := by
  obtain ⟨firstName, firstBody, firstLabel, rfl⟩ := firstValid
  obtain ⟨secondName, secondBody, secondLabel, rfl⟩ := secondValid
  obtain ⟨rfl, rfl⟩ := label_unique input firstName secondName firstBody secondBody firstLabel secondLabel
  rfl

def extractCapture (input : JSString) (span : Option (Nat × Nat)) : Option JSString :=
  span.map (fun (start, stop) => (input.drop start).take (stop - start))

theorem label_capture_bounds (input name : JSString) (body : Option JSString) (valid : Label input name body) :
    (labelMatch name body).start = 0 ∧ (labelMatch name body).stop = input.length ∧
    (labelMatch name body).captures.length = 2 ∧
    ∀ span ∈ (labelMatch name body).captures, ∀ start stop, span = some (start, stop) → start ≤ stop ∧ stop ≤ input.length := by
  cases body with
  | none =>
    obtain ⟨_, rfl⟩ := valid
    simp [labelMatch, Nat.add_comm]
  | some body =>
    obtain ⟨_, _, rfl⟩ := valid
    simp [labelMatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem label_capture_values (input name : JSString) (body : Option JSString) (valid : Label input name body) :
    (labelMatch name body).captures.map (extractCapture input) = [some name, body] := by
  cases body with
  | none =>
    obtain ⟨_, rfl⟩ := valid
    simp [labelMatch, extractCapture]
  | some body =>
    obtain ⟨_, _, rfl⟩ := valid
    simp [labelMatch, extractCapture, List.drop_append, List.take_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have size : name.length + (body.length + 2) - (name.length + 2) = body.length := by omega
    rw [size, List.drop_eq_nil_of_le (by omega)]
    simp

theorem execute_label_hit (input name : JSString) (body : Option JSString) (valid : Label input name body) :
    execute labelCode input = .matched (labelMatch name body) :=
  (execute_label_iff input _).mpr ⟨name, body, valid, rfl⟩

theorem parsed_label_execution (text input : JSString) (ast : Syntax)
    (grammar : LabelLiteralGrammar text ast) (matched : Match) :
    parseLiteral text = some ast ∧ (execute (compile ast) input = .matched matched ↔ MatchContract input matched) := by
  cases grammar
  exact ⟨parse_actual, execute_label_iff input matched⟩

/-- Every plus candidate consumes a nonempty prefix, so all choices progress
and the recursive scan itself shrinks. No nullable body can repeat. -/
theorem greedy_choice_progress (atom : Atom) (input taken suffix : JSString)
    (candidate : (taken, suffix) ∈ greedySplits atom input) :
    0 < taken.length ∧ suffix.length < input.length ∧ taken.length ≤ input.length := by
  obtain ⟨rfl, nonempty, _⟩ := (greedySplits_mem atom input taken suffix).mp candidate
  have positive : 0 < taken.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_append]
  omega

theorem greedySplits_ordered (atom : Atom) (input : JSString) :
    (greedySplits atom input).Pairwise (fun first second => second.1.length < first.1.length) := by
  induction input with
  | nil => simp [greedySplits]
  | cons unit rest ih =>
    unfold greedySplits
    split
    · apply List.pairwise_append.mpr
      refine ⟨?_, by simp, ?_⟩
      · simpa only [List.pairwise_map, List.length_cons, Nat.add_lt_add_iff_right] using ih
      · intro long member short last
        have shortEq := List.mem_singleton.mp last
        subst short
        obtain ⟨⟨taken, suffix⟩, candidate, rfl⟩ := List.mem_map.mp member
        have progress := greedy_choice_progress atom rest taken suffix candidate
        simpa using progress.1
    · simp

end HonoLean.Upstream.ECMA2025.LabelRegExp
