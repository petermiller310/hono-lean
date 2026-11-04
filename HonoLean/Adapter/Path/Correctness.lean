import HonoLean.Adapter.Path.Spec
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.String.Lemmas.Intercalate
import Init.Data.List.SplitOn.Lemmas

namespace HonoLean.Adapter.PathText

theorem validSegment_iff (text : String) :
    validSegment text = true ↔ Segment text := by
  simp [validSegment, Segment, Character, Literal.nameStart, List.all_eq_true,
    Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem Segment.no_slash {text : String} (valid : Segment text) :
    '/' ∉ text.toList := by
  intro member
  have := valid.2 '/' member
  simp [Character] at this

private theorem rejoin_split (text : String) :
    "/".intercalate ((text.split '/').toList.map (·.copy)) = text := by
  apply String.toList_inj.mp
  rw [String.toList_intercalate, String.toList_split_char]
  simp

private theorem render_cons (first : String) (rest : List String) :
    render (first :: rest) = "/".intercalate ("" :: first :: rest) := by
  simp [render, String.intercalate_cons_of_ne_nil]

private theorem split_render {pieces : HonoLean.Path}
    (valid : ∀ piece ∈ pieces, Segment piece) (nonempty : pieces ≠ []) :
    ((render pieces).split '/').toList.map (·.copy) = "" :: pieces := by
  cases pieces with
  | nil => contradiction
  | cons first rest =>
    rw [render_cons]
    have noSlash : ∀ piece ∈ "" :: first :: rest, '/' ∉ piece.toList := by
      intro piece member
      rcases List.mem_cons.mp member with equal | member
      · subst piece; simp
      · exact (valid piece member).no_slash
    simpa using (String.toList_split_intercalate (c := '/') noSlash)

/-- Soundness includes the exact returned segments, not just membership in the
accepted language. Completeness is the reverse implication. -/
theorem parsePath_iff (text : String) (pieces : HonoLean.Path) :
    parsePath text = .ok pieces ↔ Denotes text pieces := by
  constructor
  · intro parsed
    unfold parsePath at parsed
    split at parsed
    next root =>
      simp only [Except.ok.injEq] at parsed
      subst pieces
      exact ⟨by simp, by simpa [render] using root⟩
    next nonroot =>
      split at parsed
      next head parts splitEq =>
        split at parsed
        next accepted =>
          simp only [Except.ok.injEq] at parsed
          subst pieces
          have conditions := Bool.and_eq_true_iff.mp accepted
          have nonempty : parts ≠ [] := by simpa using conditions.1
          have valid : ∀ piece ∈ parts, Segment piece := by
            intro piece member
            exact (validSegment_iff piece).mp ((List.all_eq_true.mp conditions.2) piece member)
          refine ⟨valid, ?_⟩
          have joined := rejoin_split text
          rw [splitEq] at joined
          have spelling : "/".intercalate ("" :: parts) = render parts := by
            simp [render, String.intercalate_cons_of_ne_nil nonempty]
          exact (spelling ▸ joined).symm
        next => contradiction
      next => contradiction
  · rintro ⟨valid, rfl⟩
    cases pieces with
    | nil => simp [parsePath, render]
    | cons first rest =>
      have nonroot : render (first :: rest) ≠ "/" := by
        intro equal
        have splitEq := split_render valid (by simp)
        rw [equal] at splitEq
        rw [String.toList_split_char] at splitEq
        have headEmpty : first = "" := (List.cons.inj (List.cons.inj splitEq).2).1.symm
        exact (valid first (by simp)).1 headEmpty
      have allValid : (first :: rest).all validSegment = true :=
        List.all_eq_true.mpr (fun piece member => (validSegment_iff piece).mpr (valid piece member))
      simp [parsePath, nonroot, split_render valid (by simp), allValid]

theorem sound {text : String} {pieces : HonoLean.Path}
    (parsed : parsePath text = .ok pieces) : Denotes text pieces :=
  (parsePath_iff text pieces).mp parsed

theorem complete {text : String} {pieces : HonoLean.Path}
    (grammar : Denotes text pieces) : parsePath text = .ok pieces :=
  (parsePath_iff text pieces).mpr grammar

theorem parse_render {pieces : HonoLean.Path}
    (valid : ∀ piece ∈ pieces, Segment piece) :
    parsePath (render pieces) = .ok pieces :=
  complete ⟨valid, rfl⟩

theorem unique {text : String} {left right : HonoLean.Path}
    (a : Denotes text left) (b : Denotes text right) : left = right := by
  have := (complete a).symm.trans (complete b)
  exact Except.ok.inj this

theorem error_kind {text : String} {error : Error}
    (rejected : parsePath text = .error error) : error.kind = .invalidRequest := by
  unfold parsePath at rejected
  split at rejected
  · contradiction
  · split at rejected
    · split at rejected
      · contradiction
      · cases rejected; rfl
    · cases rejected; rfl

/-- Exactly the strings outside the grammar are rejected, with the request
error category rather than a successful empty path or empty match list. -/
theorem rejects_iff (text : String) :
    (∃ error, parsePath text = .error error ∧ error.kind = .invalidRequest) ↔
      ¬ ∃ pieces, Denotes text pieces := by
  constructor
  · rintro ⟨error, rejected, _⟩ ⟨pieces, grammar⟩
    have accepted := complete grammar
    rw [rejected] at accepted
    contradiction
  · intro outside
    cases parsed : parsePath text with
    | ok pieces => exact False.elim (outside ⟨pieces, sound parsed⟩)
    | error error => exact ⟨error, rfl, error_kind parsed⟩

/-- info: 'HonoLean.Adapter.PathText.parsePath_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsePath_iff

/-- info: 'HonoLean.Adapter.PathText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

end HonoLean.Adapter.PathText
