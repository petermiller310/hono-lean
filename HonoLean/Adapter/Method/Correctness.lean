import HonoLean.Adapter.Method.Spec

namespace HonoLean.Adapter.MethodText

theorem validMethod_iff (text : String) :
    Literal.ValidMethod text ↔ Spelling text := by
  simp [Literal.ValidMethod, Spelling, Character, List.all_eq_true, Bool.and_eq_true]

/-- Every success has the grammar's exact spelling; every such method is returned. -/
theorem parseMethod_iff (kind : ErrorKind) (text : String) (method : Literal.Method) :
    parseMethod kind text = .ok method ↔ Denotes text method := by
  constructor
  · intro parsed
    unfold parseMethod at parsed
    split at parsed
    next valid =>
      cases parsed
      exact ⟨(validMethod_iff text).mp valid, rfl⟩
    next => contradiction
  · rintro ⟨grammar, spelling⟩
    have valid := (validMethod_iff text).mpr grammar
    cases method with
    | mk name proof =>
      simp only at spelling
      subst name
      simp only [parseMethod, dite_eq_left valid]
      rfl

theorem sound {kind : ErrorKind} {text : String} {method : Literal.Method}
    (parsed : parseMethod kind text = .ok method) : Denotes text method :=
  (parseMethod_iff kind text method).mp parsed

/-- Completeness needs only the grammar, without a preconstructed typed method. -/
theorem complete (kind : ErrorKind) {text : String} (grammar : Spelling text) :
    ∃ method, parseMethod kind text = .ok method ∧ method.name = text := by
  let method : Literal.Method := ⟨text, (validMethod_iff text).mpr grammar⟩
  exact ⟨method, (parseMethod_iff kind text method).mpr ⟨grammar, rfl⟩, rfl⟩

theorem accepts_iff (kind : ErrorKind) (text : String) :
    (∃ method, parseMethod kind text = .ok method) ↔ Spelling text := by
  constructor
  · rintro ⟨method, parsed⟩
    exact (sound parsed).1
  · intro grammar
    obtain ⟨method, parsed, _⟩ := complete kind grammar
    exact ⟨method, parsed⟩

/-- A typed method's spelling parses back to that same method. -/
theorem parse_name (kind : ErrorKind) (method : Literal.Method) :
    parseMethod kind method.name = .ok method :=
  (parseMethod_iff kind method.name method).mpr
    ⟨(validMethod_iff method.name).mp method.valid, rfl⟩

theorem error_kind {kind : ErrorKind} {text : String} {error : Error}
    (rejected : parseMethod kind text = .error error) : error.kind = kind := by
  unfold parseMethod at rejected
  split at rejected
  · contradiction
  · cases rejected; rfl

/-- Exactly strings outside the grammar are rejected with the supplied category. -/
theorem rejects_iff (kind : ErrorKind) (text : String) :
    (∃ error, parseMethod kind text = .error error ∧ error.kind = kind) ↔
      ¬ Spelling text := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨method, parsed, _⟩ := complete kind grammar
    rw [rejected] at parsed
    contradiction
  · intro outside
    cases parsed : parseMethod kind text with
    | ok method => exact False.elim (outside (sound parsed).1)
    | error error => exact ⟨error, rfl, error_kind parsed⟩

/-- info: 'HonoLean.Adapter.MethodText.parseMethod_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parseMethod_iff

/-- info: 'HonoLean.Adapter.MethodText.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepts_iff

/-- info: 'HonoLean.Adapter.MethodText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

end HonoLean.Adapter.MethodText
