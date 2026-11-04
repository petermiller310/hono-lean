import HonoLean.Adapter.Lookup.Spec
import HonoLean.Adapter.Registration.Correctness

namespace HonoLean.Adapter.LookupText

private theorem lookup_ok_iff (router : Literal.Router) (request : TextRequest)
    (output : List Literal.Match) :
    lookup router request = .ok output ↔
      ∃ decoded, parseRequest request = .ok decoded ∧
        Literal.Router.lookup router decoded.1 decoded.2 = output := by
  cases parsed : parseRequest request with
  | error error => simp [lookup, parsed, bind, Except.bind]
  | ok decoded => simp [lookup, parsed, bind, pure, Except.bind, Except.pure]

/-- The public text lookup returns exactly the independent text-level rules
whenever the runtime router represents that ordered text table. -/
theorem lookup_iff {inputs : List TextRoute} {router : Literal.Router}
    (state : RegistrationText.StateDenotes inputs router)
    (request : TextRequest) (output : List Literal.Match) :
    lookup router request = .ok output ↔ Matches inputs request output := by
  obtain ⟨routes, table, represented⟩ := state
  rw [lookup_ok_iff]
  constructor
  · rintro ⟨decoded, parsed, found⟩
    exact ⟨routes, decoded, table, (RecordText.parseRequest_iff _ _).mp parsed,
      (Literal.Router.lookup_iff_rules represented _ _ _).mp found⟩
  · rintro ⟨actual, decoded, meaning, requestMeaning, rules⟩
    have same := ((BuildText.parseRoutes_iff inputs routes).mpr table).symm.trans
      ((BuildText.parseRoutes_iff inputs actual).mpr meaning)
    cases same
    exact ⟨decoded, (RecordText.parseRequest_iff _ _).mpr requestMeaning,
      (Literal.Router.lookup_iff_rules represented _ _ _).mpr rules⟩

theorem lookup_build_iff {inputs : List TextRoute} {router : Literal.Router}
    (built : build inputs = .ok router) (request : TextRequest) (output : List Literal.Match) :
    lookup router request = .ok output ↔ Matches inputs request output :=
  lookup_iff (RegistrationText.StateDenotes.of_build built) request output

/-- No runtime-result premise: text build followed by text lookup agrees with
the declarative rules in both directions, including all captures and order. -/
theorem build_lookup_iff (inputs : List TextRoute) (request : TextRequest)
    (output : List Literal.Match) :
    (∃ router, build inputs = .ok router ∧ lookup router request = .ok output) ↔
      Matches inputs request output := by
  constructor
  · rintro ⟨router, built, found⟩
    exact (lookup_build_iff built request output).mp found
  · rintro ⟨routes, decoded, table, requestMeaning, rules⟩
    have built := (BuildText.build_iff inputs (Literal.Router.build routes)).mpr
      ⟨routes, table, rfl⟩
    exact ⟨_, built, (lookup_build_iff built request output).mpr
      ⟨routes, decoded, table, requestMeaning, rules⟩⟩

/-- Every request in the independent grammar returns a successful match list,
possibly empty, for any runtime router. -/
theorem accepts_iff (router : Literal.Router) (request : TextRequest) :
    (∃ output, lookup router request = .ok output) ↔ RecordText.RequestSpelling request := by
  constructor
  · rintro ⟨output, found⟩
    obtain ⟨decoded, parsed, _⟩ := (lookup_ok_iff _ _ _).mp found
    exact (RecordText.request_accepts_iff request).mp ⟨decoded, parsed⟩
  · intro grammar
    obtain ⟨decoded, parsed⟩ := RecordText.request_complete grammar
    exact ⟨_, (lookup_ok_iff _ _ _).mpr ⟨decoded, parsed, rfl⟩⟩

theorem complete {inputs : List TextRoute} {request : TextRequest}
    (tableGrammar : BuildText.TableSpelling inputs)
    (requestGrammar : RecordText.RequestSpelling request) :
    ∃ router output, build inputs = .ok router ∧
      lookup router request = .ok output ∧ Matches inputs request output := by
  obtain ⟨router, built, _⟩ := BuildText.complete tableGrammar
  obtain ⟨output, found⟩ := (accepts_iff router request).mpr requestGrammar
  exact ⟨router, output, built, found, (lookup_build_iff built _ _).mp found⟩

theorem error_kind {router : Literal.Router} {request : TextRequest} {error : Error}
    (rejected : lookup router request = .error error) : error.kind = .invalidRequest := by
  cases parsed : parseRequest request with
  | error failure =>
    have same : failure = error := by
      simpa [lookup, parsed, bind, pure, Except.bind, Except.pure] using rejected
    cases same
    exact RecordText.request_error_kind parsed
  | ok decoded => simp [lookup, parsed, bind, pure, Except.bind, Except.pure] at rejected

theorem rejects_iff (router : Literal.Router) (request : TextRequest) :
    (∃ error, lookup router request = .error error ∧ error.kind = .invalidRequest) ↔
      ¬ RecordText.RequestSpelling request := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨output, found⟩ := (accepts_iff router request).mpr grammar
    rw [rejected] at found
    contradiction
  · intro outside
    cases found : lookup router request with
    | ok output => exact False.elim (outside ((accepts_iff _ _).mp ⟨output, found⟩))
    | error error => exact ⟨error, rfl, error_kind found⟩

/-- Arbitrary finite valid/invalid append histories establish the representation
needed for the same universal text-lookup guarantee. -/
theorem registrations_build_correct {initial : List TextRoute} {router : Literal.Router}
    (built : build initial = .ok router) (added : List TextRoute) :
    ∃ after, RegistrationText.TraceDenotes initial added after ∧
      (∀ request output,
        lookup (added.foldl (fun current input => (registerStep current input).1) router)
          request = .ok output ↔ Matches after request output) ∧
      (added.foldl (fun current input => (registerStep current input).1) router).nextOrdinal =
        after.length := by
  obtain ⟨after, trace, state⟩ :=
    RegistrationText.trace_correct (RegistrationText.StateDenotes.of_build built) added
  exact ⟨after, trace, lookup_iff state, state.nextOrdinal⟩

/-- info: 'HonoLean.Adapter.LookupText.build_lookup_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_lookup_iff

/-- info: 'HonoLean.Adapter.LookupText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

/-- info: 'HonoLean.Adapter.LookupText.registrations_build_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms registrations_build_correct

end HonoLean.Adapter.LookupText
