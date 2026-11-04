import HonoLean.Adapter.Registration.Spec
import HonoLean.Adapter.Build.Correctness

namespace HonoLean.Adapter.RegistrationText

private theorem table_append_one {before : List TextRoute} {routes : List Literal.Route}
    (table : BuildText.TableDenotes before routes)
    {input : TextRoute} {route : Literal.Route} (meaning : RecordText.RouteDenotes input route) :
    BuildText.TableDenotes (before ++ [input]) (routes ++ [route]) := by
  induction table with
  | nil => exact .cons meaning .nil
  | cons head _ ih => exact .cons head ih

theorem register_iff (router : Literal.Router) (input : TextRoute) (updated : Literal.Router) :
    register router input = .ok updated ↔
      ∃ route, RecordText.RouteDenotes input route ∧ updated = Literal.Router.register router route := by
  cases parsed : parseRoute input with
  | error error =>
    constructor
    · intro registered; simp [register, parsed, bind, Except.bind] at registered
    · rintro ⟨route, meaning, _⟩
      have accepted := (RecordText.parseRoute_iff input route).mpr meaning
      rw [parsed] at accepted
      contradiction
  | ok route =>
    constructor
    · intro registered
      have equal : Literal.Router.register router route = updated := by
        simpa [register, parsed, bind, pure, Except.bind, Except.pure] using registered
      exact ⟨route, (RecordText.parseRoute_iff input route).mp parsed, equal.symm⟩
    · rintro ⟨actual, meaning, equal⟩
      have same := (RecordText.parseRoute_iff input actual).mpr meaning
      rw [parsed] at same
      cases same
      simp [register, parsed, equal, bind, pure, Except.bind, Except.pure]

theorem accepts_iff (router : Literal.Router) (input : TextRoute) :
    (∃ updated, register router input = .ok updated) ↔ RecordText.RouteSpelling input := by
  constructor
  · rintro ⟨updated, registered⟩
    obtain ⟨route, meaning, _⟩ := (register_iff router input updated).mp registered
    exact (RecordText.route_accepts_iff input).mp
      ⟨route, (RecordText.parseRoute_iff input route).mpr meaning⟩
  · intro grammar
    obtain ⟨route, parsed⟩ := RecordText.route_complete grammar
    exact ⟨Literal.Router.register router route,
      (register_iff router input _).mpr
        ⟨route, (RecordText.parseRoute_iff input route).mp parsed, rfl⟩⟩

theorem error_kind {router : Literal.Router} {input : TextRoute} {error : Error}
    (rejected : register router input = .error error) : error.kind = .invalidRoute := by
  cases parsed : parseRoute input with
  | error failure =>
    have equal : failure = error := by
      simpa [register, parsed, bind, pure, Except.bind, Except.pure] using rejected
    cases equal
    exact RecordText.route_error_kind parsed
  | ok route => simp [register, parsed, bind, pure, Except.bind, Except.pure] at rejected

theorem rejects_iff (router : Literal.Router) (input : TextRoute) :
    (∃ error, register router input = .error error ∧ error.kind = .invalidRoute) ↔
      ¬ RecordText.RouteSpelling input := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨updated, registered⟩ := (accepts_iff router input).mpr grammar
    rw [rejected] at registered
    contradiction
  · intro outside
    cases registered : register router input with
    | ok updated => exact False.elim (outside ((accepts_iff router input).mp ⟨updated, registered⟩))
    | error error => exact ⟨error, rfl, error_kind registered⟩

theorem register_state {before : List TextRoute} {router updated : Literal.Router}
    (state : StateDenotes before router) {input : TextRoute}
    (registered : register router input = .ok updated) :
    StateDenotes (before ++ [input]) updated := by
  obtain ⟨routes, table, represented⟩ := state
  obtain ⟨route, meaning, rfl⟩ := (register_iff router input updated).mp registered
  exact ⟨routes ++ [route], table_append_one table meaning,
    Literal.Router.register_represents represented route⟩

theorem register_nextOrdinal {router updated : Literal.Router} {input : TextRoute}
    (registered : register router input = .ok updated) :
    updated.nextOrdinal = router.nextOrdinal + 1 := by
  obtain ⟨route, _, rfl⟩ := (register_iff router input updated).mp registered
  rfl

theorem StateDenotes.of_build {inputs : List TextRoute} {router : Literal.Router}
    (built : build inputs = .ok router) : StateDenotes inputs router :=
  BuildText.represents built

theorem StateDenotes.nextOrdinal {inputs : List TextRoute} {router : Literal.Router}
    (state : StateDenotes inputs router) : router.nextOrdinal = inputs.length := by
  obtain ⟨routes, table, represented⟩ := state
  exact represented.2.trans table.length_eq.symm

theorem step_success {router updated : Literal.Router} {input : TextRoute}
    (registered : register router input = .ok updated) :
    registerStep router input = (updated, .ok router.nextOrdinal) := by
  simp [registerStep, registered]

/-- Rejection preserves the exact runtime value, not only its model table. -/
theorem step_failure {router : Literal.Router} {input : TextRoute} {error : Error}
    (rejected : register router input = .error error) :
    registerStep router input = (router, .error error) := by
  simp [registerStep, rejected]

theorem rejected_keeps {router : Literal.Router} {input : TextRoute}
    (outside : ¬ RecordText.RouteSpelling input) :
    (registerStep router input).1 = router ∧
      ∃ error, (registerStep router input).2 = .error error ∧ error.kind = .invalidRoute := by
  obtain ⟨error, rejected, category⟩ := (rejects_iff router input).mpr outside
  rw [step_failure rejected]
  exact ⟨rfl, error, rfl, category⟩

/-- The concrete total step obeys the independent accept/reject rules and
preserves the text-table representation in both cases. -/
theorem step_correct {before : List TextRoute} {router : Literal.Router}
    (state : StateDenotes before router) (input : TextRoute) :
    ∃ after, StepDenotes before input after (registerStep router input).2 ∧
      StateDenotes after (registerStep router input).1 := by
  cases registered : register router input with
  | error error =>
    rw [step_failure registered]
    have outside := (rejects_iff router input).mp ⟨error, registered, error_kind registered⟩
    exact ⟨before, .rejected outside (error_kind registered), state⟩
  | ok updated =>
    rw [step_success registered]
    have grammar := (accepts_iff router input).mp ⟨updated, registered⟩
    refine ⟨before ++ [input], ?_, register_state state registered⟩
    simpa only [state.nextOrdinal] using (StepDenotes.accepted (before := before) grammar)

private theorem trace_cons {before middle after : List TextRoute} {input : TextRoute}
    {outcome : Except Error Nat} {rest : List TextRoute}
    (step : StepDenotes before input middle outcome) (tail : TraceDenotes middle rest after) :
    TraceDenotes before (input :: rest) after := by
  cases step with
  | accepted grammar => exact .accepted grammar tail
  | rejected outside _ => exact .rejected outside tail

/-- Any finite sequence of the same total registration step retains exactly
the grammar-valid occurrences, and the final counter is their table length. -/
theorem trace_correct {before : List TextRoute} {router : Literal.Router}
    (state : StateDenotes before router) (inputs : List TextRoute) :
    ∃ after, TraceDenotes before inputs after ∧
      StateDenotes after
        (inputs.foldl (fun current input => (registerStep current input).1) router) := by
  induction inputs generalizing before router with
  | nil => exact ⟨before, .nil, state⟩
  | cons input inputs ih =>
    obtain ⟨middle, step, middleState⟩ := step_correct state input
    obtain ⟨after, trace, finalState⟩ := ih middleState
    exact ⟨after, trace_cons step trace, finalState⟩

/-- info: 'HonoLean.Adapter.RegistrationText.register_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms register_iff

/-- info: 'HonoLean.Adapter.RegistrationText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

/-- info: 'HonoLean.Adapter.RegistrationText.step_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_correct

/-- info: 'HonoLean.Adapter.RegistrationText.trace_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_correct

end HonoLean.Adapter.RegistrationText
