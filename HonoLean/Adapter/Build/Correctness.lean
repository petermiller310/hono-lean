import HonoLean.Adapter.Build.Spec
import HonoLean.Adapter.Record.Correctness
import HonoLean.Router.Correctness

namespace HonoLean.Adapter.BuildText

theorem TableDenotes.length_eq {inputs : List TextRoute} {routes : List Literal.Route}
    (meaning : TableDenotes inputs routes) : inputs.length = routes.length := by
  induction meaning with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

private theorem table_cons_iff (input : TextRoute) (inputs : List TextRoute)
    (route : Literal.Route) (routes : List Literal.Route) :
    TableDenotes (input :: inputs) (route :: routes) ↔
      RecordText.RouteDenotes input route ∧ TableDenotes inputs routes := by
  constructor
  · intro meaning; cases meaning with | cons head tail => exact ⟨head, tail⟩
  · rintro ⟨head, tail⟩; exact .cons head tail

private theorem mapM_cons_ok (input : TextRoute) (inputs : List TextRoute)
    (route : Literal.Route) (routes : List Literal.Route) :
    (input :: inputs).mapM parseRoute = .ok (route :: routes) ↔
      parseRoute input = .ok route ∧ inputs.mapM parseRoute = .ok routes := by
  rw [List.mapM_cons]
  cases parseRoute input <;> cases inputs.mapM parseRoute <;>
    simp [bind, pure, Except.bind, Except.pure]

/-- Parsing a table preserves every occurrence in its original position. -/
theorem parseRoutes_iff (inputs : List TextRoute) (routes : List Literal.Route) :
    inputs.mapM parseRoute = .ok routes ↔ TableDenotes inputs routes := by
  induction inputs generalizing routes with
  | nil =>
    cases routes with
    | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
    | cons route routes =>
      constructor
      · intro parsed; simp [pure, Except.pure] at parsed
      · intro meaning; cases meaning
  | cons input inputs ih =>
    cases routes with
    | nil =>
      constructor
      · intro parsed
        rw [List.mapM_cons] at parsed
        cases head : parseRoute input <;> cases tail : inputs.mapM parseRoute <;>
          simp_all [bind, pure, Except.bind, Except.pure]
      · intro meaning; cases meaning
    | cons route routes =>
      rw [mapM_cons_ok, table_cons_iff, RecordText.parseRoute_iff, ih]

/-- A successful text build is exactly the build of its ordered parsed table. -/
theorem build_iff (inputs : List TextRoute) (router : Literal.Router) :
    build inputs = .ok router ↔
      ∃ routes, TableDenotes inputs routes ∧ router = Literal.Router.build routes := by
  cases parsed : inputs.mapM parseRoute with
  | error error =>
    constructor
    · intro built; simp [build, parsed, Functor.map, Except.map] at built
    · rintro ⟨routes, meaning, _⟩
      have accepted := (parseRoutes_iff inputs routes).mpr meaning
      rw [parsed] at accepted
      contradiction
  | ok routes =>
    constructor
    · intro built
      have equal : Literal.Router.build routes = router := by
        simpa [build, parsed, Functor.map, Except.map] using built
      exact ⟨routes, (parseRoutes_iff inputs routes).mp parsed, equal.symm⟩
    · rintro ⟨actual, meaning, equal⟩
      have same := (parseRoutes_iff inputs actual).mpr meaning
      rw [parsed] at same
      cases same
      simp [build, parsed, equal, Functor.map, Except.map]

theorem represents {inputs : List TextRoute} {router : Literal.Router}
    (built : build inputs = .ok router) :
    ∃ routes, TableDenotes inputs routes ∧ Literal.Router.Represents router routes := by
  obtain ⟨routes, meaning, rfl⟩ := (build_iff inputs router).mp built
  exact ⟨routes, meaning, Literal.Router.build_represents routes⟩

theorem nextOrdinal {inputs : List TextRoute} {router : Literal.Router}
    (built : build inputs = .ok router) : router.nextOrdinal = inputs.length := by
  obtain ⟨routes, meaning, represented⟩ := represents built
  exact represented.2.trans meaning.length_eq.symm

theorem TableDenotes.spelling {inputs : List TextRoute} {routes : List Literal.Route}
    (meaning : TableDenotes inputs routes) : TableSpelling inputs := by
  induction meaning with
  | nil => simp [TableSpelling]
  | @cons input route inputs routes head _ ih =>
    intro actual member
    rcases List.mem_cons.mp member with equal | member
    · subst actual
      exact (RecordText.route_accepts_iff input).mp
        ⟨route, (RecordText.parseRoute_iff input route).mpr head⟩
    · exact ih actual member

/-- Grammar-only completeness constructs the entire ordered table. -/
theorem table_complete {inputs : List TextRoute} (grammar : TableSpelling inputs) :
    ∃ routes, TableDenotes inputs routes := by
  induction inputs with
  | nil => exact ⟨[], .nil⟩
  | cons input inputs ih =>
    obtain ⟨route, parsed⟩ := RecordText.route_complete (grammar input (by simp))
    obtain ⟨routes, meaning⟩ := ih (fun item member => grammar item (by simp [member]))
    exact ⟨route :: routes, .cons ((RecordText.parseRoute_iff input route).mp parsed) meaning⟩

theorem accepts_iff (inputs : List TextRoute) :
    (∃ router, build inputs = .ok router) ↔ TableSpelling inputs := by
  constructor
  · rintro ⟨router, built⟩
    obtain ⟨routes, meaning, _⟩ := (build_iff inputs router).mp built
    exact meaning.spelling
  · intro grammar
    obtain ⟨routes, meaning⟩ := table_complete grammar
    exact ⟨Literal.Router.build routes, (build_iff _ _).mpr ⟨routes, meaning, rfl⟩⟩

theorem complete {inputs : List TextRoute} (grammar : TableSpelling inputs) :
    ∃ router, build inputs = .ok router ∧ router.nextOrdinal = inputs.length := by
  obtain ⟨router, built⟩ := (accepts_iff inputs).mpr grammar
  exact ⟨router, built, nextOrdinal built⟩

private theorem parseRoutes_error_kind {inputs : List TextRoute} {error : Error}
    (rejected : inputs.mapM parseRoute = .error error) : error.kind = .invalidRoute := by
  induction inputs with
  | nil => simp [pure, Except.pure] at rejected
  | cons input inputs ih =>
    rw [List.mapM_cons] at rejected
    cases head : parseRoute input with
    | error failure =>
      have equal : failure = error := by
        simpa [head, bind, Except.bind] using rejected
      subst error
      exact RecordText.route_error_kind head
    | ok route =>
      cases tail : inputs.mapM parseRoute with
      | error failure =>
        have equal : failure = error := by
          simpa [head, tail, bind, Except.bind, pure, Except.pure] using rejected
        subst error
        exact ih tail
      | ok routes => simp [head, tail, bind, Except.bind, pure, Except.pure] at rejected

theorem error_kind {inputs : List TextRoute} {error : Error}
    (rejected : build inputs = .error error) : error.kind = .invalidRoute := by
  cases parsed : inputs.mapM parseRoute with
  | error failure =>
    have equal : failure = error := by
      simpa [build, parsed, Functor.map, Except.map] using rejected
    subst error
    exact parseRoutes_error_kind parsed
  | ok routes => simp [build, parsed, Functor.map, Except.map] at rejected

/-- An invalid table rejects as a whole, never as a partial successful build. -/
theorem rejects_iff (inputs : List TextRoute) :
    (∃ error, build inputs = .error error ∧ error.kind = .invalidRoute) ↔
      ¬ TableSpelling inputs := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨router, built⟩ := (accepts_iff inputs).mpr grammar
    rw [rejected] at built
    contradiction
  · intro outside
    cases built : build inputs with
    | ok router => exact False.elim (outside ((accepts_iff inputs).mp ⟨router, built⟩))
    | error error => exact ⟨error, rfl, error_kind built⟩

/-- info: 'HonoLean.Adapter.BuildText.build_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_iff

/-- info: 'HonoLean.Adapter.BuildText.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepts_iff

/-- info: 'HonoLean.Adapter.BuildText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

end HonoLean.Adapter.BuildText
