import HonoLean.Adapter.Registration.Correctness

namespace HonoLean.Adapter.RegistrationText
open Literal

private def bad : TextRoute := ⟨"get", "/", ""⟩
private def good : TextRoute := ⟨"ALL", "/", ""⟩
private def rejected := registerStep Router.empty bad
private def first := registerStep rejected.1 good
private def duplicate := registerStep first.1 good

/-- The failed append returns the actual input router, and the next valid
registration still gets zero. Repeating it appends a distinct occurrence. -/
example : rejected.1 = Router.empty ∧ first.2 = .ok 0 ∧ duplicate.2 = .ok 1 ∧
    duplicate.1.nextOrdinal = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The failed step reports the route category rather than succeeding empty. -/
example : (match rejected.2 with
    | .error error => error.kind == .invalidRoute
    | .ok _ => false) = true := by rfl

/-- A saved old router remains its original value after constructing new ones. -/
example : Router.empty.nextOrdinal = 0 ∧ first.1.nextOrdinal = 1 :=
  ⟨rfl, rfl⟩

example (inputs : List TextRoute) :
    ∃ after, TraceDenotes [] inputs after ∧
      (inputs.foldl (fun router input => (registerStep router input).1) Router.empty).nextOrdinal =
        after.length := by
  have empty : StateDenotes [] Router.empty :=
    ⟨[], .nil, Router.empty_represents⟩
  obtain ⟨after, trace, state⟩ := trace_correct empty inputs
  exact ⟨after, trace, state.nextOrdinal⟩

end HonoLean.Adapter.RegistrationText
