import HonoLean.Adapter.Build.Correctness

namespace HonoLean.Adapter.BuildText

example : build [] = .ok Literal.Router.empty := rfl

private def input : TextRoute := ⟨"ALL", "/", ""⟩
private def root : Literal.Route := Literal.literalRoute .all [] ""

/-- Empty labels and identical routes remain two registration occurrences. -/
example : build [input, input] = .ok (Literal.Router.build [root, root]) := by
  apply (build_iff _ _).mpr
  refine ⟨[root, root], .cons ?_ (.cons ?_ .nil), rfl⟩ <;>
    exact (RecordText.parseRoute_iff input root).mp rfl

example : (match build [input, input] with
    | .ok router => router.nextOrdinal == 2
    | .error _ => false) = true := rfl

/-- An invalid registration in the middle cannot expose a partial build. -/
example : (match build [input, ⟨"get", "/", "bad"⟩, input] with
    | .error error => error.kind == .invalidRoute
    | .ok _ => false) = true := rfl

end HonoLean.Adapter.BuildText
