import HonoLean.Adapter.Pattern.Correctness

namespace HonoLean.Adapter.PatternText
open Literal

/-- A concrete inhabitant of the independent grammar, including a named prefix
and a terminal wildcard. -/
example : Denotes "/students/:id/*" [.literal "students", .parameter "id"] true := by
  constructor
  · refine ⟨["students", ":id", "*"], ?_, Or.inl rfl⟩
    apply Pieces.component (item := .literal "students")
    · exact ⟨rfl, by simp [PathText.Segment, PathText.Character]⟩
    apply Pieces.component (item := .parameter "id")
    · exact ⟨rfl, by simp [Name, NameStart]⟩
    exact .wildcard
  · simp [parameterNames]

private def shape (text : String) : Option (List Component × Bool) :=
  match parsePattern text with
  | .ok parsed => some (parsed.path, parsed.suffix)
  | .error _ => none

example : shape "/" = some ([], false) ∧ shape "*" = some ([], true) ∧
    shape "/*" = some ([], true) := by
  simp only [shape, parsePattern, patternTexts, rootedPieces, String.toList_split_char]
  exact ⟨rfl, rfl, rfl⟩

example : shape "/students/:id/*" = some ([.literal "students", .parameter "id"], true) := by
  simp only [shape, parsePattern, patternTexts, rootedPieces, String.toList_split_char]
  rfl

example : ["", "a", "//", "/a/", "/a//b", "/a/*/b", "/a/*/*", "/a/**",
    "/a*", "/:id/:id", "/:1id", "/:", "/:id?", "/:id{a}", "/a.b",
    "/a%20b", "/café", " /a"].all (fun text =>
      match parsePattern text with
      | .error error => error.kind == .invalidRoute
      | .ok _ => false) = true := by
  simp only [parsePattern, patternTexts, rootedPieces, String.toList_split_char]
  rfl

end HonoLean.Adapter.PatternText
