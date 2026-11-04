import HonoLean.Adapter.Path.Correctness

namespace HonoLean.Adapter.PathText

example : parsePath "/" = .ok [] := by rfl

example : parsePath "/students/A-0_b" = .ok ["students", "A-0_b"] := by
  apply complete
  constructor
  · simp [Segment, Character]
  · rfl

/-- Capitalization and leading zeroes are preserved in the returned segments. -/
example : parsePath "/GET/007" = .ok ["GET", "007"] := by
  apply complete
  constructor
  · simp [Segment, Character]
  · rfl

/-- Evaluate the real parser through the standard split-character theorem.
These examples complement the universal theorem; they do not replace it. -/
example : ["", "students", "//", "/a/", "/a//b", "/a.b", "/a/..",
    "/café", "/%61", "/a?b", "/a#b", " /a", "/a ", "/:id", "/*",
    "https://example.com/a"].all (fun text =>
      match parsePath text with
      | .error error => error.kind == .invalidRequest
      | .ok _ => false) = true := by
  simp only [parsePath, String.toList_split_char]
  rfl

end HonoLean.Adapter.PathText
