import HonoLean.Adapter.Method.Correctness

namespace HonoLean.Adapter.MethodText

/-- Completeness constructs the typed result from the grammar alone. -/
example : ∃ method, parseMethod .invalidRequest "PURGE" = .ok method ∧
    method.name = "PURGE" :=
  complete .invalidRequest (by simp [Spelling, Character])

example : ∃ method, parseMethod .invalidRequest "ALLA" = .ok method ∧
    method.name = "ALLA" :=
  complete .invalidRequest (by simp [Spelling, Character])

/-- Exercise the real parser and exact spellings, including custom methods. -/
example : ["A", "Z", "GET", "HEAD", "OPTIONS", "PURGE", "CUSTOM", "ALLA"].all
    (fun text => match parseMethod .invalidRequest text with
      | .ok method => method.name == text
      | .error _ => false) = true := by rfl

/-- ALL is a route selector, not a request method. Errors retain the supplied
category, including when the helper is used to parse an exact route method. -/
example : [ErrorKind.invalidRequest, .invalidRoute, .invalidInput].all (fun kind =>
    ["", "ALL", "get", "Get", " GET", "GET ", "G3T", "M-SEARCH", "@", "[",
      "GÉT", "ＧＥＴ", "G\nET"].all (fun text =>
        match parseMethod kind text with
        | .error error => error.kind == kind
        | .ok _ => false)) = true := by rfl

end HonoLean.Adapter.MethodText
