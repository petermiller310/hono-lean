import HonoLean.Adapter.Record.Correctness

namespace HonoLean.Adapter.RecordText
open Literal

/-- ALL selects every supported request method; labels are opaque data. -/
example : (match parseRoute ⟨"ALL", "/students/:id/*", "任意\n\"label\""⟩ with
    | .ok route =>
      (match route.selector with | .all => true | .exact _ => false) &&
      decide (route.path = [.literal "students", .parameter "id"]) &&
      route.suffix && route.handler == "任意\n\"label\""
    | .error _ => false) = true := by
  simp only [parseRoute, parsePattern, patternTexts, rootedPieces, String.toList_split_char]
  rfl

example : (match parseRoute ⟨"GET", "/", ""⟩ with
    | .ok route =>
      (match route.selector with | .all => false | .exact method => method.name == "GET") &&
      route.path.isEmpty && !route.suffix && route.handler.isEmpty
    | .error _ => false) = true := by rfl

example : (match parseRequest ⟨"HEAD", "/Students/S1"⟩ with
    | .ok (method, path) => method.name == "HEAD" && path == ["Students", "S1"]
    | .error _ => false) = true := by
  simp only [parseRequest, parsePath, String.toList_split_char]
  rfl

example : ([⟨"get", "/", ""⟩, ⟨"GET", "/:id/:id", "label"⟩,
    ⟨"ALL", "/a/*/b", "label"⟩] : List TextRoute).all (fun input =>
      match parseRoute input with
      | .error error => error.kind == .invalidRoute
      | .ok _ => false) = true := by
  simp only [parseRoute, parsePattern, patternTexts, rootedPieces, String.toList_split_char]
  rfl

example : ([⟨"ALL", "/"⟩, ⟨"GET", "/a/"⟩, ⟨" get", "/"⟩] : List TextRequest).all
    (fun input => match parseRequest input with
      | .error error => error.kind == .invalidRequest
      | .ok _ => false) = true := by
  simp only [parseRequest, parsePath, String.toList_split_char]
  rfl

end HonoLean.Adapter.RecordText
