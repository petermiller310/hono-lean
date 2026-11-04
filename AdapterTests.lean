import HonoLean.Adapter.Json

open HonoLean Literal Adapter Lean

def need {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let opaqueLabel := "任意\n\"label\""
  let allRecord ← need (parseRoute ⟨"ALL", "/students/:id/*", opaqueLabel⟩)
  ensure ((match allRecord.selector with | .all => true | .exact _ => false) &&
    allRecord.path == [.literal "students", .parameter "id"] &&
    allRecord.suffix && allRecord.handler == opaqueLabel) "Route record changed a field"
  let (headMethod, headPath) ← need (parseRequest ⟨"HEAD", "/Students/S1"⟩)
  ensure (headMethod.name == "HEAD" && headPath == ["Students", "S1"])
    "Request record changed a field"
  let patterns : List (String × List Component × Bool) := [
    ("/", [], false), ("*", [], true), ("/*", [], true),
    ("/a", [.literal "a"], false),
    ("/students/:id/*", [.literal "students", .parameter "id"], true),
    ("/:id/:ID", [.parameter "id", .parameter "ID"], false),
    ("/:__proto__/:constructor/*", [.parameter "__proto__", .parameter "constructor"], true)]
  for (text, components, suffix) in patterns do
    let parsed ← need (parsePattern text)
    ensure (parsed.path == components && parsed.suffix == suffix)
      "Pattern parser changed components or wildcard flag"
  for text in ["", "a", "//", "/a/", "/a//b", "/a/*/b", "/a/*/*", "/a/**",
      "/a*", "/:id/:id", "/:1id", "/:", "/:id?", "/:id{a}", "/a.b",
      "/a%20b", "/café", " /a"] do
    match parsePattern text with
    | .ok _ => throw (IO.userError s!"Invalid pattern accepted: {text}")
    | .error error => ensure (error.kind == .invalidRoute) "Wrong pattern error category"
  for kind in [ErrorKind.invalidRequest, .invalidRoute, .invalidInput] do
    for text in ["A", "Z", "GET", "HEAD", "OPTIONS", "PURGE", "CUSTOM", "ALLA"] do
      let actual ← need (parseMethod kind text)
      ensure (actual.name == text) "Method parser changed exact spelling"
    for text in ["", "ALL", "get", "Get", " GET", "GET ", "G3T", "M-SEARCH",
        "@", "[", "GÉT", "ＧＥＴ", "G\nET"] do
      match parseMethod kind text with
      | .ok _ => throw (IO.userError s!"Invalid method accepted: {text}")
      | .error error => ensure (error.kind == kind) "Wrong method error category"
  for (text, expected) in [("/", []), ("/students/A-0_b", ["students", "A-0_b"]),
      ("/GET/007", ["GET", "007"])] do
    let actual ← need (parsePath text)
    ensure (actual == expected) "Path parser changed canonical segments"
  for text in ["", "students", "//", "/a/", "/a//b", "/a.b", "/a/..",
      "/café", "/%61", "/a?b", "/a#b", " /a", "/a ", "/:id", "/*",
      "https://example.com/a"] do
    match parsePath text with
    | .ok _ => throw (IO.userError s!"Invalid request path accepted: {text}")
    | .error error => ensure (error.kind == .invalidRequest) "Wrong path error category"
  let read : TextRoute := ⟨"GET", "/students/:id", "read"⟩
  let old ← need (Adapter.build [read])
  let retained ← need (Adapter.lookup old ⟨"GET", "/students/s1"⟩)
  let bad : TextRoute := ⟨"GET", "/:id/:id", "bad"⟩
  let (kept, rejectedStep) := registerStep old bad
  match rejectedStep with
  | .ok _ => throw (IO.userError "Invalid total registration step succeeded")
  | .error error => ensure (error.kind == .invalidRoute) "Wrong step rejection category"
  let keptResult ← need (Adapter.lookup kept ⟨"GET", "/students/s1"⟩)
  ensure (kept.nextOrdinal == old.nextOrdinal && keptResult == retained)
    "Rejected total step changed the prior router"
  let (advanced, acceptedStep) := registerStep kept ⟨"ALL", "/students/*", "log"⟩
  let assigned ← need acceptedStep
  ensure (assigned == 1 && advanced.nextOrdinal == 2)
    "Total step consumed the wrong ordinal"
  match Adapter.register old bad with
  | .ok _ => throw (IO.userError "Invalid registration succeeded")
  | .error error => ensure (error.kind == .invalidRoute) "Wrong registration category"
  match Adapter.build [read, bad] with
  | .ok _ => throw (IO.userError "Invalid build exposed a partial router")
  | .error error => ensure (error.kind == .invalidRoute) "Wrong build category"
  let updated ← need (Adapter.register old ⟨"ALL", "/students/*", "log"⟩)
  let actual ← need (Adapter.lookup updated ⟨"GET", "/students/s2"⟩)
  ensure (decide (actual = [
    {registration := 0, handler := "read", params := [("id", "s2")]},
    {registration := 1, handler := "log"}])) "Failed registration consumed an ordinal"
  let oldAgain ← need (Adapter.lookup old ⟨"GET", "/students/s1"⟩)
  ensure (old.nextOrdinal == 1 && updated.nextOrdinal == 2 && oldAgain == retained)
    "Old router or retained capture changed"
  ensure (decide (retained = [{registration := 0, handler := "read", params := [("id", "s1")]}]))
    "Retained value changed after later request"
  let miss ← need (Adapter.lookup old ⟨"GET", "/missing"⟩)
  ensure miss.isEmpty "Valid miss must succeed with an empty list"
  match Adapter.lookup old ⟨"GET", "/students/"⟩ with
  | .ok _ => throw (IO.userError "Invalid request treated as a successful miss")
  | .error error => ensure (error.kind == .invalidRequest) "Wrong request category"
  let parsed ← need (parseRoute ⟨"PURGE", "/grade_2/:student_id/*", "任意\n\"label\""⟩)
  ensure (decide (parsed.path = [.literal "grade_2", .parameter "student_id"]) &&
    parsed.suffix && parsed.handler == "任意\n\"label\"") "Text parsing altered route data"
  let bare ← need (parseRoute ⟨"GET", "*", ""⟩)
  let slash ← need (parseRoute ⟨"GET", "/*", ""⟩)
  ensure (bare.path.isEmpty && slash.path.isEmpty && bare.suffix && slash.suffix)
    "Global aliases do not produce the empty-prefix suffix route"
  IO.println "Direct adapter checks passed: method/path/pattern grammars, atomic failure, retained versions/results, parse shape, aliases and error distinction."
