import HonoLean.Router.Correctness
import HonoLean.Literal.Examples

namespace HonoLean.Literal

def registrationRead : Route :=
  {selector := .exact getMethod, path := [.literal "students", .parameter "id"],
    handler := "read", valid := by decide +kernel}

def registrationWrite : Route :=
  {registrationRead with selector := .exact postMethod, handler := "write"}

def registrationLog : Route :=
  {literalRoute .all ["students"] "log" with suffix := true}

def registrationInitial : List Route := [
  literalRoute (.exact postMethod) ["unrelated"] "before", registrationRead
]

structure RegistrationExample where
  label : String
  initial : List Route := registrationInitial
  added : List Route := []
  method : Method := getMethod
  path : Path := ["students", "s1"]
  expected : List Match

def registrationExamples : List RegistrationExample := [
  {label := "Empty router", initial := [], expected := []},
  {label := "Initial build counts a nonmatching registration", expected := [
    {registration := 1, handler := "read", params := [("id", "s1")]}
  ]},
  {label := "Lookup miss", path := ["missing"], expected := []},
  {label := "Append ALL wildcard", added := [registrationLog], expected := [
    {registration := 1, handler := "read", params := [("id", "s1")]},
    {registration := 2, handler := "log"}
  ]},
  {label := "Append POST after wildcard", added := [registrationLog, registrationWrite],
    method := postMethod, expected := [
      {registration := 2, handler := "log"},
      {registration := 3, handler := "write", params := [("id", "s1")]}
    ]},
  {label := "Append a duplicate", added := [registrationLog, registrationRead], expected := [
    {registration := 1, handler := "read", params := [("id", "s1")]},
    {registration := 2, handler := "log"},
    {registration := 3, handler := "read", params := [("id", "s1")]}
  ]},
  {label := "Wildcard accepts empty suffix", added := [registrationLog], path := ["students"],
    expected := [{registration := 2, handler := "log"}]},
  {label := "Wildcard accepts longer suffix", added := [registrationLog],
    path := ["students", "s1", "worksheets"], expected := [{registration := 2, handler := "log"}]},
  {label := "HEAD matches appended ALL", added := [registrationLog], method := headMethod,
    expected := [{registration := 2, handler := "log"}]},
  {label := "Special name remains string data", initial := [], path := ["alpha", "suffix"],
    added := [
      {selector := .exact getMethod, path := [.parameter "__proto__"], suffix := true,
        handler := "key", valid := by decide +kernel}
    ],
    expected := [{registration := 0, handler := "key", params := [("__proto__", "alpha")]}]},
  {label := "Empty handler label is preserved", initial := [], path := [],
    added := [{literalRoute .all [] "global" with suffix := true},
      literalRoute (.exact getMethod) [] ""], expected := [
      {registration := 0, handler := "global"}, {registration := 1, handler := ""}
    ]},
  {label := "Appended shape keeps its own name", added := [
    {selector := .exact getMethod, path := [.literal "students", .parameter "studentId"],
      handler := "other", valid := by decide +kernel}
  ], expected := [
    {registration := 1, handler := "read", params := [("id", "s1")]},
    {registration := 2, handler := "other", params := [("studentId", "s1")]}
  ]}
]

theorem registration_regression_examples :
    registrationExamples.all (fun item => decide
      (Router.lookup (Router.registerMany (Router.build item.initial) item.added)
        item.method item.path = item.expected)) = true := by
  simp only [Router.lookup_registerMany_build]
  decide +kernel

def runRegistrationExamples : IO Unit := do
  for item in registrationExamples do
    let router := Router.registerMany (Router.build item.initial) item.added
    let actual := Router.lookup router item.method item.path
    if actual ≠ item.expected ∨ router.nextOrdinal ≠ item.initial.length + item.added.length then
      throw (IO.userError s!"Unexpected registration result: {item.label}")
    IO.println s!"{item.label}: {reprStr actual}"

/-- Keep real old router and result values across later requests and registrations. -/
def runRegistrationSequence : IO Unit := do
  let original := Router.build [registrationRead]
  let retained := Router.lookup original getMethod ["students", "s1"]
  let second := Router.lookup original getMethod ["students", "s2"]
  let missing := Router.lookup original getMethod ["missing"]
  let withPost := Router.register original registrationWrite
  let withDuplicate := Router.register withPost registrationRead
  let fork := Router.register original registrationLog
  let expectedRetained : List Match := [
    {registration := 0, handler := "read", params := [("id", "s1")]}
  ]
  let expectedSecond : List Match := [
    {registration := 0, handler := "read", params := [("id", "s2")]}
  ]
  let expectedPost : List Match := [
    {registration := 1, handler := "write", params := [("id", "s3")]}
  ]
  let expectedDuplicates : List Match := [
    {registration := 0, handler := "read", params := [("id", "s4")]},
    {registration := 2, handler := "read", params := [("id", "s4")]}
  ]
  let expectedFork := expectedRetained ++ [{registration := 1, handler := "log"}]
  if retained ≠ expectedRetained ∨ second ≠ expectedSecond ∨ missing ≠ [] ∨
      Router.lookup original getMethod ["students", "s1"] ≠ expectedRetained ∨
      Router.lookup original postMethod ["students", "s3"] ≠ [] ∨
      Router.lookup withPost postMethod ["students", "s3"] ≠ expectedPost ∨
      Router.lookup withPost getMethod ["students", "s1"] ≠ expectedRetained ∨
      Router.lookup withDuplicate getMethod ["students", "s4"] ≠ expectedDuplicates ∨
      Router.lookup fork getMethod ["students", "s1"] ≠ expectedFork ∨
      original.nextOrdinal ≠ 1 ∨ withPost.nextOrdinal ≠ 2 ∨
      withDuplicate.nextOrdinal ≠ 3 ∨ fork.nextOrdinal ≠ 2 then
    throw (IO.userError "Registration sequence, retained result, or independent fork changed")
  IO.println "Interleaved requests, retained result, old versions, duplicate append, and fork: passed"

end HonoLean.Literal
