import HonoLean.Literal.Correctness

namespace HonoLean.Literal

def getMethod : Method := ⟨"GET", by decide +kernel⟩
def postMethod : Method := ⟨"POST", by decide +kernel⟩
def headMethod : Method := ⟨"HEAD", by decide +kernel⟩
def optionsMethod : Method := ⟨"OPTIONS", by decide +kernel⟩
def purgeMethod : Method := ⟨"PURGE", by decide +kernel⟩

example : ¬ ValidMethod "" := by decide +kernel
example : ¬ ValidMethod "get" := by decide +kernel
example : ¬ ValidMethod "ALL" := by decide +kernel
example : ¬ ValidMethod "GÉT" := by decide +kernel
example : ¬ ValidMethod "M-SEARCH" := by decide +kernel

def exampleRoutes : List Route := [
  literalRoute (.all) ["unrelated"] "before",
  literalRoute (.all) ["students", "new"] "same",
  literalRoute (.all) [] "root",
  literalRoute (.all) ["students"] "listStudents",
  literalRoute (.all) ["elsewhere"] "between",
  literalRoute (.all) ["students", "new"] "same",
  literalRoute (.all) ["students", "new"] ""
]

structure Example where
  label : String
  method : Method := getMethod
  path : Path
  expected : List Match

def examples : List Example := [
  {label := "Exact path", path := ["students", "new"], expected := [
    {registration := 1, handler := "same"},
    {registration := 5, handler := "same"},
    {registration := 6, handler := ""}
  ]},
  {label := "Root", path := [], expected := [{registration := 2, handler := "root"}]},
  {label := "Parent path", path := ["students"],
    expected := [{registration := 3, handler := "listStudents"}]},
  {label := "Extra segment", path := ["students", "new", "extra"], expected := []},
  {label := "Missing path", path := ["missing"], expected := []},
  {label := "Case-sensitive", path := ["students", "New"], expected := []}
]

theorem regression_examples :
    examples.all (fun item =>
      decide (referenceLookup exampleRoutes item.method item.path = item.expected) &&
      decide (Trie.lookup (Trie.build exampleRoutes) item.method item.path = item.expected)) = true := by
  simp only [Trie.lookup_build]
  decide +kernel

example : Trie.lookup (Trie.build []) getMethod [] = [] := by decide +kernel

def methodRoutes : List Route := [
  literalRoute (.exact postMethod) ["students"] "write",
  literalRoute (.all) ["students"] "same",
  literalRoute (.exact getMethod) ["students"] "same",
  literalRoute (.exact purgeMethod) ["students"] "purge",
  literalRoute (.all) ["students"] "same",
  literalRoute (.exact getMethod) ["students"] "",
  literalRoute (.exact headMethod) ["students"] "head",
  literalRoute (.exact getMethod) ["get-only"] "only",
  literalRoute (.all) [] "rootAll",
  literalRoute (.exact getMethod) [] "rootGet"
]

def methodExamples : List Example := [
  {label := "GET /students", path := ["students"], expected := [
    {registration := 1, handler := "same"}, {registration := 2, handler := "same"},
    {registration := 4, handler := "same"}, {registration := 5, handler := ""}
  ]},
  {label := "POST /students", method := postMethod, path := ["students"], expected := [
    {registration := 0, handler := "write"}, {registration := 1, handler := "same"},
    {registration := 4, handler := "same"}
  ]},
  {label := "HEAD /students", method := headMethod, path := ["students"], expected := [
    {registration := 1, handler := "same"}, {registration := 4, handler := "same"},
    {registration := 6, handler := "head"}
  ]},
  {label := "OPTIONS /students", method := optionsMethod, path := ["students"], expected := [
    {registration := 1, handler := "same"}, {registration := 4, handler := "same"}
  ]},
  {label := "PURGE /students", method := purgeMethod, path := ["students"], expected := [
    {registration := 1, handler := "same"}, {registration := 3, handler := "purge"},
    {registration := 4, handler := "same"}
  ]},
  {label := "HEAD /get-only", method := headMethod, path := ["get-only"], expected := []},
  {label := "GET /", path := [], expected := [
    {registration := 8, handler := "rootAll"}, {registration := 9, handler := "rootGet"}
  ]},
  {label := "HEAD /", method := headMethod, path := [], expected := [
    {registration := 8, handler := "rootAll"}
  ]},
  {label := "GET /students/extra", path := ["students", "extra"], expected := []},
  {label := "GET /missing", path := ["missing"], expected := []},
  {label := "GET /students again", path := ["students"], expected := [
    {registration := 1, handler := "same"}, {registration := 2, handler := "same"},
    {registration := 4, handler := "same"}, {registration := 5, handler := ""}
  ]}
]

theorem method_regression_examples :
    methodExamples.all (fun item =>
      decide (referenceLookup methodRoutes item.method item.path = item.expected) &&
      decide (Trie.lookup (Trie.build methodRoutes) item.method item.path = item.expected)) = true := by
  simp only [Trie.lookup_build]
  decide +kernel

example : validName "__proto__" = true := by decide +kernel
example : validName "constructor" = true := by decide +kernel
example : validName "student_id2" = true := by decide +kernel
example : validName "" = false := by decide +kernel
example : validName "1id" = false := by decide +kernel
example : validName "student-id" = false := by decide +kernel
example : validName "íd" = false := by decide +kernel
example : ¬ ValidPattern [.parameter "id", .parameter "id"] := by decide +kernel

example : SameParams [("a", "1"), ("b", "2")] [("b", "2"), ("a", "1")] := by
  apply params_permutation_same_map (by decide +kernel) (by decide +kernel)
  exact List.Perm.swap ..

def parameterRoutes : List Route := [
  literalRoute (.exact getMethod) ["students", "new"] "literal",
  {selector := .exact getMethod, path := [.parameter "kind", .parameter "id"],
    handler := "general", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "studentId"],
    handler := "student", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "id"],
    handler := "short", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "studentId"],
    handler := "student", valid := by decide +kernel},
  {selector := .all, path := [.literal "students", .parameter "__proto__"],
    handler := "key", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "constructor"],
    handler := "", valid := by decide +kernel},
  {selector := .exact postMethod, path := [.literal "students", .parameter "id"],
    handler := "write", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "studentId",
      .literal "worksheets", .parameter "worksheetId"],
    handler := "worksheet", valid := by decide +kernel},
  literalRoute .all [] "root",
  {selector := .exact getMethod, path := [.parameter "one"], handler := "one", valid := by decide +kernel}
]

def studentMatches (id : String) : List Match := [
  {registration := 1, handler := "general", params := [("kind", "students"), ("id", id)]},
  {registration := 2, handler := "student", params := [("studentId", id)]},
  {registration := 3, handler := "short", params := [("id", id)]},
  {registration := 4, handler := "student", params := [("studentId", id)]},
  {registration := 5, handler := "key", params := [("__proto__", id)]},
  {registration := 6, handler := "", params := [("constructor", id)]}
]

def parameterExamples : List Example := [
  {label := "GET /students/new: literal and parameters", path := ["students", "new"],
    expected := {registration := 0, handler := "literal"} :: studentMatches "new"},
  {label := "GET /students/s1: branch-local names", path := ["students", "s1"], expected := studentMatches "s1"},
  {label := "POST /students/s1", method := postMethod, path := ["students", "s1"], expected := [
    {registration := 5, handler := "key", params := [("__proto__", "s1")]},
    {registration := 7, handler := "write", params := [("id", "s1")]}
  ]},
  {label := "HEAD /students/s1: ALL only", method := headMethod, path := ["students", "s1"],
    expected := [{registration := 5, handler := "key", params := [("__proto__", "s1")]}]},
  {label := "GET /students/s1/worksheets/w2", path := ["students", "s1", "worksheets", "w2"], expected := [
    {registration := 8, handler := "worksheet", params := [("studentId", "s1"), ("worksheetId", "w2")]}
  ]},
  {label := "GET /: no empty capture", path := [], expected := [{registration := 9, handler := "root"}]},
  {label := "GET /students: one segment", path := ["students"],
    expected := [{registration := 10, handler := "one", params := [("one", "students")]}]},
  {label := "GET /students/empty: reject empty capture", path := ["students", ""], expected := []},
  {label := "GET /empty/new: reject empty first capture", path := ["", "new"], expected := []},
  {label := "GET /students/s1/extra: exact length", path := ["students", "s1", "extra"], expected := []},
  {label := "GET /students/s2: fresh values", path := ["students", "s2"], expected := studentMatches "s2"},
  {label := "GET /students/s1 again", path := ["students", "s1"], expected := studentMatches "s1"}
]

theorem parameter_regression_examples :
    parameterExamples.all (fun item =>
      decide (referenceLookup parameterRoutes item.method item.path = item.expected) &&
      decide (Trie.lookup (Trie.build parameterRoutes) item.method item.path = item.expected)) = true := by
  simp only [Trie.lookup_build]
  decide +kernel

/-- The empty-prefix suffix route is the parsed form shared by `*` and `/*`. -/
def wildcardRoutes : List Route := [
  literalRoute (.exact getMethod) ["students"] "students",
  {literalRoute (.exact getMethod) ["students"] "student-tree" with suffix := true},
  {selector := .exact getMethod, path := [.literal "students", .parameter "id"],
    handler := "student", valid := by decide +kernel},
  {selector := .all, path := [.literal "students", .parameter "id"], suffix := true,
    handler := "student-suffix", valid := by decide +kernel},
  literalRoute (.exact getMethod) ["students", "new"] "new",
  {literalRoute .all [] "global" with suffix := true},
  {literalRoute (.exact getMethod) ["students"] "student-tree" with suffix := true},
  {literalRoute (.exact postMethod) ["students"] "write" with suffix := true},
  {literalRoute .all [] "global" with suffix := true},
  literalRoute (.exact getMethod) [] "root",
  {selector := .exact getMethod, path := [.parameter "kind", .literal "new"], suffix := true,
    handler := "kind-suffix", valid := by decide +kernel},
  {selector := .exact getMethod, path := [.literal "students", .parameter "id",
      .literal "worksheets", .parameter "worksheetId"], suffix := true,
    handler := "worksheet-suffix", valid := by decide +kernel}
]

def globalMatches : List Match := [
  {registration := 5, handler := "global"}, {registration := 8, handler := "global"}
]

def deepStudentMatches (id : String) : List Match := [
  {registration := 1, handler := "student-tree"},
  {registration := 3, handler := "student-suffix", params := [("id", id)]},
  {registration := 5, handler := "global"},
  {registration := 6, handler := "student-tree"},
  {registration := 8, handler := "global"}
]

def wildcardExamples : List Example := [
  {label := "GET /: global wildcard includes root", path := [], expected :=
    globalMatches ++ [{registration := 9, handler := "root"}]},
  {label := "GET /students: empty suffix", path := ["students"], expected := [
    {registration := 0, handler := "students"}, {registration := 1, handler := "student-tree"},
    {registration := 5, handler := "global"}, {registration := 6, handler := "student-tree"},
    {registration := 8, handler := "global"}
  ]},
  {label := "GET /students/new: all overlapping routes", path := ["students", "new"], expected := [
    {registration := 1, handler := "student-tree"},
    {registration := 2, handler := "student", params := [("id", "new")]},
    {registration := 3, handler := "student-suffix", params := [("id", "new")]},
    {registration := 4, handler := "new"}, {registration := 5, handler := "global"},
    {registration := 6, handler := "student-tree"}, {registration := 8, handler := "global"},
    {registration := 10, handler := "kind-suffix", params := [("kind", "students")]}
  ]},
  {label := "GET /students/s1: parameter before empty suffix", path := ["students", "s1"], expected := [
    {registration := 1, handler := "student-tree"},
    {registration := 2, handler := "student", params := [("id", "s1")]},
    {registration := 3, handler := "student-suffix", params := [("id", "s1")]},
    {registration := 5, handler := "global"}, {registration := 6, handler := "student-tree"},
    {registration := 8, handler := "global"}
  ]},
  {label := "GET /students/s1/a/b/c: each wildcard once", path := ["students", "s1", "a", "b", "c"],
    expected := deepStudentMatches "s1"},
  {label := "GET /students/new/extra: exact route stops", path := ["students", "new", "extra"],
    expected := deepStudentMatches "new" ++ [
      {registration := 10, handler := "kind-suffix", params := [("kind", "students")]}
    ]},
  {label := "POST /students/s1/extra: methods still apply", method := postMethod,
    path := ["students", "s1", "extra"], expected := [
      {registration := 3, handler := "student-suffix", params := [("id", "s1")]},
      {registration := 5, handler := "global"}, {registration := 7, handler := "write"},
      {registration := 8, handler := "global"}
    ]},
  {label := "HEAD /students/s1: ALL only", method := headMethod, path := ["students", "s1"], expected := [
    {registration := 3, handler := "student-suffix", params := [("id", "s1")]},
    {registration := 5, handler := "global"}, {registration := 8, handler := "global"}
  ]},
  {label := "PURGE /other/path: global ALL", method := purgeMethod, path := ["other", "path"],
    expected := globalMatches},
  {label := "GET /other/new/a: branch-local capture", path := ["other", "new", "a"], expected :=
    globalMatches ++ [{registration := 10, handler := "kind-suffix", params := [("kind", "other")]}]},
  {label := "GET /students/empty/a: parameter cannot be empty", path := ["students", "", "a"], expected := [
    {registration := 1, handler := "student-tree"}, {registration := 5, handler := "global"},
    {registration := 6, handler := "student-tree"}, {registration := 8, handler := "global"}
  ]},
  {label := "GET /students/s1/worksheets/w2: two captures, empty suffix",
    path := ["students", "s1", "worksheets", "w2"], expected := deepStudentMatches "s1" ++ [
      {registration := 11, handler := "worksheet-suffix", params := [("id", "s1"), ("worksheetId", "w2")]}
    ]},
  {label := "GET /students/s1/worksheets/w2/a/b: suffix adds no capture",
    path := ["students", "s1", "worksheets", "w2", "a", "b"], expected := deepStudentMatches "s1" ++ [
      {registration := 11, handler := "worksheet-suffix", params := [("id", "s1"), ("worksheetId", "w2")]}
    ]},
  {label := "GET /students/s2/a: fresh capture", path := ["students", "s2", "a"],
    expected := deepStudentMatches "s2"}
]

theorem wildcard_regression_examples :
    wildcardExamples.all (fun item =>
      decide (referenceLookup wildcardRoutes item.method item.path = item.expected) &&
      decide (Trie.lookup (Trie.build wildcardRoutes) item.method item.path = item.expected)) = true := by
  simp only [Trie.lookup_build]
  decide +kernel

example (remaining : Path) : Captures [] true remaining [] := Captures.suffix
example : capture [.parameter "id"] true [] = none := by decide +kernel

end HonoLean.Literal
