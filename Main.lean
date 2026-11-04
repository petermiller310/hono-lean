import HonoLean

open HonoLean
open HonoLean.Literal

def runExamples (routes : List HonoLean.Literal.Route) (cases : List Example) : IO Unit := do
  let tree := Trie.build routes
  for item in cases do
    let reference := referenceLookup routes item.method item.path
    let actual := Trie.lookup tree item.method item.path
    if actual ≠ item.expected ∨ actual ≠ reference then
      throw (IO.userError s!"Unexpected result for {item.label}")
    let summary := actual.map (fun entry => (entry.registration, entry.handler, entry.params))
    IO.println s!"{item.label}: {reprStr summary}"

def main : IO Unit := do
  IO.println "Literal paths (ALL selectors):"
  runExamples exampleRoutes examples
  IO.println "Method matching:"
  runExamples methodRoutes methodExamples
  IO.println "Named parameters:"
  runExamples parameterRoutes parameterExamples
  IO.println "Terminal wildcards:"
  runExamples wildcardRoutes wildcardExamples
  IO.println "Incremental registration:"
  runRegistrationExamples
  runRegistrationSequence
