import HonoLean.Adapter.Json

open HonoLean Literal Adapter Lean

namespace HonoLean.Benchmark

structure Workload where
  name : String
  banks : Array (List Literal.Route)
  requests : Array (Method × Path)

def need {α : Type} (value : Except Error α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError (reprStr error))

def natural (value : Json) (key : String) : IO Nat := do
  let field ← need (Adapter.field .invalidInput value key)
  match field.getNat? with
  | .ok n => pure n
  | .error message => throw (IO.userError message)

def parseWorkload (value : Json) : IO Workload := do
  let name ← need (stringField .invalidInput value "name")
  let banks ← need (arrayField .invalidInput value "banks")
  let banks ← banks.mapM fun bank => do
    let routes ← need (arrayField .invalidInput bank "routes")
    routes.toList.mapM (fun route => need (decodeRoute route >>= parseRoute))
  let requests ← need (arrayField .invalidInput value "requests")
  let requests ← requests.mapM (fun request => need (decodeRequest request >>= parseRequest))
  if banks.isEmpty || requests.isEmpty then throw (IO.userError "Empty benchmark bank")
  return ⟨name, banks, requests⟩

/-- An observable IO call boundary keeps construction inside each timed iteration. -/
@[noinline] def freshBuild (banks : Array (List Literal.Route)) (index : Nat) : IO Router :=
  pure (Router.build banks[index % banks.size]!)

@[noinline] def actualLookup (router : Router) (requests : Array (Method × Path))
    (index : Nat) : IO (List Match) := do
  match requests[index % requests.size]? with
  | some (method, path) => pure (Router.lookup router method path)
  | none => throw (IO.userError "Empty request bank")

/-- A small liveness sink, not a correctness oracle; fixture text is ASCII. -/
def digest (items : List Match) : UInt32 := items.foldl (fun acc item =>
  item.params.foldl (fun n binding => n + binding.1.length.toUInt32 + binding.2.length.toUInt32)
    (acc + item.registration.toUInt32 + item.handler.length.toUInt32 + item.params.length.toUInt32 + 1)) 0

def buildSample (workload : Workload) (iterations offset : Nat) : IO Json := do
  let mut roots : Array Router := #[]
  let start ← IO.monoNanosNow
  for i in [:iterations] do
    roots := roots.push (← freshBuild workload.banks (offset + i))
  let elapsed := (← IO.monoNanosNow) - start
  -- Read every actual built tree after the stop time; never time a lookup as a build.
  let mut checksum : UInt32 := 0
  for root in roots do
    checksum := checksum + digest (← actualLookup root workload.requests 0)
  return Json.mkObj [("nanos", toJson elapsed), ("checksum", toJson checksum.toNat)]

def lookupSample (workload : Workload) (router : Router) (iterations offset : Nat) : IO Json := do
  let mut checksum : UInt32 := 0
  let start ← IO.monoNanosNow
  for i in [:iterations] do
    checksum := checksum + digest (← actualLookup router workload.requests (offset + i))
  let elapsed := (← IO.monoNanosNow) - start
  return Json.mkObj [("nanos", toJson elapsed), ("checksum", toJson checksum.toNat)]

def measure (warmups samples : Nat) (sample : Nat → IO Json) : IO (Array Json) := do
  for i in [:warmups] do
    let _ ← sample i
  let mut results := #[]
  for i in [:samples] do results := results.push (← sample (warmups + i))
  return results

def run : IO Unit := do
  let source ← (← IO.getStdin).readToEnd
  let input ← match Json.parse source with
    | .ok input => pure input
    | .error message => throw (IO.userError message)
  let mode ← need (stringField .invalidInput input "mode")
  let config ← need (Adapter.field .invalidInput input "config")
  let warmups ← natural config "warmupSamples"
  let samples ← natural config "samples"
  let builds ← natural config "buildIterations"
  let lookups ← natural config "lookupIterations"
  let workloads ← need (arrayField .invalidInput input "workloads")
  let workloads ← workloads.mapM parseWorkload
  let mut output := #[]
  for workload in workloads do
    if mode == "validate" then
      let mut banks := #[]
      for routes in workload.banks do
        let router := Router.build routes
        let mut observations := #[]
        for (method, path) in workload.requests do
          observations := observations.push (matchesJson (Router.lookup router method path))
        banks := banks.push (Json.arr observations)
      output := output.push (Json.mkObj [("name", toJson workload.name), ("observations", .arr banks)])
    else if mode == "measure" then
      let router ← freshBuild workload.banks 0
      let build ← measure warmups samples (buildSample workload builds)
      let lookup ← measure warmups samples (lookupSample workload router lookups)
      output := output.push (Json.mkObj [("name", toJson workload.name),
        ("build", .arr build), ("lookup", .arr lookup)])
    else throw (IO.userError "Expected validate or measure mode")
  (← IO.getStdout).putStrLn ((Json.arr output).compress)

end HonoLean.Benchmark

def main : IO Unit := HonoLean.Benchmark.run
