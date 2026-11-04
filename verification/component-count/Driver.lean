import HonoLean.Upstream.SourceSubset.RegExpSequence
import HonoLean.Upstream.NodeComponentCount.Generated
import HonoLean.Upstream.NodeQueueAdvance.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Invalid UTF16 unit"

private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "array" => .array <$> (← json.getObjVal? "ref").getNat?
  | "object" => .object <$> (← json.getObjVal? "ref").getNat?
  | _ => throw "Unsupported fixture value"

private def encode : Value → Except String Json
  | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
  | .null => pure <| Json.mkObj [("kind", toJson "null")]
  | .boolean value => pure <| Json.mkObj [("kind", toJson "bool"), ("value", toJson value)]
  | .number value => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson value)]
  | .string value => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (value.map UInt16.toNat))]
  | .array reference => pure <| Json.mkObj [("kind", toJson "array"), ("ref", toJson reference)]
  | .object reference => pure <| Json.mkObj [("kind", toJson "object"), ("ref", toJson reference)]
  | _ => throw "Unsupported observation"

private def arrayInput (json : Json) : Except String IndexedArray := do
  let slots ← (← json.getArr?).toList.mapM fun slot =>
    if slot == Json.null then pure none else some <$> decode slot
  pure ⟨slots.length, fun index => slots[index]?.join⟩

private def heapOutput (state : IndexedState) (hiddenRefs : List Nat) : Except String Json := do
  toJson <$> (state.heap.zipIdx).mapM fun (array, reference) => do
    if hiddenRefs.contains reference then pure <| Json.mkObj [("internalAccumulator", toJson true)] else
    let slots ← (List.range array.length).mapM fun index =>
      match array.own index with | none => pure Json.null | some value => encode value
    pure (toJson slots)

private def items (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok value => (·.toList) <$> value.getArr? | .error _ => pure []
private def number (json : Json) (key : String) (fallback : Nat) : Except String Nat :=
  match json.getObjVal? key with | .ok value => value.getNat? | .error _ => pure fallback
private def inputValue (json : Json) (key : String) (fallback : Value) : Except String Value :=
  match json.getObjVal? key with | .ok value => decode value | .error _ => pure fallback
private def binding (state : IndexedState) (key : String) : Except String Value :=
  match state.environment.lookup key with | some value => pure value | none => throw ("Missing " ++ key)

private def trace (run : UnitExecution) (accumulator : IndexedArray) : Except String Json := do
  let matchContents ← (List.range accumulator.length).mapM fun index =>
    match accumulator.own index with
    | some (.string contents) => pure (contents.map UInt16.toNat)
    | _ => throw "Unexpected actual model accumulator cell"
  unless matchContents.length == run.positions.length do throw "Accumulator/exec-trace length mismatch"
  pure <| Json.mkObj [("positions", toJson run.positions), ("lastIndexTrace", toJson run.lastIndexWrites),
    ("unit", toJson run.cell.unit.toNat), ("lastIndex", toJson run.cell.lastIndex),
    ("match", if run.positions.isEmpty then Json.null else toJson matchContents)]

private def runCase (program : List RegExpStmt) (advance : List SparseStmt) (full : Bool)
    (input : Json) : Except String Json := do
  let heap ← (← items input "heap").mapM arrayInput
  let queue ← inputValue input "queue" (.array 0)
  let temp ← inputValue input "temp" (.array 2)
  let current ← inputValue input "current" .undefined
  let mut state : RegExpState := {arrays := ⟨[("curNodes", current), ("tempNodes", temp), ("curNodesQueue", queue)], heap⟩}
  let mut hiddenRefs : List Nat := []
  let mut counts : List Json := []
  let mut schedules : List Json := []
  let mut advances : List Json := []
  let mut retained : List Json := []
  let mut traces : List Json := []
  let mut failed := false
  for request in (← items input "requests") do
    if !failed then
      let m ← inputValue request "m" (.array 1)
      let child ← inputValue request "child" (.object 0)
      let oldEnvironment := state.arrays.environment
      let activated := {state with arrays := {state.arrays with environment := [("m", m), ("child", child)] ++ oldEnvironment}}
      let oldCount := state.arrays.heap.length
      match executeRegExpSequence 128 program activated with
      | .error _ => failed := true
      | .ok after =>
        unless after.executions.length == state.executions.length + 1 &&
            after.regexps.length == state.regexps.length + 1 && oldCount < after.arrays.heap.length do
          throw "Expected one fresh regexp, one execution and a tracked accumulator"
        let run ← match after.executions.getLast? with
          | some run => pure run | none => throw "Missing model exec trace"
        let cell ← match after.regexps[state.regexps.length]? with
          | some cell => pure cell | none => throw "Missing actual model regexp cell"
        unless cell == run.cell do throw "Actual regexp store/exec-trace mismatch"
        let accumulator ← match after.arrays.heap[oldCount]? with
          | some array => pure array | none => throw "Missing model accumulator"
        traces := traces ++ [← trace run accumulator]
        let count ← binding after.arrays "componentCount"
        counts := counts ++ [← encode count]
        hiddenRefs := hiddenRefs ++ [oldCount]
        if full then
          let target ← binding after.arrays "targetCurNodes"
          let fresh := match target with | .array reference => decide (oldCount + 1 ≤ reference) | _ => false
          retained := retained ++ [← encode target]
          schedules := schedules ++ [Json.mkObj [("target", ← encode target), ("fresh", toJson fresh),
            ("heap", ← heapOutput after.arrays hiddenRefs)]]
        state := {after with arrays := {after.arrays with environment := oldEnvironment}}
  for _ in [:(← number input "advances" 0)] do
    if !failed then
      let oldEnvironment := state.arrays.environment
      let oldCount := state.arrays.heap.length
      match executeSparseSequence 128 ["curNodes"] advance state.arrays with
      | .error _ => failed := true
      | .ok after =>
        let shifted ← binding after "shifted"
        let current ← binding after "curNodes"
        let fresh := match current with | .array reference => decide (oldCount ≤ reference) | _ => false
        advances := advances ++ [Json.mkObj [("shifted", ← encode shifted), ("current", ← encode current),
          ("fresh", toJson fresh), ("heap", ← heapOutput after hiddenRefs)]]
        state := {state with arrays := {after with environment := oldEnvironment.set 0 ("curNodes", current)}}
  if failed then pure <| Json.mkObj [("ok", toJson false)] else
    pure <| Json.mkObj [("ok", toJson true), ("counts", toJson counts), ("schedules", toJson schedules),
      ("advances", toJson advances), ("retained", toJson retained), ("heap", ← heapOutput state.arrays hiddenRefs),
      ("traces", toJson traces)]

private def packet (input : Json) : Except String Json := do
  let full ← match input.getObjVal? "full" with | .ok value => value.getBool? | .error _ => pure true
  let source ← match input.getObjVal? "source" with
    | .ok value => value.getStr? | .error _ => pure (if full then NodeComponentCount.pinnedFullSource else NodeComponentCount.pinnedSource)
  let bindings := if full then ["m", "curNodesQueue", "child"] else ["m"]
  match parseRegExpSequence source bindings,
      parseSparseSequence NodeQueueAdvance.pinnedSource ["curNodesQueue", "curNodes", "tempNodes"] ["curNodes"] with
  | some program, some advance =>
    let results ← (← items input "cases").mapM (runCase program advance full)
    pure <| Json.mkObj [("parsed", toJson true), ("results", toJson results)]
  | _, _ => pure <| Json.mkObj [("parsed", toJson false)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok output => (← IO.getStdout).putStrLn output.compress
  | .error message => throw <| IO.userError message
