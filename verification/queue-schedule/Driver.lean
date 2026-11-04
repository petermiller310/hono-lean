import HonoLean.Upstream.SourceSubset.SparseSequence
import HonoLean.Upstream.NodeQueueSchedule.Generated
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

private def heapOutput (state : IndexedState) : Except String Json := do
  toJson <$> state.heap.mapM fun array => do
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

private def runCase (schedule advance : List SparseStmt) (denseAdvance : List Stmt) (input : Json) : Except String Json := do
  let heap ← (← items input "heap").mapM arrayInput
  let queue ← decode (← input.getObjVal? "queue")
  let temp ← inputValue input "temp" (.array 2)
  let current ← inputValue input "current" .undefined
  let baseEnvironment := [("curNodes", current), ("tempNodes", temp), ("curNodesQueue", queue),
    ("targetCurNodes", .object 3), ("curNodes", .object 3), ("shifted", .number 99)]
  let ambient : State := {objects := List.replicate 4 emptyNullObject, thisValue := .object 2}
  let mut state : IndexedState := ⟨baseEnvironment, heap⟩
  let mut schedules : List Json := []
  let mut advances : List Json := []
  let mut retained : List Json := []
  let mut failed := false
  for request in (← items input "requests") do
    if !failed then
      let index ← (← request.getObjVal? "index").getInt?
      let child ← decode (← request.getObjVal? "child")
      let oldEnvironment := state.environment
      let activated := {state with environment := [("componentCount", .number index), ("child", child)] ++ oldEnvironment}
      let oldCount := state.heap.length
      match executeSparseSequence 128 [] schedule activated with
      | .error _ => failed := true
      | .ok after =>
        let target ← binding after "targetCurNodes"
        unless after.environment == ("targetCurNodes", target) :: activated.environment do
          throw "Unexpected scheduling lexical effect"
        let fresh := match target with | .array reference => decide (oldCount ≤ reference) | _ => false
        retained := retained ++ [← encode target]
        schedules := schedules ++ [Json.mkObj [("target", ← encode target), ("fresh", toJson fresh),
          ("heap", ← heapOutput after)]]
        state := {after with environment := oldEnvironment}
  for _ in [:(← number input "advances" 0)] do
    if !failed then
      let oldEnvironment := state.environment
      let oldCount := state.heap.length
      let before := state
      match executeSparseSequence 128 ["curNodes"] advance state with
      | .error _ => failed := true
      | .ok after =>
        let shifted ← binding after "shifted"
        let current ← binding after "curNodes"
        unless after.environment == ("shifted", shifted) :: oldEnvironment.set 0 ("curNodes", current) do
          throw "Unexpected consumer lexical effect"
        -- This checks the READ-VALUE bridge; it never replaces authoritative
        -- sparse own properties or asserts hole-presence equality.
        match executeMutableSequence 128 defaultSplitLimit ["curNodes"] denseAdvance (embedIndexedState ambient before) with
        | .ok (.normal dense) =>
          unless dense.heap == (embedIndexedState ambient after).heap && dense.environment == after.environment do
            throw "Sparse/dense read-value bridge mismatch"
        | _ => throw "Dense consumer failed after sparse success"
        let fresh := match current with | .array reference => decide (oldCount ≤ reference) | _ => false
        advances := advances ++ [Json.mkObj [("shifted", ← encode shifted), ("current", ← encode current),
          ("fresh", toJson fresh), ("heap", ← heapOutput after)]]
        state := {after with environment := oldEnvironment.set 0 ("curNodes", current)}
  if failed then pure <| Json.mkObj [("ok", toJson false)] else
    pure <| Json.mkObj [("ok", toJson true), ("schedules", toJson schedules), ("advances", toJson advances),
      ("retained", toJson retained), ("heap", ← heapOutput state)]

private def packet (input : Json) : Except String Json := do
  let scheduleSource ← match input.getObjVal? "scheduleSource" with
    | .ok value => value.getStr? | .error _ => pure NodeQueueSchedule.pinnedSource
  let advanceSource ← match input.getObjVal? "advanceSource" with
    | .ok value => value.getStr? | .error _ => pure NodeQueueAdvance.pinnedSource
  let schedule := parseSparseSequence scheduleSource ["curNodesQueue", "componentCount", "child"]
  let advance := parseSparseSequence advanceSource ["curNodesQueue", "curNodes", "tempNodes"] ["curNodes"]
  let dense := parseMutableSequence advanceSource ["curNodesQueue", "curNodes", "tempNodes"] ["curNodes"]
  match schedule, advance, dense with
  | some schedule, some advance, some dense =>
    let results ← (← items input "cases").mapM (runCase schedule advance dense)
    pure <| Json.mkObj [("parsed", toJson true), ("results", toJson results)]
  | _, _, _ => pure <| Json.mkObj [("parsed", toJson false)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok output => (← IO.getStdout).putStrLn output.compress
  | .error message => throw <| IO.userError message
