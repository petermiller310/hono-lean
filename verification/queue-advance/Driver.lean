import HonoLean.Upstream.SourceSubset.MutableSequence
import HonoLean.Upstream.NodeQueueAdvance.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset Lean

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
  | _ => throw "Unsupported observed fixture value"

private def observedHeap (state : State) : Except String Json := do
  toJson <$> state.heap.mapM (fun values => toJson <$> values.mapM encode)

private def normal : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

private def integer (json : Json) (key : String) (fallback : Nat) : Except String Nat :=
  match json.getObjVal? key with
  | .ok value => value.getNat?
  | .error _ => pure fallback

private def runCase (program : List Stmt) (input : Json) : Except String Json := do
  let heap ← (← (← input.getObjVal? "heap").getArr?).toList.mapM fun row => do
    (← row.getArr?).toList.mapM decode
  let queue ← decode (← input.getObjVal? "queue")
  let temp ← decode (← input.getObjVal? "temp")
  let current ← match input.getObjVal? "current" with | .ok value => decode value | .error _ => pure .undefined
  let count ← integer input "rounds" 1
  let environment := [("curNodes", current), ("keep", .number 73), ("tempNodes", temp),
    ("curNodesQueue", queue), ("curNodes", .object 3), ("shifted", .number 99)]
  let initial : State := {
    heap, environment, objects := List.replicate 4 ECMA2025.emptyNullObject
    thisValue := .object 2 }
  let mut state := initial
  let mut steps : List Json := []
  let mut failed := false
  for _ in [:count] do
    if !failed then
      let oldCount := state.heap.length
      let oldEnvironment := state.environment
      match executeMutableSequence 128 defaultSplitLimit ["curNodes"] program state >>= normal with
      | .error _ => failed := true
      | .ok after =>
        let shifted ← (lookupVariable after "shifted").mapError reprStr
        let current ← (lookupVariable after "curNodes").mapError reprStr
        -- The fresh fragment-local const may shadow earlier shifted bindings;
        -- all unrelated and older shadowed curNodes entries must survive.
        let expected := ("shifted", shifted) :: oldEnvironment.set 0 ("curNodes", current)
        if after.environment != expected then throw "Unexpected lexical state"
        if after.objects != state.objects || after.functions.length != state.functions.length ||
            after.sets != state.sets || after.privates != state.privates || after.thisValue != state.thisValue then
          throw "Unexpected nonarray frame change"
        let fresh := match current with | .array reference => decide (oldCount ≤ reference) | _ => false
        steps := steps ++ [Json.mkObj [("shifted", ← encode shifted), ("current", ← encode current),
          ("fresh", toJson fresh), ("heap", ← observedHeap after)]]
        -- Each wrapper invocation leaves its local shifted scope while retaining
        -- the actual outer curNodes write and all heap effects.
        state := {after with environment := oldEnvironment.set 0 ("curNodes", current)}
  if failed then pure <| Json.mkObj [("ok", toJson false)]
  else pure <| Json.mkObj [("ok", toJson true), ("steps", toJson steps)]

private def packet (input : Json) : Except String Json := do
  let source ← match input.getObjVal? "source" with
    | .ok value => value.getStr?
    | .error _ => pure NodeQueueAdvance.pinnedSource
  match parseMutableSequence source ["curNodesQueue", "curNodes", "tempNodes"] ["curNodes"] with
  | none => pure <| Json.mkObj [("parsed", toJson false)]
  | some program =>
    let cases ← (← (← input.getObjVal? "cases").getArr?).toList.mapM (runCase program)
    pure <| Json.mkObj [("parsed", toJson true), ("results", toJson cases)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output := do packet (← Json.parse input)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error error => throw <| IO.userError error
