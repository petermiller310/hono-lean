import HonoLean.Upstream.SourceSubset.OffsetSequence
import HonoLean.Upstream.SourceSubset.SplitPath
import HonoLean.Upstream.NodePartOffsets.Generated
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

private def items (json : Json) (key : String) : Except String (List Json) := do
  (← (← json.getObjVal? key).getArr?).toList |> pure

private def binding (state : State) (name : String) : Except String Value :=
  match state.environment.lookup name with | some value => pure value | none => throw ("Missing " ++ name)

private def heapOutput (heap : List (List Value)) : Except String Json := do
  toJson <$> heap.mapM fun array => toJson <$> array.mapM encode

private def runCase (program : List OffsetStmt) (prepareOnly : Bool) (input : Json) : Except String Json := do
  let initialHeap ← (← items input "heap").mapM fun row => do
    (← row.getArr?).toList.mapM decode
  let path ← units (← input.getObjVal? "path")
  let cache ← decode (← input.getObjVal? "cache")
  let useSplit ← match input.getObjVal? "split" with | .ok value => value.getBool? | .error _ => pure false
  let mut heap := initialHeap
  let mut supplied : List (String × Value) := []
  if useSplit then
    -- Explicit fixture preparation: execute the actual parsed splitter in its
    -- isolated model, then re-embed its returned contents as one fresh array.
    -- Current-heap startup/call composition is a separate source theorem.
    let parsed ← match parse pinnedSource with | some program => pure program | none => throw "Pinned splitter rejected"
    let parts ← (run parsed path defaultSplitLimit).mapError reprStr
    supplied := [("parts", .array heap.length), ("len", .number parts.length)]
    heap := heap ++ [parts]
  else
    if let .ok value := input.getObjVal? "parts" then supplied := supplied ++ [("parts", ← decode value)]
    if let .ok value := input.getObjVal? "len" then supplied := supplied ++ [("len", .number (← value.getInt?))]
  let canaries : List (String × Value) := [("offset", .number 91), ("p", .number 92), ("restPathString", .number 97)]
  let ambient : State := {
    objects := [emptyNullObject]
    sets := [[[120]]]
    thisValue := .object 0
    privates := PrivateStore.ofData [("saved", 9)] [(0, [(9, if heap.isEmpty then .number 9 else .array 0)])]}
  let mut state := {ambient with heap}
  let mut current := cache
  let mut steps : List Json := []
  let mut failed := false
  let indices ← match input.getObjVal? "indices" with | .ok value => value.getArr? | .error _ => pure #[toJson (0 : Nat)]
  let fuel ← match input.getObjVal? "fuel" with | .ok value => value.getNat? | .error _ => pure 10000
  for index in indices do
    if !failed then
      let index ← index.getInt?
      let environment := [("partOffsets", current), ("path", .string path), ("i", .number index)] ++ supplied ++ canaries
      let before := {state with environment}
      let oldCount := before.heap.length
      match executeOffsetSequence fuel defaultSplitLimit ["partOffsets"] program before with
      | .error _ => failed := true
      | .ok after =>
        let result ← binding after "partOffsets"
        let rest ← if prepareOnly then pure .undefined else binding after "restPathString"
        let expected := (if prepareOnly then [] else [("restPathString", rest)]) ++
          before.environment.set 0 ("partOffsets", result)
        unless after.objects == before.objects && after.sets == before.sets &&
            after.privates.names == before.privates.names && after.privates.elements == before.privates.elements &&
            after.thisValue == before.thisValue && after.functions.length == before.functions.length do
          throw "Unexpected ambient-frame mutation"
        let fresh := match result with | .array reference => decide (oldCount ≤ reference) | _ => false
        let fields := [("cache", ← encode result), ("reused", toJson (result == current)), ("fresh", toJson fresh),
          ("scope", toJson (after.environment == expected)), ("heap", ← heapOutput after.heap)]
        let encodedRest ← encode rest
        let fields := if prepareOnly then fields else fields ++ [("rest", encodedRest)]
        steps := steps ++ [Json.mkObj fields]
        state := {after with environment := []}
        current := result
  if failed then pure <| Json.mkObj [("ok", toJson false)] else
    pure <| Json.mkObj [("ok", toJson true), ("steps", toJson steps), ("importedSplit", toJson useSplit)]

private def packet (input : Json) : Except String Json := do
  let prepareOnly ← match input.getObjVal? "prepareOnly" with | .ok value => value.getBool? | .error _ => pure false
  let source ← match input.getObjVal? "source" with
    | .ok value => value.getStr? | .error _ => pure (if prepareOnly then NodePartOffsets.pinnedPrepare else NodePartOffsets.pinnedSource)
  match parseOffsetSequence source ["partOffsets", "path", "parts", "len", "i"] ["partOffsets"] with
  | none => pure <| Json.mkObj [("parsed", toJson false)]
  | some program =>
    let results ← (← items input "cases").mapM (runCase program prepareOnly)
    pure <| Json.mkObj [("parsed", toJson true), ("results", toJson results)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok output => (← IO.getStdout).putStrLn output.compress
  | .error message => throw <| IO.userError message
