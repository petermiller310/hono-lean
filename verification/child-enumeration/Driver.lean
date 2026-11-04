import HonoLean.Upstream.SourceSubset.ForInSequence
import HonoLean.Upstream.NodeChildEnumeration.Generated
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
  let values ← (← json.getObjVal? key).getArr?
  pure values.toList

private def arrayInput (json : Json) : Except String IndexedArray := do
  let slots ← (← json.getArr?).toList.mapM fun slot =>
    if slot == Json.null then pure none else some <$> decode slot
  pure ⟨slots.length, fun index => slots[index]?.join⟩

private def objectInput (json : Json) : Except String OrdinaryObject := do
  let prototype ← json.getObjVal? "prototype"
  let prototype ← if prototype == Json.null then pure none else some <$> prototype.getNat?
  let own ← (← items json "own").mapM fun property => do
    let key ← units (← property.getObjVal? "key")
    let enumerable ← (← property.getObjVal? "enumerable").getBool?
    let configurable ← (← property.getObjVal? "configurable").getBool?
    let descriptor ← match ← (← property.getObjVal? "kind").getStr? with
      | "data" =>
        let value ← decode (← property.getObjVal? "value")
        let writable ← (← property.getObjVal? "writable").getBool?
        pure (.data value writable enumerable configurable)
      | "accessor" => pure <| PropertyDescriptor.accessor .unsupported .missing enumerable configurable
      | _ => throw "Unsupported fixture descriptor"
    pure (key, descriptor)
  pure ⟨own, prototype, true⟩

private def objectsOutput (heap : ObjectHeap) : Except String Json := do
  toJson <$> heap.mapM fun object => do
    let own ← object.own.mapM fun (key, descriptor) => do
      let key := toJson (key.map UInt16.toNat)
      match descriptor with
      | .data value writable enumerable configurable => pure <| Json.mkObj [
          ("key", key), ("kind", toJson "data"), ("value", ← encode value),
          ("writable", toJson writable), ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
      | .accessor _ _ enumerable configurable => pure <| Json.mkObj [
          ("key", key), ("kind", toJson "accessor"), ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
    pure <| Json.mkObj [("prototype", toJson object.prototype), ("own", toJson own)]

private def heapOutput (state : IndexedState) : Except String Json := do
  toJson <$> state.heap.mapM fun array => do
    toJson <$> (List.range array.length).mapM fun index =>
      match array.own index with | none => pure Json.null | some value => encode value

private def privateValues (state : ForInState) : Except String Json := do
  let pairs ← (["children", "params", "keep"] : List String).mapM fun name => do
    let value ← match privateGet (.object 0) name (forInStateView state) with
      | .ok value => pure value | .error _ => throw "Missing observed private field"
    pure (name, ← encode value)
  pure <| Json.mkObj pairs

private def trace (cell : UnitRegExpCell) (run : UnitExecution) : Except String Json := do
  unless cell == run.cell do throw "Actual regexp cell/trace mismatch"
  pure <| Json.mkObj [("positions", toJson run.positions), ("lastIndexTrace", toJson run.lastIndexWrites),
    ("unit", toJson cell.unit.toNat), ("lastIndex", toJson cell.lastIndex),
    ("match", if run.positions.isEmpty then Json.null else toJson (run.positions.map fun _ => [cell.unit.toNat]))]

private def runCase (program : List ForInStmt) (input : Json) : Except String Json := do
  let heap ← (← items input "heap").mapM arrayInput
  let objects ← (← items input "objects").mapM objectInput
  let supplied ← input.getObjVal? "bindings"
  let bindings ← (["child", "params", "m", "curNodesQueue"] : List String).filterMapM fun name => do
    match supplied.getObjVal? name with
    | .ok value => return some (name, ← decode value)
    | .error _ => return none
  let environment := bindings ++ [("_", .number 99), ("componentCount", .number 98), ("targetCurNodes", .number 97)]
  let privateInput ← input.getObjVal? "private"
  let values ← ([("children", 0), ("params", 1), ("keep", 2)] : List (String × Nat)).mapM fun (name, identity) =>
    return (identity, ← decode (← privateInput.getObjVal? name))
  let ambient : State := {
    objects := objects
    thisValue := .object 0
    privates := PrivateStore.ofData [("children", 0), ("params", 1), ("keep", 2)] [(0, values)]}
  let initial : ForInState := {ambient := ambient, regexp := {arrays := ⟨environment, heap⟩, regexps := [⟨120, 37⟩]}}
  match executeForInSequence 256 program initial with
  | .error _ | .ok (.breakLoop _) => pure <| Json.mkObj [("ok", toJson false)]
  | .ok (.normal after) =>
    unless after.regexp.regexps[0]? == some ⟨120, 37⟩ &&
        after.regexp.regexps.length == after.regexp.executions.length + 1 do
      throw "Old regexp frame/fresh trace count mismatch"
    let traces ← (after.regexp.regexps.drop 1 |>.zip after.regexp.executions).mapM fun (cell, run) => trace cell run
    pure <| Json.mkObj [("ok", toJson true), ("state", Json.mkObj [
      ("private", ← privateValues after), ("heap", ← heapOutput after.regexp.arrays),
      ("objects", ← objectsOutput after.ambient.objects),
      ("scope", toJson (after.regexp.arrays.environment == environment))]),
      ("traces", toJson traces)]

private def packet (input : Json) : Except String Json := do
  let source ← match input.getObjVal? "source" with
    | .ok value => value.getStr? | .error _ => pure NodeChildEnumeration.pinnedSource
  match parseForInSequence source ["child", "params", "m", "curNodesQueue"] ["children", "params", "keep"] with
  | none => pure <| Json.mkObj [("parsed", toJson false)]
  | some program =>
    let results ← (← items input "cases").mapM (runCase program)
    pure <| Json.mkObj [("parsed", toJson true), ("results", toJson results)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok output => (← IO.getStdout).putStrLn output.compress
  | .error message => throw <| IO.userError message
