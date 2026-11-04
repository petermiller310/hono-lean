import HonoLean.Upstream.NodeParamAssignment.Correctness
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"

private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "object" => .object <$> (← json.getObjVal? "ref").getNat?
  | "array" => pure (.array 0)
  | "constructor" => pure .objectConstructor
  | _ => throw "Unknown packet value"

private def encode (value : Value) : Json :=
  let kind (name : String) (fields : List (String × Json) := []) :=
    Json.mkObj (("kind", toJson name) :: fields)
  match value with
  | .undefined => kind "undefined"
  | .null => kind "null"
  | .boolean value => kind "bool" [("value", toJson value)]
  | .number value => kind "number" [("value", toJson value)]
  | .string text => kind "string" [("units", toJson (text.map UInt16.toNat))]
  | .object reference => kind "object" [("ref", toJson reference)]
  | .array reference => kind "array" [("ref", toJson reference)]
  | .objectConstructor => kind "constructor"
  | .function reference => Json.mkObj [("kind", toJson "function"), ("ref", toJson reference)]
  | .set reference => kind "set" [("ref", toJson reference)]
  | .setConstructor => kind "set-constructor"

private def runCase (program : Assignment) (json : Json) : Except String Json := do
  let key ← units (← json.getObjVal? "key")
  let nodeValue ← decode (← json.getObjVal? "node")
  let parameterValue ← decode (← json.getObjVal? "p")
  let nodeOwn ← (← json.getObjVal? "nodeOwn").getBool?
  let mode ← (← json.getObjVal? "pMode").getStr?
  let index ← (← json.getObjVal? "index").getInt?
  let prepopulate ← match json.getObjVal? "prepopulate" with
    | .ok value => value.getBool?
    | .error _ => pure false
  let node : OrdinaryObject := {prototype := some 0}
  let node := if nodeOwn then newDataObject node key nodeValue else node
  let optional : OrdinaryObject := if mode == "inherited" then {prototype := some 0} else emptyNullObject
  let optional := if mode == "own" then newDataObject optional key parameterValue else optional
  let parameter := if mode == "undefined" then Value.undefined else if mode == "null" then .null else .object 2
  let seedKey : JSString := [115, 101, 101, 100]
  let outputBefore := if prepopulate then newDataObject emptyNullObject seedKey (.string [102, 114, 97, 109, 101])
    else emptyNullObject
  let before : State := {
    environment := [("handlerSet", .object 4), ("params", parameter), ("i", .number index),
      ("key", .string key), ("nodeParams", .object 1)]
    heap := [[]]
    objects := [objectPrototypeProjection [], node, optional, outputBefore,
      newDataObject emptyNullObject NodeParamAssignment.paramsKey (.object 3)]
  }
  let (value, after) ← (runAssignment program before).mapError reprStr
  let output ← (getProperty propertyFuel after.objects 3 key).mapError reprStr
  let own ← (hasOwn after.objects 3 key).mapError reprStr
  let retainedSeed ← (getProperty propertyFuel after.objects 3 seedKey).mapError reprStr
  let object ← match after.objects[3]? with | some object => pure object | none => throw "Missing output"
  let descriptor ← match object.own.lookup key with
    | some (.data _ writable enumerable configurable) => pure <| Json.mkObj [
        ("writable", toJson writable), ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
    | _ => throw "Unexpected output descriptor"
  return Json.mkObj [("returned", encode value), ("output", encode output), ("own", toJson own),
    ("prototype", toJson object.prototype), ("descriptor", descriptor),
    ("retainedSeed", encode retainedSeed), ("ownCount", toJson object.own.length),
    ("frameKept", toJson (decide (after.environment = before.environment ∧ after.heap = before.heap ∧
      after.objects.length = before.objects.length ∧
      ∀ index ∈ List.range before.objects.length, index ≠ 3 → after.objects[index]? = before.objects[index]?)))]

def main : IO Unit := do
  let text ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let json ← Json.parse text
    let source ← match json.getObjVal? "source" with
      | .ok value => value.getStr?
      | .error _ => pure NodeParamAssignment.pinnedSource
    let program ← match parseAssignment source NodeParamAssignment.bindings with
      | some program => pure program
      | none => throw "Assignment parse rejected"
    let cases ← (← json.getObjVal? "cases").getArr?
    return toJson (← cases.toList.mapM (runCase program))
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
