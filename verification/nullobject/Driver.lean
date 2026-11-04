import HonoLean.Upstream.D1.Mechanism
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"

private def tagged : Value → Except String Json
  | .string text => pure (Json.mkObj [("string", toJson (text.map UInt16.toNat))])
  | .object reference => pure (Json.mkObj [("object", toJson reference)])
  | .null => pure Json.null
  | .undefined => pure (Json.mkObj [("undefined", toJson true)])
  | _ => throw "Unsupported observation"

private def descriptor : Option PropertyDescriptor → Except String Json
  | none => pure Json.null
  | some (.data value writable enumerable configurable) =>
    return Json.mkObj [("kind", toJson "data"), ("value", ← tagged value),
      ("writable", toJson writable), ("enumerable", toJson enumerable),
      ("configurable", toJson configurable)]
  | _ => throw "Unexpected accessor output"

private def transfer (json : Json) : Except String Json := do
  let key ← units (← json.getObjVal? "key")
  let contents ← units (← json.getObjVal? "contents")
  let result ← (D1.captureTransfer key contents).mapError reprStr
  return Json.mkObj [
    ("temporaryHasOwn", toJson result.temporaryHasOwn), ("readValue", ← tagged result.readValue),
    ("outputHasOwn", toJson result.outputHasOwn), ("outputValue", ← tagged result.outputValue),
    ("outputPrototype", toJson result.outputPrototype), ("descriptor", ← descriptor result.descriptor)]

private def allocation (source : String) (json : Json) : Except String Json := do
  let count ← json.getNat?
  let before : State := {
    environment := [("frame", .string [97])]
    heap := [[.string [98]]]
    objects := List.replicate count emptyNullObject
  }
  let program ← match parseNoArg source with
    | some program => pure program
    | none => throw "Source parse rejected"
  let (first, after) ← (runNoArg program before).mapError reprStr
  let (second, final) ← (runNoArg program after).mapError reprStr
  let first ← match first with | .object reference => pure reference | _ => throw "Wrong return"
  let second ← match second with | .object reference => pure reference | _ => throw "Wrong return"
  let object ← match final.objects[first]? with | some object => pure object | none => throw "Missing object"
  return Json.mkObj [("first", toJson first), ("second", toJson second),
    ("distinct", toJson (first != second)), ("length", toJson final.objects.length),
    ("emptyOwn", toJson object.own.isEmpty), ("prototype", toJson object.prototype),
    ("extensible", toJson object.extensible),
    ("frameKept", toJson (decide (final.environment = before.environment ∧ final.heap = before.heap ∧
      final.objects.take count = before.objects)))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let json ← Json.parse input
    let source ← match json.getObjVal? "source" with
      | .ok value => value.getStr?
      | .error _ => pure CreateNullObject.pinnedSource
    let allocations ← (← (← json.getObjVal? "allocations").getArr?).toList.mapM (allocation source)
    let transfers ← (← (← json.getObjVal? "transfers").getArr?).toList.mapM transfer
    return Json.mkObj [("allocations", toJson allocations), ("transfers", toJson transfers)]
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
