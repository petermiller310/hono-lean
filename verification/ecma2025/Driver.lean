import HonoLean.Upstream.ECMA2025.PrimitiveBridge
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def units (json : Json) : Except String JSString := do
  let values ← json.getArr?
  values.toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Invalid UTF-16 code unit"

private def tagged : Value → Except String Json
  | .string contents => pure (Json.mkObj [("string", toJson (contents.map UInt16.toNat))])
  | .undefined => pure (Json.mkObj [("undefined", toJson true)])
  | _ => throw "Value outside the test transport domain"

private def strings (values : List Value) : Except String Json := do
  let contents ← values.mapM fun value => match value with
    | .string contents => pure (contents.map UInt16.toNat)
    | _ => throw "Expected only strings"
  return toJson contents

private def arrayCase (json : Json) : Except String Json := do
  let elements ← (← json.getArr?).toList.mapM units
  let array := ofList (elements.map Value.string)
  let (first, after) := shiftSteps array
  let indices := [0, 1, array.length, array.length + 1]
  let gets ← indices.mapM (fun index => tagged (numericGet array index))
  let equals ← indices.mapM fun index =>
    (equalsEmpty (numericGet array index)).mapError reprStr
  return Json.mkObj [
    ("first", ← tagged first), ("after", ← strings (observe after)),
    ("indices", toJson indices), ("get", toJson gets), ("equalsEmpty", toJson equals),
    ("length", toJson after.length),
    ("oldLastIsOwn", toJson ((after.own (array.length - 1)).isSome))]

private def document (json : Json) : Except String Json := do
  let limit ← (← json.getObjVal? "limit").getNat?
  if limit > defaultSplitLimit then throw "Expected normalized uint32 limit"
  let separator ← (← json.getObjVal? "separator").getNat?
  if separator ≥ 65536 then throw "Invalid separator code unit"
  let inputs ← (← json.getObjVal? "inputs").getArr?
  let splitResults ← inputs.toList.mapM fun input => do
    let input ← units input
    pure (toJson ((stringSplit input (UInt16.ofNat separator) limit).map
      (fun value => value.map UInt16.toNat)))
  let pathResults ← inputs.toList.mapM fun input => do
    let input ← units input
    strings (← (splitPathSteps input limit).mapError reprStr)
  let arrays ← (← json.getObjVal? "arrays").getArr?
  let arrayResults ← arrays.toList.mapM arrayCase
  return Json.mkObj [("split", toJson splitResults), ("paths", toJson pathResults),
    ("arrays", toJson arrayResults)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= document with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
