import HonoLean.Upstream.ECMA2025.StringSearchSlice
import Lean.Data.Json

open HonoLean.Upstream.SourceSubset HonoLean.Upstream.ECMA2025 Lean

private def runCase (json : Json) : Except String Json := do
  let units ← (← json.getObjVal? "units").getArr?
  let input ← units.toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"
  let separator ← (← json.getObjVal? "separator").getNat?
  if separator ≥ 65536 then throw "Invalid separator"
  let position ← (← json.getObjVal? "position").getInt?
  let start ← (← json.getObjVal? "start").getInt?
  let stop ← match ← json.getObjVal? "stop" with
    | .null => pure none
    | value => some <$> value.getInt?
  return Json.mkObj [
    ("index", toJson (stringIndexOf input (UInt16.ofNat separator) position)),
    ("slice", toJson ((stringSlice input start stop).map UInt16.toNat))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let json ← Json.parse input
    let values ← json.getArr?
    return toJson (← values.toList.mapM runCase)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
