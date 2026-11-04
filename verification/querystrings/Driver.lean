import HonoLean.Upstream.GetQueryStrings.Correctness
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset Lean

private def units (json : Json) : Except String JSString := do
  let values ← json.getArr?
  values.toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Expected UTF-16 code unit"

private def document (json : Json) : Except String Json := do
  let inputs ← (← json.getObjVal? "inputs").getArr?
  let source ← match json.getObjVal? "source" with
    | .ok value => value.getStr?
    | .error _ => pure GetQueryStrings.pinnedSource
  let program ← match parseString source with
    | some value => pure value
    | none => throw "Source outside the checked parser subset"
  let results ← inputs.toList.mapM fun input => do
    let input ← units input
    let output ← (runString program input).mapError reprStr
    pure (output.map UInt16.toNat)
  return Json.mkObj [("results", toJson results)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= document with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
