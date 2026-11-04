import HonoLean.Upstream.SourceSubset.SplitPath
import Lean.Data.Json

open HonoLean.Upstream.SourceSubset Lean

private def inputUnits (json : Json) : Except String JSString := do
  let values ← json.getArr?
  values.toList.mapM fun json => do
    let unit ← json.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else .error "Expected UTF-16 code unit"

private def encoded (values : List Value) : Except String Json := do
  let arrays ← values.mapM fun value =>
    match value with
    | .string contents => .ok (toJson (contents.map UInt16.toNat))
    | _ => .error "Expected a string array result"
  return toJson arrays

private def document (json : Json) : Except String Json := do
  let inputs ← (← json.getObjVal? "inputs").getArr?
  let limit ← (← json.getObjVal? "limit").getNat?
  if limit > defaultSplitLimit then throw "Limit is not normalized uint32"
  let source ← match json.getObjVal? "source" with
    | .ok source => source.getStr?
    | .error _ => pure pinnedSource
  let program ← match parse source with
    | some program => pure program
    | none => .error "Source outside checked parser subset"
  let results ← inputs.toList.mapM fun input => do
    let contents ← inputUnits input
    let values ← (run program contents limit).mapError reprStr
    encoded values
  return Json.mkObj [("results", toJson results)]

def main : IO Unit := do
  let text ← (← IO.getStdin).readToEnd
  match Json.parse text >>= document with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
