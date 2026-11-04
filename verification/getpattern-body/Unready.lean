import HonoLean.Upstream.SourceSubset.PatternCache
import HonoLean.Upstream.SourceSubset.LabelMatchRealm
import Lean.Data.Json
open Lean HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025
set_option autoImplicit false
private def packet (json : Json) : Except String Json := do
  let source ← (← json.getObjVal? "source").getStr?
  let some program := parsePatternCacheBody source ["label","next","patternCache","RegExp"] | throw "Body parser refused"
  let empty : LabelMatchState := {base := {regexp := {ambient := {environment := [("label",.string [42])]}}}}
  let dangling := cacheWithAmbient empty {empty.base.regexp.ambient with environment :=
    [("label",.string [42]),("patternCache",.object 999),("next",.object 999),("RegExp",.number 17)]}
  let results ← [empty,dangling].mapM fun before => do
    let (value,after) ← (runPatternCache 512 defaultSplitLimit ⟨labelStandardContext⟩ program before).mapError reprStr
    pure <| Json.mkObj [("value",toJson (reprStr value)),("sameEntireState",toJson (reprStr after == reprStr before)),
      ("arrays",toJson after.base.regexp.ambient.heap.length),("objects",toJson after.base.regexp.ambient.objects.length)]
  pure (toJson results)
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok result => (← IO.getStdout).putStrLn result.compress; pure 0
  | .error error => (← IO.getStderr).putStrLn error; pure 1
