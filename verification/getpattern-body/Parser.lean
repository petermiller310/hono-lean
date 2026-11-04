import HonoLean.Upstream.GetPatternBody.Syntax
import Lean.Data.Json
open Lean HonoLean.Upstream HonoLean.Upstream.SourceSubset HonoLean.Upstream.GetPatternBody
set_option autoImplicit false

private def encodeType : TypeSyntax → Json
  | .named name => Json.mkObj [("kind",toJson "named"),("name",toJson name)]
  | .union left right => Json.mkObj [("kind",toJson "union"),("left",encodeType left),("right",encodeType right)]
  | other => Json.mkObj [("kind",toJson "other"),("repr",toJson (reprStr other))]
private def parse (value : Json) (canonical : List PatternCacheStmt) : Except String Json := do
  let source ← value.getStr?
  match parseExportedArrow source ["patternCache","RegExp"] with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some declaration => pure <| Json.mkObj [("parsed",toJson true),("name",toJson declaration.name),
      ("parameters",toJson (declaration.parameters.map (fun p => Json.mkObj [("name",toJson p.name),("optional",toJson p.optional),("type",encodeType p.annotation)]))),
      ("resultType",encodeType declaration.resultType),("innerSource",toJson declaration.innerSource),
      ("bodyLength",toJson declaration.body.length),("bodyMatches",toJson (reprStr declaration.body == reprStr canonical))]
private def packet (value : Json) : Except String Json := do
  let body ← (← value.getObjVal? "body").getStr?
  let some canonical := parsePatternCacheBody body ["label","next","patternCache","RegExp"] | throw "Canonical body parser refused"
  let sources ← (← value.getObjVal? "sources").getArr?
  toJson <$> sources.toList.mapM (fun source => parse source canonical)
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok result => (← IO.getStdout).putStrLn result.compress; pure 0
  | .error error => (← IO.getStderr).putStrLn error; pure 1
