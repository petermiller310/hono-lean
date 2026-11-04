import HonoLean.Upstream.GetPatternLookahead.Source
import HonoLean.Upstream.SourceSubset.LookaheadRegExp.Runtime
import Lean.Data.Json
open Lean HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025
set_option autoImplicit false

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let number ← value.getNat?
    if number < 65536 then pure (UInt16.ofNat number) else throw "Invalid UTF16 unit"
private def entries (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with | .ok value => return (← value.getArr?).toList | .error _ => pure []
private def flag (json : Json) (name : String) (fallback : Bool) : Except String Bool :=
  match json.getObjVal? name with | .ok value => value.getBool? | .error _ => pure fallback
private def integer (json : Json) (name : String) (fallback : Int) : Except String Int :=
  match json.getObjVal? name with | .ok value => value.getInt? | .error _ => pure fallback
private def field (json : Json) (name fallback : String) : Except String String :=
  match json.getObjVal? name with | .ok value => value.getStr? | .error _ => pure fallback
private def encoded (value : Value) : Except String Json :=
  match value with
  | .string value => pure (toJson (value.map UInt16.toNat))
  | _ => throw "Expected visible string"
private def lastDescriptor (world : LookaheadRegExp.State) (reference : Nat) : Except String Json := do
  let some object := world.base.base.regexp.ambient.objects[reference]? | throw "Missing regex object"
  let some (.data (.number value) writable enumerable configurable) := object.own.lookup lastIndexKey | throw "Non-numeric lastIndex observer boundary"
  pure (Json.mkObj [("value",toJson value),("writable",toJson writable),("enumerable",toJson enumerable),("configurable",toJson configurable)])
private def oldFrames (before after : LookaheadRegExp.State) : Bool :=
  let initial := before.base.base.regexp.ambient
  let current := after.base.base.regexp.ambient
  decide (current.heap.take initial.heap.length=initial.heap) &&
  ((List.range initial.objects.length).all fun reference => decide (current.objects[reference]?=initial.objects[reference]?)) &&
  decide (current.privates=initial.privates) && decide (current.sets=initial.sets) &&
  decide (current.thisValue=initial.thisValue) && (reprStr current.functions == reprStr initial.functions) &&
  decide (after.base.base.regexp.brands=before.base.base.regexp.brands) &&
  decide (after.base.symbols=before.base.symbols) && decide (after.base.accessors=before.base.accessors)
private def encodeMatch (world : LookaheadRegExp.State) (value : Value) : Except String Json := do
  match value with
  | .null => pure Json.null
  | .array reference =>
    let some values := world.base.base.regexp.ambient.heap[reference]? | throw "Missing result array"
    let some view := world.base.base.regexp.results.lookup reference | throw "Missing match view"
    pure (Json.mkObj [("values",toJson (← values.mapM encoded)),("index",toJson view.index),
      ("input",toJson (view.input.map UInt16.toNat)),("groupsUndefined",toJson true)])
  | _ => throw "Unexpected exec value"
private def failed : Json := Json.mkObj [("ok",toJson false)]
private def runCase (nodes : GetPatternLookahead.SelectedNodes) (fixture : Json) : Except String Json := do
  let label ← units (← fixture.getObjVal? "label")
  let next ← units (← fixture.getObjVal? "next")
  let constructorKind ← field fixture "constructorKind" "builtin"
  let original := labelStandardState []
  let initial : LookaheadRegExp.State := ⟨cacheWithAmbient original {original.base.regexp.ambient with
      environment := [("label",.string label),("next",.string next),("RegExp",if constructorKind="number"then .number 17 else .function 6)]
      heap := original.base.regexp.ambient.heap ++ [[]]},[]⟩
  let .ok matched := LookaheadRegExp.executeDeclaration 2048 defaultSplitLimit ⟨labelStandardContext⟩ nodes.labelDeclaration initial | return failed
  let .ok keyed := LookaheadRegExp.executeDeclaration 2048 defaultSplitLimit ⟨labelStandardContext⟩ nodes.keyDeclaration matched | return failed
  let .ok (tuple, constructed) := LookaheadRegExp.evalExpr 2048 defaultSplitLimit ⟨labelStandardContext⟩ nodes.positiveTuple keyed | return failed
  let .array tupleReference := tuple | throw "Non-array tuple"
  let some tupleValues := constructed.base.base.regexp.ambient.heap[tupleReference]? | throw "Missing tuple"
  let some first := tupleValues[0]? | throw "Missing first tuple slot"
  let some name := tupleValues[1]? | throw "Missing name slot"
  let some (Value.object reference) := tupleValues[2]? | throw "Missing regex slot"
  let some (.lookahead record) := LookaheadRegExp.recordAt constructed reference | throw "Wrong authoritative record kind"
  let some object := constructed.base.base.regexp.ambient.objects[reference]? | throw "Missing constructed object"
  let lastIndex ← integer fixture "lastIndex" 0
  let writable ← flag fixture "writable" true
  let modified : OrdinaryObject := {object with own := [(lastIndexKey,.data (.number lastIndex) writable false false)]}
  let ambient := {constructed.base.base.regexp.ambient with objects := constructed.base.base.regexp.ambient.objects.set reference modified}
  let mut world := LookaheadRegExp.withAmbient constructed ambient
  let mut observations : List Json := []
  for query in ← entries fixture "queries" do
    let input ← units query
    let .ok (value, after) := LookaheadRegExp.invokeExec (.object reference) [.string input] world | return failed
    world := after
    observations := observations ++ [Json.mkObj [("value",← encodeMatch world value),("lastIndex",← lastDescriptor world reference)]]
  pure (Json.mkObj [("ok",toJson true),("tuple",toJson [← encoded first,← encoded name]),
    ("source",toJson ((LiteralLookahead.escapeSlashes record.originalSource).map UInt16.toNat)),
    ("flags",toJson (record.originalFlags.map UInt16.toNat)),
    ("ownSource",toJson (object.own.lookup (cacheAscii "source")).isSome),
    ("ownFlags",toJson (object.own.lookup (cacheAscii "flags")).isSome),
    ("prototypeStandard",toJson (decide (object.prototype=some 2))),
    ("extensible",toJson object.extensible),("lastIndex",← lastDescriptor world reference),
    ("queries",toJson observations),("oldFrames",toJson (oldFrames initial world))])
private def packet (json : Json) : Except String Json := do
  let source ← field json "source" GetPatternLookahead.pinnedBody
  let some body := parsePatternCacheBody source PatternCache.bindings | return Json.mkObj [("parsed",toJson false)]
  let some nodes := GetPatternLookahead.selectNodes body | return Json.mkObj [("parsed",toJson false)]
  pure (Json.mkObj [("parsed",toJson true),("results",toJson (← (← entries json "cases").mapM (runCase nodes)))])
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= packet with
  | .ok result => (← IO.getStdout).putStrLn result.compress; pure 0
  | .error error => (← IO.getStderr).putStrLn error; pure 1
