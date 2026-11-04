import HonoLean.Upstream.SourceSubset.LabelMatchRealm
import HonoLean.Upstream.LabelMatch.Generated
import HonoLean.Upstream.PatternConstruct.Source
import HonoLean.Upstream.NodePatternBinding.Source
import HonoLean.Upstream.NodeRegExpExec.Source
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean
set_option autoImplicit false

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Invalid UTF16 unit"

private def encode (value : Value) : Except String Json := do
  let kind (name : String) (fields : List (String × Json) := []) := Json.mkObj (("kind",toJson name)::fields)
  match value with
  | .undefined => pure <| kind "undefined"
  | .null => pure <| kind "null"
  | .boolean value => pure <| kind "bool" [("value",toJson value)]
  | .number value => pure <| kind "number" [("value",toJson value)]
  | .string value => pure <| kind "string" [("units",toJson (value.map UInt16.toNat))]
  | .array ref => pure <| kind "array" [("ref",toJson ref)]
  | .object ref => pure <| kind "object" [("ref",toJson ref)]
  | .function ref => pure <| kind "function" [("ref",toJson ref)]
  | _ => throw "Outside fixture output domain"

private def descriptor : Option PropertyDescriptor → Except String Json
  | none => pure .null
  | some (.data value writable enumerable configurable) => do pure <| Json.mkObj [
    ("kind",toJson "data"),("value",← encode value),("writable",toJson writable),
    ("enumerable",toJson enumerable),("configurable",toJson configurable)]
  | some _ => throw "Expected result DATA descriptor"

private def view (state : LabelMatchState) (ref : Nat) : Except String Json := do
  let fields : List (String × LabelResultField) := [("zero",.zero),("one",.one),("two",.two),
    ("length",.length),("index",.index),("input",.input),("groups",.groups)]
  pure <| Json.mkObj (← fields.mapM fun (name,field) => do pure (name,← descriptor (observeLabelResult state ref field)))

private def keyJson : LabelPropertyKey → Json
  | .string key => Json.mkObj [("kind",toJson "string"),("units",toJson (key.map UInt16.toNat))]
  | .symbol .match => Json.mkObj [("kind",toJson "symbol"),("symbol",toJson "match")]
private def eventJson (event : LabelEvent) : Except String Json := do
  let make (name : String) (fields : List (String × Json) := []) := Json.mkObj (("event",toJson name)::fields)
  match event with
  | .receiver value => pure <| make "receiver" [("value",← encode value)]
  | .get receiver key holder value => pure <| make "get" [("receiver",← encode receiver),("key",keyJson key),("holder",toJson holder),("value",← encode value)]
  | .getter callee receiver => pure <| make "getter" [("callee",← encode callee),("receiver",← encode receiver)]
  | .literalAllocated ref => pure <| make "literalAllocated" [("ref",toJson ref)]
  | .initialized ref source flags => pure <| make "initialized" [("ref",toJson ref),("source",toJson (source.map UInt16.toNat)),("flags",toJson (flags.map UInt16.toNat))]
  | .call callee receiver => pure <| make "call" [("callee",← encode callee),("receiver",← encode receiver)]
  | .toString value => pure <| make "toString" [("value",← encode value)]
  | .lastIndex value length => pure <| make "lastIndex" [("value",← encode value),("length",toJson length)]
  | .executed ref => pure <| make "executed" [("ref",toJson ref)]

private def execView (state : RegExpCallState) (reference : Nat) : Except String Json := do
  let fields : List (String × RegExpMatchProperty) := [("zero",.zero),("length",.length),
    ("index",.index),("input",.input),("groups",.groups)]
  pure <| Json.mkObj (← fields.mapM fun (name,field) => do pure (name,← descriptor (observeRegExpResult state reference field)))

private def downstream (before : LabelMatchState) : Except String (LabelMatchState × Json) := do
  let context := labelStandardContext.iterators
  let constructors := context.constructors
  let some expression := parseRegExpConstruct PatternConstruct.pinnedSource PatternConstruct.bindings [] | throw "Constructor parser refused"
  let (tuple,constructed) ← (evalRegExpConstruct 128 defaultSplitLimit constructors expression before.base.regexp).mapError reprStr
  let prepared := {before.base with regexp := {constructed with ambient := {constructed.ambient with
    environment := ("pattern",tuple) :: constructed.ambient.environment}}}
  let some binding := parseArrayBinding NodePatternBinding.pinnedSource ["pattern"] [] | throw "Binding parser refused"
  let (_,bound) ← (runArrayBinding 128 defaultSplitLimit context binding prepared).mapError reprStr
  let some declaration := parseMemberDeclaration NodeRegExpExec.pinnedSource NodeRegExpExec.bindings [] | throw "Exec parser refused"
  let after ← (executeRegExpDeclaration 128 defaultSplitLimit constructors.methods constructors.functions constructors.members constructors.builtins declaration bound.regexp).mapError reprStr
  let result := {before with base := {bound with regexp := after}}
  let .array tupleRef := tuple | throw "Expected tuple"
  let some values := after.ambient.heap[tupleRef]? | throw "Expected tuple contents"
  let some (Value.object matcherRef) := values[2]? | throw "Expected matcher"
  let some record := after.brands.lookup matcherRef | throw "Expected initialized matcher record"
  let some literalObject := after.ambient.objects[matcherRef]? | throw "Expected matcher object"
  let m := (after.ambient.environment.lookup "m").getD .undefined
  let (captures,resultView) ← match m with
    | .null => pure (Json.null,Json.null)
    | .array reference => do
      let some captured := after.ambient.heap[reference]? | throw "Missing match array"
      pure (toJson (← captured.mapM encode),← execView after reference)
    | _ => throw "Expected regexp result"
  let produced := Json.mkObj [("tuple",← encode tuple),("label",← encode (values[0]?.getD .undefined)),
    ("name",← encode (values[1]?.getD .undefined)),("source",toJson (record.originalSource.map UInt16.toNat)),
    ("flags",toJson (record.originalFlags.map UInt16.toNat)),("lastIndex",← descriptor (literalObject.own.lookup lastIndexKey))]
  pure (result,Json.mkObj [("produced",produced),("name",← encode ((after.ambient.environment.lookup "name").getD .undefined)),
    ("matcherSameAsTuple",toJson (decide (after.ambient.environment.lookup "matcher" = some (.object matcherRef)))),
    ("m",← encode m),("execCaptures",captures),("execView",resultView)])

private def runCase (decl : LabelMatchDecl) (pipeline : Bool) (fixture : Json) : Except String (Json × Json) := do
  let input ← units (← fixture.getObjVal? "label")
  let query ← match fixture.getObjVal? "input" with | .ok value => units value | .error _ => pure [49,50]
  let original := labelStandardState input
  let before := if pipeline then {original with base := {original.base with
    regexp := {original.base.regexp with ambient := {original.base.regexp.ambient with
      environment := [("RegExp",.function 6),("restPathString",.string query),("m",.object 5)] ++ original.base.regexp.ambient.environment}}
    symbols := [(.object 3,[(.iterator,.data (.function 7) true false true)])]}} else original
  match executeLabelMatch 128 defaultSplitLimit labelStandardContext decl before with
  | .error error => pure (Json.mkObj [("modelError",toJson (reprStr error))],Json.null)
  | .ok matched =>
    let (after,pipelineResult) ← if pipeline then downstream matched else pure (matched,Json.null)
    let ambient := after.base.regexp.ambient
    let old := before.base.regexp.ambient
    let value := (ambient.environment.lookup "match").getD .undefined
    let arraysPreserved := decide (ambient.heap.take old.heap.length = old.heap)
    let objectsPreserved := decide (ambient.objects.take old.objects.length = old.objects)
    let oldFrames := arraysPreserved && objectsPreserved && decide (ambient.privates = old.privates) &&
      decide (ambient.sets = old.sets) && decide (after.base.symbols = before.base.symbols) &&
      ((List.range old.objects.length).all (fun ref => decide (after.base.iterators.lookup ref = before.base.iterators.lookup ref))) &&
      ((List.range old.objects.length).all (fun ref => decide (after.base.regexp.brands.lookup ref = before.base.regexp.brands.lookup ref))) &&
      ((List.range old.heap.length).all (fun ref => decide (after.base.regexp.results.lookup ref = before.base.regexp.results.lookup ref))) && decide (after.symbols = before.symbols) &&
      decide (after.accessors = before.accessors) && (reprStr ambient.functions == reprStr old.functions)
    let (captures,resultView,ownNames) ← match value with
      | .array ref => do
        let some values := ambient.heap[ref]? | throw "Invalid result reference"
        let names := ((List.range values.length).map toString ++ ["groups","index","input","length"]).mergeSort (fun a b => compare a b != .gt)
        pure (toJson (← values.mapM encode),← view after ref,toJson names)
      | .null => pure (Json.null,Json.null,Json.null)
      | _ => throw "Outside observed result domain"
    let baseFields := [("result",← encode value),("captures",captures),("view",resultView),("ownNames",ownNames),
      ("outerPreserved",toJson (decide (matched.base.regexp.ambient.environment.drop 1 = old.environment))),
      ("thisPreserved",toJson (decide (ambient.thisValue = old.thisValue))),("oldFrames",toJson oldFrames)]
    let observed := Json.mkObj (baseFields ++ if pipeline then [("pipeline",pipelineResult)] else [])
    let some literalRecord := after.brands.lookup old.objects.length | throw "Missing actual literal record"
    let some literalObject := ambient.objects[old.objects.length]? | throw "Missing actual literal object"
    let compiledFromSource := match LabelRegExp.parseLiteral (47 :: literalRecord.source ++ [47]) with
      | none => false
      | some syntaxTree => decide (literalRecord.compiled = LabelRegExp.compile syntaxTree)
    let modelOnly := Json.mkObj [("trace",toJson (← after.trace.mapM eventJson)),
      ("literalCount",toJson (after.brands.length-before.brands.length)),
      ("captureArrayCount",toJson (after.results.length-before.results.length)),
      ("literalLastIndex",← descriptor ((ambient.objects[old.objects.length]?).bind (fun object => object.own.lookup lastIndexKey))),
      ("literalSource",toJson (literalRecord.source.map UInt16.toNat)),("literalFlags",toJson (literalRecord.flags.map UInt16.toNat)),
      ("compiledFromStoredSource",toJson compiledFromSource),("literalPrototype",toJson literalObject.prototype),
      ("literalExtensible",toJson literalObject.extensible)]
    pure (observed,modelOnly)

private def runPacket (packet : Json) : Except String Json := do
  let pipeline ← match packet.getObjVal? "mode" with | .ok value => pure ((← value.getStr?) == "pipeline") | .error _ => pure false
  let source ← match packet.getObjVal? "source" with | .ok value => value.getStr? | .error _ => pure LabelMatch.pinnedSource
  match parseLabelMatch source ["label", "alternateLabel"] with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some decl =>
    let cases ← (← packet.getObjVal? "cases").getArr?
    let results ← cases.toList.mapM (runCase decl pipeline)
    pure <| Json.mkObj [("parsed",toJson true),("results",toJson (results.map Prod.fst)),
      ("modelOnly",toJson (results.map Prod.snd))]

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let text ← stdin.readToEnd
  match Json.parse text >>= runPacket with
  | .ok result => stdout.putStrLn result.compress; pure 0
  | .error error => stderr.putStrLn error; pure 1
