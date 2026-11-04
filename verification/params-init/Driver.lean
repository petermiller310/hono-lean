import HonoLean.Upstream.SourceSubset.ObjectInit
import HonoLean.Upstream.NodeParamsInit.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

set_option autoImplicit false

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Invalid UTF16 unit"

private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "array" => .array <$> (← json.getObjVal? "ref").getNat?
  | "object" => .object <$> (← json.getObjVal? "ref").getNat?
  | "constructor" => pure .objectConstructor
  | _ => throw "Unsupported fixture value"

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
  | .objectConstructor => pure <| kind "constructor"
  | _ => throw "Unregistered output value"

private def descriptor (json : Json) : Except String (JSString × PropertyDescriptor) := do
  let key ← units (← json.getObjVal? "key")
  let enumerable ← (← json.getObjVal? "enumerable").getBool?
  let configurable ← (← json.getObjVal? "configurable").getBool?
  let value ← match ← (← json.getObjVal? "kind").getStr? with
    | "data" =>
      let captured ← decode (← json.getObjVal? "value")
      let writable ← (← json.getObjVal? "writable").getBool?
      pure <| PropertyDescriptor.data captured writable enumerable configurable
    | "accessor" =>
      let getter ← match ← (← json.getObjVal? "getter").getStr? with
        | "missing" => pure Getter.missing | "prototype" => pure .prototype | "unsupported" => pure .unsupported
        | _ => throw "Unknown getter"
      let setter ← match ← (← json.getObjVal? "setter").getStr? with
        | "missing" => pure Setter.missing | "prototype" => pure .prototype | "unsupported" => pure .unsupported
        | _ => throw "Unknown setter"
      pure <| .accessor getter setter enumerable configurable
    | _ => throw "Unknown descriptor"
  pure (key,value)

private def object (json : Json) : Except String OrdinaryObject := do
  let prototype ← match ← json.getObjVal? "prototype" with
    | .null => pure none | value => some <$> value.getNat?
  pure ⟨← (← (← json.getObjVal? "own").getArr?).toList.mapM descriptor, prototype,
    ← (← json.getObjVal? "extensible").getBool?⟩

private def encodeObject (object : OrdinaryObject) : Except String Json := do
  let own ← object.own.mapM fun (key,descriptor) => do
    let common := [("key",toJson (key.map UInt16.toNat))]
    let fields ← match descriptor with
      | .data value writable enumerable configurable => pure [("kind",toJson "data"),("value",← encode value),
          ("writable",toJson writable),("enumerable",toJson enumerable),("configurable",toJson configurable)]
      | .accessor getter setter enumerable configurable =>
        let getter := match getter with | .missing => "missing" | .prototype => "prototype" | .unsupported => "unsupported"
        let setter := match setter with | .missing => "missing" | .prototype => "prototype" | .unsupported => "unsupported"
        pure [("kind",toJson "accessor"),("getter",toJson getter),("setter",toJson setter),
          ("enumerable",toJson enumerable),("configurable",toJson configurable)]
    pure <| Json.mkObj (common++fields)
  pure <| Json.mkObj [("prototype",toJson object.prototype),("extensible",toJson object.extensible),("own",toJson own)]

private def runCase (program : ObjectInitDecl) (json : Json) : Except String Json := do
  let heap ← (← (← json.getObjVal? "heap").getArr?).toList.mapM fun row => do
    (← row.getArr?).toList.mapM decode
  let objectRows ← (← json.getObjVal? "objects").getArr?
  let objects ← objectRows.toList.zipIdx.mapM fun (row,index) => do
    if index=0 then
      if (← (← row.getObjVal? "intrinsicPrototype").getBool?) then pure (objectPrototypeProjection [])
      else throw "Expected intrinsic prototype projection atO0"
    else object row
  let node ← (← json.getObjVal? "node").getNat?
  let source ← (← json.getObjVal? "source").getNat?
  let empty ← (← json.getObjVal? "emptyParams").getNat?
  if node=0 || node≥objects.length || source≥objects.length || empty≥objects.length then throw "Invalid fixture reference"
  let environment := [("node",Value.object node),("emptyParams",.object empty),("params",.number 97),
    ("offset",.number 91),("p",.number 92)]
  let before : State := {
    environment := environment
    heap := heap
    objects := objects
    thisValue := .object node
    sets := [[[120]]]
    privates := ⟨[("params",0),("frame",1)],[(node,[(0,.data (.object source)),(1,.data (.number 23))])]⟩
  }
  match executeObjectInit 1024 defaultSplitLimit program before with
  | .error _ => pure <| Json.mkObj [("ok",toJson false)]
  | .ok after =>
    let result ← (lookupVariable after "params").mapError reprStr
    let slot ← (privateGet (.object node) "params" after).mapError reprStr
    let scope := after.environment==("params",result)::before.environment && after.heap==before.heap &&
      after.sets==before.sets && after.thisValue==before.thisValue && decide (after.privates=before.privates) &&
      after.functions.length==before.functions.length && after.objects[0]?==before.objects[0]?
    let encoded ← after.objects.zipIdx.mapM fun (value,index) =>
      if index=0 then pure <| Json.mkObj [("intrinsicPrototype",toJson true)] else encodeObject value
    pure <| Json.mkObj [("ok",toJson true),("scope",toJson scope),("result",← encode result),("slot",← encode slot),
      ("objects",toJson encoded),("heap",toJson (← after.heap.mapM (List.mapM encode))),
      ("fresh",toJson (after.objects.length==before.objects.length+1 && result==.object before.objects.length))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let result : Except String Json := do
    let packet ← Json.parse input
    let source ← match packet.getObjVal? "source" with | .ok value => value.getStr? | .error _ => pure NodeParamsInit.pinnedSource
    match parseObjectInit source ["node","emptyParams"] ["params"] with
    | none => pure <| Json.mkObj [("parsed",toJson false)]
    | some program => pure <| Json.mkObj [("parsed",toJson true),
        ("results",toJson (← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase program)))]
  match result with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw <| IO.userError message
