import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.CreateNullObject.Generated
import HonoLean.Upstream.NodeParamLoop.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"

private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "object" => .object <$> (← json.getObjVal? "ref").getNat?
  | "array" => .array <$> (← json.getObjVal? "ref").getNat?
  | "function" => .function <$> (← json.getObjVal? "ref").getNat?
  | "constructor" => pure .objectConstructor
  | _ => throw "Unknown packet value"

private def encode (value : Value) : Json :=
  let tag (name : String) (fields : List (String × Json) := []) :=
    Json.mkObj (("kind", toJson name) :: fields)
  match value with
  | .undefined => tag "undefined"
  | .null => tag "null"
  | .boolean value => tag "bool" [("value", toJson value)]
  | .number value => tag "number" [("value", toJson value)]
  | .string value => tag "string" [("units", toJson (value.map UInt16.toNat))]
  | .object reference => tag "object" [("ref", toJson reference)]
  | .array reference => tag "array" [("ref", toJson reference)]
  | .function reference => tag "function" [("ref", toJson reference)]
  | .objectConstructor => tag "constructor"
  | .set reference => tag "set" [("ref", toJson reference)]
  | .setConstructor => tag "set-constructor"

private def stringField (json : Json) (name fallback : String) : Except String String :=
  match json.getObjVal? name with | .ok value => value.getStr? | .error _ => pure fallback

private def arrayField (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with | .ok value => (·.toList) <$> value.getArr? | .error _ => pure []

private def fill (object : OrdinaryObject) (entries : List Json) : Except String OrdinaryObject := do
  entries.foldlM (fun current entry => do
    let key ← units (← entry.getObjVal? "key")
    let value ← decode (← entry.getObjVal? "value")
    return newDataObject current key value) object

private def keyLE : JSString → JSString → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then keyLE as bs else decide (a.toNat < b.toNat)

private def runCase (program : List Stmt) (helper : NoArgFunction) (json : Json) : Except String Json := do
  let keys ← (← (← json.getObjVal? "keys").getArr?).toList.mapM units
  let mode ← stringField json "parameterMode" "nullproto"
  let nodeMode ← stringField json "nodeMode" "node"
  let prior ← (← arrayField json "priorHandlers").mapM fun value => Value.object <$> value.getNat?
  let node ← fill {prototype := some 0} (← arrayField json "nodeEntries")
  let parameter ← fill (if mode = "ordinary" then {prototype := some 0} else emptyNullObject)
    (← arrayField json "parameterEntries")
  let oldParamsSelf ← match json.getObjVal? "oldParamsSelf" with
    | .ok value => value.getBool? | .error _ => pure false
  let handler := newDataObject (newDataObject {prototype := some 0} (ascii "possibleKeys") (.array 0))
    (ascii "params") (.object (if oldParamsSelf then 3 else 4))
  let parameterValue := if mode = "undefined" then Value.undefined else if mode = "null" then .null
    else if mode = "handler" then .object 3 else .object 2
  let shadow ← match json.getObjVal? "shadowObject" with
    | .ok value => value.getBool? | .error _ => pure false
  let before : State := {
    environment := [("handlerSet", .object 3), ("handlerSets", .array 1), ("params", parameterValue),
      ("nodeParams", .object (if nodeMode = "handler" then 3 else 1)), ("createNullObject", .function 0),
      ("i", .number 55), ("len", .number 66), ("key", .string (ascii "outer")),
      ("Object", if shadow then .null else .objectConstructor)]
    objects := [objectPrototypeProjection [], node, parameter, handler,
      newDataObject emptyNullObject (ascii "old") (.string (ascii "untouched")),
      newDataObject emptyNullObject (ascii "marker") (.string (ascii "prior"))]
    heap := [keys.map Value.string, prior]
    functions := [⟨helper, []⟩]
  }
  let result ← (runBlock (keys.length + 64) program before).mapError reprStr
  let after ← match result with | .normal state => pure state | .returned _ _ => throw "Unexpected return"
  let output ← (getProperty propertyFuel after.objects 3 (ascii "params")).mapError reprStr
  let reference ← match output with | .object reference => pure reference | _ => throw "Expected object output"
  let object ← match after.objects[reference]? with | some object => pure object | none => throw "Missing output"
  let entries ← ((object.own.mergeSort (fun a b => keyLE a.1 b.1)).mapM fun (key, descriptor) =>
    match descriptor with
    | .data value writable enumerable configurable => pure <| Json.mkObj [
        ("key", toJson (key.map UInt16.toNat)), ("value", encode value),
        ("writable", toJson writable), ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
    | _ => throw "Expected data output")
  let handlers ← match after.heap[1]? with | some handlers => pure handlers | none => throw "Missing handlers"
  let scope ← ["i", "len", "key"].mapM fun name => (lookupVariable after name).mapError reprStr
  let handlerAfter ← match after.objects[3]? with | some handler => pure handler | none => throw "Missing handler"
  let filterParams (object : OrdinaryObject) : List (JSString × PropertyDescriptor) :=
    object.own.filter (fun entry => entry.1 != ascii "params")
  let functionsView (state : State) : List (String × List (String × Value)) := state.functions.map fun definition =>
    (definition.program.name, definition.environment)
  let objectFrame := (List.range 6).all fun index => index = 3 || decide (after.objects[index]? = before.objects[index]?)
  let frame : Bool := objectFrame && decide (after.environment = before.environment) &&
    decide (after.objects.length = 7) && decide (after.heap[(0 : Nat)]? = before.heap[(0 : Nat)]?) &&
    decide (after.heap.length = before.heap.length) && decide (functionsView after = functionsView before) &&
    decide (filterParams handlerAfter = filterParams handler) &&
    decide (handlerAfter.prototype = handler.prototype) && decide (handlerAfter.extensible = handler.extensible)
  let oldOutputIntact := decide (after.objects[4]? = before.objects[4]?)
  return Json.mkObj [("output", encode output), ("fresh", toJson (decide (reference ≥ before.objects.length))),
    ("nullPrototype", toJson object.prototype.isNone), ("entries", toJson entries),
    ("handlerSets", toJson (handlers.map encode)), ("scope", toJson (scope.map encode)),
    ("frameKept", toJson frame), ("oldOutputIntact", toJson oldOutputIntact)]

def main : IO Unit := do
  let text ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let json ← Json.parse text
    let source ← stringField json "source" NodeParamLoop.pinnedSource
    let program ← match parseBlock source ["handlerSet", "handlerSets", "params", "nodeParams", "createNullObject",
        "i", "len", "key", "Object"] with
      | some program => pure program | none => throw "Block parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with
      | some helper => pure helper | none => throw "Pinned helper parse rejected"
    let cases ← (← (← json.getObjVal? "cases").getArr?).toList.mapM (runCase program helper)
    return toJson cases
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
