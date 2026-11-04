import HonoLean.Upstream.SourceSubset.PrivateControl
import HonoLean.Upstream.SourceSubset.ObjectInit
import HonoLean.Upstream.NodeCaptureCollect.Generated
import HonoLean.Upstream.NodeParamsInit.Generated
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.CreateNullObject.Generated
import HonoLean.Upstream.NodePrivateCall.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)
private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid UTF16 unit"
private def items (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok value => (·.toList) <$> value.getArr? | .error _ => pure []
private def text (json : Json) (key fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok value => value.getStr? | .error _ => pure fallback
private def natural (json : Json) (key : String) : Except String Nat :=
  match json.getObjVal? key with | .ok value => value.getNat? | .error _ => pure 0
private def boolean (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with | .ok value => value.getBool? | .error _ => pure false
private def decode (code : String) : Value :=
  if code.startsWith "r" then .object (4 + ((code.drop 1).toString.toNat?.getD 0)) else
  match code with
  | "u" => .undefined | "n" => .null | "f" => .boolean false | "z" => .number 0
  | "empty" => .string [] | "t" => .boolean true | "one" => .number 1 | "text" => .string [120] | "ctor" => .objectConstructor
  | _ => .undefined
private def fields (json : Json) (key : String) : Except String (List (JSString × Value)) := do
  (← items json key).mapM fun pair => do
    let pair ← pair.getArr?
    let left ← match pair[0]? with | some value => units value | none => throw "Missing key"
    let right ← match pair[1]? with | some value => value.getStr? | none => throw "Missing value"
    pure (left, decode right)
private def fill (base : OrdinaryObject) (fields : List (JSString × Value)) : OrdinaryObject :=
  fields.foldl (fun object entry => newDataObject object entry.1 entry.2) base
private def encode : Value → Except String Json
  | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
  | .null => pure <| Json.mkObj [("kind", toJson "null")]
  | .boolean value => pure <| Json.mkObj [("kind", toJson "bool"), ("value", toJson value)]
  | .number value => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson value)]
  | .string value => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (value.map UInt16.toNat))]
  | .objectConstructor => pure <| Json.mkObj [("kind", toJson "constructor")]
  | .object reference => pure <| Json.mkObj [("kind", toJson "object"), ("ref", toJson reference)]
  | _ => throw "Unsupported observed capture value"
private def keyLE : JSString → JSString → Bool
  | [], _ => true | _ :: _, [] => false
  | a :: rest, b :: tail => if a = b then keyLE rest tail else decide (a.toNat < b.toNat)
private def entries (object : OrdinaryObject) : Except String Json := do
  let result ← (object.own.mergeSort (fun a b => keyLE a.1 b.1)).mapM fun (key, descriptor) => do
    match descriptor with
    | .data value writable enumerable configurable => pure <| Json.mkObj [
      ("key", toJson (key.map UInt16.toNat)), ("value", ← encode value), ("writable", toJson writable),
      ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
    | _ => throw "Expected data output"
  return toJson result
private def data (state : State) (reference : Nat) (key : String) : Except String Value := do
  let object ← match state.objects[reference]? with | some object => pure object | none => throw "Missing object"
  match object.own.lookup (ascii key) with | some (.data value _ _ _) => pure value | _ => throw "Missing data field"

private def runCase (program : PrivateMethod) (initializer : ObjectInitDecl) (full : List PrivateControlStmt) (helper : NoArgFunction) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let keys ← (← items json "records").mapM fun item => do (← item.getArr?).toList.mapM units
  let rows ← items json "rows"
  let priorCount ← natural json "priorCount"
  let priorRecords ← (← items json "priorRecords").mapM Json.getNat?
  let shared ← boolean json "shared"
  let ordinary ← boolean json "ordinaryParent"
  let missingMatch ← boolean json "missingMatch"
  let name ← units (← json.getObjVal? "name")
  let captured ← decode <$> text json "capture" "text"
  let node ← fields json "nodeEntries"
  let inheritedNode ← fields json "inheritedNode"
  let records := keys.zipIdx |>.map fun (_, index) => fill {prototype := some 0}
    [(ascii "handler", .number index), (ascii "possibleKeys", .array index),
     (ascii "score", .number (100 + index)), (ascii "params", .object 3)]
  let pairs ← rows.zipIdx |>.mapM fun (row, index) => do
    let nullPrototype ← boolean row "nullPrototype"
    let inherited ← fields row "inherited"
    let own ← fields row "own"
    let prototype := 4 + records.length + 2 * index
    pure [fill emptyNullObject inherited, fill {prototype := if nullPrototype then none else some prototype} own]
  let owner := 4 + records.length + 2 * rows.length
  let collector := keys.length
  let methodArray := collector + 1
  let methodValues := rows.zipIdx |>.map fun (_, index) => Value.object (5 + records.length + 2 * index)
  let callerNames := [("methods", 17), ("params", 18), ("pushHandlerSets", 19)]
  let closure : PrivateMethodClosure := ⟨program,
    [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL"))], callerNames⟩
  let table : PrivateMethodTable := ⟨1, [closure]⟩
  let parent := if shared then 2 else 1
  let parentObject := fill {prototype := if ordinary then some 0 else if inheritedNode.isEmpty then none else some 3} node
  let before : State := {
    environment := [("node", .object (owner + 1)), ("nextNode", .object owner), ("child", .object owner), ("method", .string method), ("nodeParams", .object 1),
      ("emptyParams", .object 2), ("name", .string name),
      ("params", .number 97),
      ("handlerSets", .array collector), ("createNullObject", .number 99), ("METHOD_NAME_ALL", .string (ascii "POST")),
      ("i", .string (ascii "outer-i")), ("len", .string (ascii "outer-len")),
      ("handlerSet", .string (ascii "outer-handler")), ("key", .string (ascii "outer-key"))] ++ (if missingMatch then [] else [("m", .array (methodArray + 1))]),
    objects := [objectPrototypeProjection [], parentObject, (if shared then parentObject else emptyNullObject),
      fill (fill emptyNullObject inheritedNode) [(ascii "marker", .string (ascii "prior"))]] ++ records ++ pairs.flatten ++ List.replicate 3 {prototype := some 0},
    heap := keys.map (List.map Value.string) ++ [List.replicate priorCount (.object 3) ++ priorRecords.map (fun index => Value.object (4 + index)), methodValues, [captured]],
    thisValue := .object (owner + 2),
    functions := [⟨helper, []⟩], privates := ⟨callerNames,
      [(owner, [(17, .data (.array methodArray))]), (owner + 1, [(18, .data (.object parent))]),
       (owner + 2, [(19, .method (.function 1))])]⟩}
  let budget := 512 + rows.length * 16 + (keys.map List.length).foldl (· + ·) 0
  let initialized ← (executeObjectInit budget defaultSplitLimit initializer before).mapError reprStr
  let completion ← (executePrivateControl budget defaultSplitLimit table full initialized).mapError reprStr
  let after ← match completion with | .normal state => pure state | _ => throw "Unexpected return"
  let result ← (lookupVariable after "params").mapError reprStr
  if !(decide (after.environment = ("params",result)::before.environment) && decide (after.privates.names = before.privates.names) &&
      decide (after.thisValue = before.thisValue)) then
    throw "Caller environment/private scope/this changed"
  let allocated := after.objects.drop before.objects.length
  let allocationIndex := fun value : Value => match value with
    | .object reference => if reference < before.objects.length then (-1 : Int) else reference - before.objects.length
    | _ => -1
  let recordParams ← records.zipIdx |>.mapM fun (_, index) => allocationIndex <$> data after (4 + index) "params"
  let collected ← match after.heap[collector]? with | some values => pure values | none => throw "Missing collector"
  let collectedIDs := collected.map fun value => match value with
    | .object reference => if reference = 3 then (-1 : Int) else reference - 4 | _ => -2
  let collectorParams ← collected.mapM fun value => do
    match value with
    | .object 3 => pure (-1 : Int)
    | .object reference => allocationIndex <$> data after reference "params"
    | _ => throw "Unexpected collector element"
  let unchangedObject := fun index => decide (after.objects[index]? = before.objects[index]?)
  let methodsKept := decide (after.privates = before.privates) && decide (after.heap[methodArray]? = before.heap[methodArray]?) &&
    (List.range 4).all unchangedObject &&
    (List.range (2 * rows.length)).all (fun offset => unchangedObject (4 + records.length + offset))
  let keysKept := (List.range keys.length).all (fun index => decide (after.heap[index]? = before.heap[index]?) &&
    decide ((after.objects[4 + index]?.map (fun object => object.own.lookup (ascii "possibleKeys"))) = some (some (.data (.array index) true true true))))
  let handlerFieldsKept ← records.zipIdx |>.mapM fun (_, index) => do
    pure (decide ((← data after (4 + index) "handler") = .number index) &&
      decide ((← data after (4 + index) "score") = .number (100 + index)))
  let scope ← ["i", "len", "handlerSet", "key"].mapM fun name => do
    match ← (lookupVariable after name).mapError reprStr with
    | .string value => pure <| String.ofList (value.map (Char.ofNat ∘ UInt16.toNat))
    | _ => throw "Outer binding changed"
  return Json.mkObj [("freshParams", ← encode result), ("collector", toJson collectedIDs), ("recordParams", toJson recordParams),
    ("collectorParams", toJson collectorParams), ("allocations", toJson (← allocated.mapM entries)),
    ("freshOrdinary", toJson (match allocated.head? with | some object => decide (object.prototype = some 0 ∧ object.extensible = true) | none => false)),
    ("nullPrototypes", toJson ((allocated.drop 1).all (fun object => object.prototype.isNone))),
    ("methodsKept", toJson methodsKept), ("keysKept", toJson keysKept),
    ("handlerFieldsKept", toJson (handlerFieldsKept.all id)), ("scope", toJson scope)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let methodSource ← text packet "methodSource" NodePrivateCall.pinnedMethodSource
    let initSource ← text packet "initSource" NodeParamsInit.pinnedSource
    let source ← text packet "source" NodeCaptureCollect.pinnedSource
    let privateNames := ["methods", "children", "patterns", "pattern", "params", "pushHandlerSets"]
    let bindings := ["node", "child", "method", "params", "handlerSets", "name", "m"]
    let program ← match parsePrivateMethod methodSource ["createNullObject", "METHOD_NAME_ALL", "Object"] privateNames with
      | some value => pure value | none => throw "Method parse rejected"
    let initializer ← match parseObjectInit initSource ["node", "emptyParams"] privateNames with
      | some value => pure value | none => throw "Initializer parse rejected"
    let full ← match parsePrivateControl source bindings privateNames with
      | some value => pure value | none => throw "Guard+call parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some value => pure value | none => throw "Helper parse rejected"
    return toJson (← (← items packet "cases").mapM (runCase program initializer full helper))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
