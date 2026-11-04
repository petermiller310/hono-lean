import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.CreateNullObject.Generated
import HonoLean.Upstream.MethodsLoop.Generated
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
  | "empty" => .string [] | "t" => .boolean true | "one" => .number 1 | "text" => .string [120]
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

private def runCase (program : List Stmt) (helper : NoArgFunction) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let keys ← (← items json "records").mapM fun item => do (← item.getArr?).toList.mapM units
  let rows ← items json "rows"
  let priorCount ← natural json "priorCount"
  let node ← fields json "nodeEntries"
  let parameter ← fields json "parameterEntries"
  let parameterMode ← text json "parameterMode" "object"
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
  let before : State := {
    environment := [("node", .object owner), ("method", .string method), ("nodeParams", .object 1),
      ("params", if parameterMode = "null" then .null else if parameterMode = "undefined" then .undefined else .object 2),
      ("handlerSets", .array collector), ("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL")),
      ("i", .string (ascii "outer-i")), ("len", .string (ascii "outer-len")),
      ("m", .string (ascii "outer-m")), ("handlerSet", .string (ascii "outer-handler")), ("key", .string (ascii "outer-key"))],
    objects := [objectPrototypeProjection [], fill emptyNullObject node, fill emptyNullObject parameter,
      fill emptyNullObject [(ascii "marker", .string (ascii "prior"))]] ++ records ++ pairs.flatten ++ [{prototype := some 0}],
    heap := keys.map (List.map Value.string) ++ [List.replicate priorCount (.object 3), methodValues],
    functions := [⟨helper, []⟩], privates := PrivateStore.ofData ([("methods", 17)]) ([(owner, [(17, .array methodArray)])])}
  let budget := 512 + rows.length * 16 + (keys.map List.length).foldl (· + ·) 0
  let completed ← (runBlock budget program before).mapError reprStr
  let after ← match completed with | .normal state => pure state | _ => throw "Unexpected return"
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
    (List.range (2 * rows.length)).all (fun offset => unchangedObject (4 + records.length + offset))
  let keysKept := (List.range keys.length).all (fun index => decide (after.heap[index]? = before.heap[index]?))
  let handlerFieldsKept ← records.zipIdx |>.mapM fun (_, index) => do
    pure (decide ((← data after (4 + index) "handler") = .number index) &&
      decide ((← data after (4 + index) "score") = .number (100 + index)))
  let scope ← ["i", "len", "m", "handlerSet", "key"].mapM fun name => do
    match ← (lookupVariable after name).mapError reprStr with
    | .string value => pure <| String.ofList (value.map (Char.ofNat ∘ UInt16.toNat))
    | _ => throw "Outer binding changed"
  return Json.mkObj [("collector", toJson collectedIDs), ("recordParams", toJson recordParams),
    ("collectorParams", toJson collectorParams), ("allocations", toJson (← allocated.mapM entries)),
    ("nullPrototypes", toJson (allocated.all (fun object => object.prototype.isNone))),
    ("methodsKept", toJson methodsKept), ("keysKept", toJson keysKept),
    ("handlerFieldsKept", toJson (handlerFieldsKept.all id)), ("scope", toJson scope)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let source ← text packet "source" MethodsLoop.pinnedSource
    let program ← match parseBlock source ["node", "method", "nodeParams", "params", "handlerSets", "createNullObject", "METHOD_NAME_ALL",
        "i", "len", "m", "handlerSet", "key"] ["methods"] with
      | some value => pure value | none => throw "Outer loop parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some value => pure value | none => throw "Helper parse rejected"
    return toJson (← (← items packet "cases").mapM (runCase program helper))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
