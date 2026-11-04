import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.NodeMethodsPush.Generated
import HonoLean.Upstream.SearchEntry.Generated
import HonoLean.Upstream.MethodsLoop.Generated
import HonoLean.Upstream.CreateNullObject.Generated
import HonoLean.Upstream.ECMA2025.StringSet
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
private def decode : String → Value
  | "u" => .undefined | "n" => .null | "f" => .boolean false | "z" => .number 0 | "empty" => .string []
  | "t" => .boolean true | "one" => .number 1 | "text" => .string [120] | _ => .undefined
private def fields (json : Json) (key : String) : Except String (List (JSString × Value)) := do
  (← items json key).mapM fun pair => do
    let pair ← pair.getArr?
    let left ← match pair[0]? with | some value => units value | none => throw "Missing key"
    let right ← match pair[1]? with | some value => value.getStr? | none => throw "Missing value"
    pure (left, decode right)
private def fill (fields : List (JSString × Value)) : OrdinaryObject :=
  fields.foldl (fun object entry => newDataObject object entry.1 entry.2) emptyNullObject
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
  let values ← (object.own.mergeSort (fun a b => keyLE a.1 b.1)).mapM fun (key, descriptor) => do
    match descriptor with
    | .data value writable enumerable configurable => pure <| Json.mkObj [
      ("key", toJson (key.map UInt16.toNat)), ("value", ← encode value), ("writable", toJson writable),
      ("enumerable", toJson enumerable), ("configurable", toJson configurable)]
    | _ => throw "Unexpected accessor output"
  return toJson values
private def own (state : State) (reference : Nat) (key : JSString) : Except String Value := do
  let object ← match state.objects[reference]? with | some object => pure object | none => throw "Missing object"
  match object.own.lookup key with | some (.data value _ _ _) => pure value | _ => throw "Missing own field"
private def asObject : Value → Except String Nat
  | .object reference => pure reference | _ => throw "Expected object"
private def asArray : Value → Except String Nat
  | .array reference => pure reference | _ => throw "Expected array"
private def values (state : State) (reference : Nat) : Except String (List Value) :=
  match state.heap[reference]? with | some values => pure values | none => throw "Missing array"
private def normal : Completion → Except String State
  | .normal state => pure state | _ => throw "Unexpected return"
private def declare (program : List Stmt) (before : State) : Except String State := do
  normal (← (execute 64 defaultSplitLimit program {before with environment := withoutBindings before.environment (declaredNames program)}).mapError reprStr)
private def lookup (state : State) (name : String) : Except String Value := (lookupVariable state name).mapError reprStr
private def parse (source : String) (bindings : List String) (privateNames : List String := []) : Except String (List Stmt) :=
  match parseBlock source bindings privateNames with | some value => pure value | none => throw "Block parse rejected"

private def userHandler (input : Json) (index : Nat) : Except String Value :=
  match input.getObjVal? "handlerCode" with | .ok value => decode <$> value.getStr? | .error _ => pure (.number index)
private def recordRefs (state : State) (registrations : List Json) : Except String (List Nat) := do
  ((← values state 0).zip registrations).mapM fun (value, input) => do
    let row ← asObject value
    asObject (← own state row (← units (← input.getObjVal? "method")))
private def prefixObservation (before after : State) (registrations : List Json) (method : JSString) (returned : Value) : Except String Json := do
  let prior ← values before 0
  let current ← values after 0
  let oldRecords ← recordRefs before registrations
  let oldKeys ← oldRecords.mapM fun reference => do asArray (← own before reference (ascii "possibleKeys"))
  let row ← match current.getLast? with | some value => asObject value | none => throw "Missing stored row"
  let record ← asObject (← own after row method)
  let keys ← asArray (← own after record (ascii "possibleKeys"))
  let keyOrder ← (← values after keys).mapM fun value => match value with
    | .string key => pure (key.map UInt16.toNat) | _ => throw "Expected copied string key"
  let oldRowsKept ← prior.zipIdx.mapM fun (value, index) => do
    let reference ← asObject value
    pure (decide (current[index]? = some value) && decide (after.objects[reference]? = before.objects[reference]?))
  let integer := fun value : Value => match value with | .number n => toJson n | _ => Json.null
  return Json.mkObj [("returned", integer returned), ("count", toJson current.length),
    ("order", integer (← lookup after "order")), ("score", integer (← own after record (ascii "score"))),
    ("method", toJson (method.map UInt16.toNat)), ("handler", ← encode (← own after record (ascii "handler"))),
    ("keys", toJson keyOrder), ("oldRowsKept", toJson (oldRowsKept.all id)),
    ("oldRecordsKept", toJson (oldRecords.all (fun reference => decide (after.objects[reference]? = before.objects[reference]?)))),
    ("oldKeysKept", toJson (oldKeys.all (fun reference => decide (after.heap[reference]? = before.heap[reference]?)))),
    ("rowFresh", toJson (row != record && !prior.contains (.object row) && !oldRecords.contains row)),
    ("recordFresh", toJson (!prior.contains (.object record) && !oldRecords.contains record)),
    ("keysFresh", toJson (keys != 0 && !oldKeys.contains keys)),
    ("privateArrayKept", toJson (decide (after.privates = before.privates)))]

private def runCase (registration : Expr) (collector loop : List Stmt) (all : Value) (helper : NoArgFunction) (observePrefixes : Bool) (json : Json) : Except String Json := do
  let registrations ← items json "registrations"
  let queries ← (← items json "queries").mapM units
  let node ← fields json "nodeEntries"
  let parameter ← fields json "parameterEntries"
  let mode ← text json "parameterMode" "object"
  let startOrder ← match json.getObjVal? "startOrder" with | .ok value => value.getInt? | .error _ => pure 0
  let parameterValue := if mode = "null" then Value.null else if mode = "undefined" then .undefined else .object 2
  let initial : State := {
    environment := [("order", .number startOrder)], heap := [[]],
    objects := [objectPrototypeProjection [(ascii "toString", .data (.function 1) true false true)], fill node, fill parameter, {prototype := some 0}],
    functions := [⟨helper, []⟩, ⟨⟨"opaque-toString", .null⟩, []⟩],
    privates := PrivateStore.ofData ([("methods", 17)]) ([(3, [(17, .array 0)])])}
  let (registered, bound, steps) ← registrations.zipIdx.foldlM (fun (state, bound, steps) (input, index) => do
    let method ← units (← input.getObjVal? "method")
    let events ← (← items input "names").mapM units
    let keys := StringSet.fromTrace events
    let order ← lookup state "order"
    let handler ← userHandler input index
    let entry : State := {state with sets := state.sets ++ [keys], environment := [("curNode", .object 3),
      ("method", .string method), ("handler", handler), ("possibleKeys", .set state.sets.length), ("order", order)]}
    let (returned, after) ← (evalExpression 64 defaultSplitLimit registration entry).mapError reprStr
    let observation ← if observePrefixes then prefixObservation state after registrations method returned else pure Json.null
    return (after, max bound keys.length, if observePrefixes then steps ++ [observation] else steps)) (initial, 0, [])
  let rows ← values registered 0
  let records ← (rows.zip registrations).mapM fun (value, input) => do
    let reference ← asObject value
    let method ← units (← input.getObjVal? "method")
    asObject (← own registered reference method)
  let keyArrays ← records.mapM fun reference => do asArray (← own registered reference (ascii "possibleKeys"))
  let keyOrder ← keyArrays.mapM fun reference => do
    (← values registered reference).mapM fun value => match value with
    | .string key => pure (key.map UInt16.toNat) | _ => throw "Expected string key"
  let order ← lookup registered "order"
  let (after, collectors) ← queries.foldlM (fun (state, prior) query => do
    let collected ← declare collector {state with environment := [("order", order)]}
    let collectorID ← asArray (← lookup collected "handlerSets")
    let activation : State := {collected with environment := [("node", .object 3), ("handlerSets", .array collectorID),
      ("method", .string query), ("nodeParams", .object 1), ("params", parameterValue),
      ("createNullObject", .function 0), ("METHOD_NAME_ALL", all), ("order", order)]}
    let final ← normal (← (runBlock (registrations.length + bound + 103) loop activation).mapError reprStr)
    return (final, prior ++ [collectorID])) (registered, [])
  let allocations := after.objects.drop registered.objects.length
  let allocationIndex := fun value : Value => match value with
    | .object reference => if reference < registered.objects.length then (-1 : Int) else reference - registered.objects.length
    | _ => -1
  let recordParams ← records.mapM fun reference => do
    let value ← (getProperty propertyFuel after.objects reference (ascii "params")).mapError reprStr
    pure (allocationIndex value)
  let collectorValues ← collectors.mapM (values after)
  let recordIndex := fun value => (records.map Value.object).idxOf? value |>.map Int.ofNat |>.getD (-1)
  let collectorParams ← collectorValues.mapM fun elements => elements.mapM fun value => do
    let reference ← asObject value
    pure (allocationIndex (← (getProperty propertyFuel after.objects reference (ascii "params")).mapError reprStr))
  let scores ← records.mapM fun reference => do
    match ← own after reference (ascii "score") with | .number value => pure value | _ => throw "Expected score"
  let collectorsFresh := collectors.zipIdx |>.all fun (reference, index) =>
    reference != 0 && !keyArrays.contains reference && !(collectors.take index).contains reference
  let storedShape ← (rows.zipIdx).mapM fun (value, index) => do
    let outer ← asObject value
    let input ← match registrations[index]? with | some input => pure input | none => throw "Missing input"
    let method ← units (← input.getObjVal? "method")
    let handlerValue ← userHandler input index
    let record ← match records[index]? with | some record => pure record | none => throw "Missing record"
    let row ← match after.objects[outer]? with | some row => pure row | none => throw "Missing row"
    let handler ← match after.objects[record]? with | some handler => pure handler | none => throw "Missing handler"
    let keyArray ← match keyArrays[index]? with | some keyArray => pure keyArray | none => throw "Missing keys"
    return decide (row.prototype = some 0) && decide (row.own.length = 1) &&
      decide (row.own.lookup method = some (.data (.object record) true true true)) && decide (handler.prototype = some 0) &&
      decide ((← own after record (ascii "handler")) = handlerValue) && decide ((← own after record (ascii "possibleKeys")) = .array keyArray)
  return Json.mkObj ((if observePrefixes then [("registrationSteps", toJson steps)] else []) ++ [("collectors", toJson (collectorValues.map (List.map recordIndex))),
    ("recordParams", toJson recordParams), ("collectorParams", toJson collectorParams),
    ("allocations", toJson (← allocations.mapM entries)), ("nullPrototypes", toJson (allocations.all (fun object => object.prototype.isNone))),
    ("keyOrder", toJson keyOrder), ("scores", toJson scores), ("order", match order with | .number value => toJson value | _ => Json.null),
    ("collectorsFresh", toJson collectorsFresh),
    ("storedShape", toJson (decide (after.heap[(0 : Nat)]? = registered.heap[(0 : Nat)]?) && storedShape.all id))])

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let registration ← match parseExpression (← text packet "registrationSource" NodeMethodsPush.pinnedSource)
        ["curNode", "method", "handler", "possibleKeys", "order"] ["methods"] with
      | some value => pure value | none => throw "Registration parse rejected"
    let collector ← parse (← text packet "collectorSource" SearchEntry.pinnedCollectorSource) []
    let loop ← parse (← text packet "loopSource" MethodsLoop.pinnedSource)
      ["node", "method", "nodeParams", "params", "handlerSets", "createNullObject", "METHOD_NAME_ALL"] ["methods"]
    let allExpr ← match parseExpression SearchEntry.pinnedAllSource [] with | some value => pure value | none => throw "ALL parse rejected"
    let (all, _) ← (evalExpression 32 defaultSplitLimit allExpr {}).mapError reprStr
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some value => pure value | none => throw "Helper parse rejected"
    let observePrefixes ← match packet.getObjVal? "observePrefixes" with | .ok value => value.getBool? | .error _ => pure false
    return toJson (← (← items packet "cases").mapM (runCase registration collector loop all helper observePrefixes))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
