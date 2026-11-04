import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.SearchEntry.Generated
import HonoLean.Upstream.NodeMethodsPush.Generated
import HonoLean.Upstream.NodeParamLoop.Generated
import HonoLean.Upstream.CreateNullObject.Correctness
import HonoLean.Upstream.ECMA2025.StringSet
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)
private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid UTF16 unit"
private def field (json : Json) (key fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok value => value.getStr? | .error _ => pure fallback
private def boolField (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with | .ok value => value.getBool? | .error _ => pure false
private def jsonList (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok value => do pure (← value.getArr?).toList | .error _ => pure []

private def decode : String → Value
  | "u" => .undefined | "n" => .null | "f" => .boolean false | "t" => .boolean true
  | "z" => .number 0 | "one" => .number 1 | "empty" => .string [] | "text" => .string [120]
  | "direct" => .object 3 | "all" => .object 4 | "row" => .object 2 | "prototype" => .object 0
  | "custom" => .object 1 | "array" => .array 0 | "set" => .set 0 | "function" => .function 0
  | "Object" => .objectConstructor | "Set" => .setConstructor | _ => .undefined
private def encode : Value → Json
  | .undefined => Json.mkObj [("tag", toJson "u")]
  | .null => Json.mkObj [("tag", toJson "n")]
  | .boolean value => Json.mkObj [("tag", toJson "boolean"), ("value", toJson value)]
  | .number value => Json.mkObj [("tag", toJson "number"), ("value", toJson value)]
  | .string value => Json.mkObj [("tag", toJson "string"), ("value", toJson (value.map UInt16.toNat))]
  | .object ref => Json.mkObj [("tag", toJson (match ref with | 0 => "prototype" | 1 => "custom" | 2 => "row" | 3 => "direct" | _ => "all"))]
  | .array _ => Json.mkObj [("tag", toJson "array")]
  | .set _ => Json.mkObj [("tag", toJson "set")]
  | .function _ => Json.mkObj [("tag", toJson "function")]
  | .objectConstructor => Json.mkObj [("tag", toJson "Object")]
  | .setConstructor => Json.mkObj [("tag", toJson "Set")]

private def entries (json : Json) (key : String) : Except String (List (JSString × Value)) := do
  (← jsonList json key).mapM fun pair => do
    let values ← pair.getArr?
    let left ← match values[0]? with | some value => units value | none => throw "Missing key"
    let right ← match values[1]? with | some value => value.getStr? | none => throw "Missing value"
    pure (left, decode right)
private def objectWith (base : OrdinaryObject) (fields : List (JSString × Value)) : OrdinaryObject :=
  fields.foldl (fun object entry => newDataObject object entry.1 entry.2) base
private def parseProgram (source : String) (bindings : List String) (privateNames : List String := []) : Except String (List Stmt) :=
  match parseBlock source bindings privateNames with | some value => pure value | none => throw "Declaration parse rejected"
private def declaration (program : List Stmt) (before : State) : Except String State := do
  let completed ← (execute 64 defaultSplitLimit program
    {before with environment := withoutBindings before.environment (declaredNames program)}).mapError reprStr
  match completed with | .normal state => pure state | _ => throw "Unexpected return"
private def lookup (state : State) (name : String) : Except String Value := (lookupVariable state name).mapError reprStr

private def selectionCase (program : List Stmt) (all : Value) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let own ← entries json "own"
  let inherited ← entries json "inherited"
  let nullPrototype ← boolField json "nullPrototype"
  let omitAll ← boolField json "omitAll"
  let before : State := {
    environment := [("m", .object 2), ("method", .string method)] ++
      (if omitAll then [] else [("METHOD_NAME_ALL", all)]),
    heap := [[]], sets := [[]],
    objects := [objectPrototypeProjection [(ascii "toString", .data (.function 0) true false true)],
      objectWith {prototype := some 0} inherited,
      objectWith {prototype := if nullPrototype then none else some 1} own, emptyNullObject, emptyNullObject],
    functions := [⟨⟨"opaque-function-identity", .null⟩, []⟩]}
  let after ← declaration program before
  return Json.mkObj [("chosen", encode (← lookup after "handlerSet")),
    ("frameKept", toJson (decide (after.objects = before.objects) && decide (after.heap = before.heap) &&
      decide (after.sets = before.sets) && decide (after.privates = before.privates) &&
      (reprStr after.functions == reprStr before.functions)))]

private def data (state : State) (reference : Nat) (key : String) : Except String Value := do
  let object ← match state.objects[reference]? with | some value => pure value | none => throw "Missing object"
  match object.own.lookup (ascii key) with | some (.data value _ _ _) => pure value | _ => throw "Missing data field"
private def asObject : Value → Except String Nat
  | .object reference => pure reference | _ => throw "Expected object"
private def asArray : Value → Except String Nat
  | .array reference => pure reference | _ => throw "Expected array"
private def elements (state : State) (reference : Nat) : Except String (List Value) :=
  match state.heap[reference]? with | some values => pure values | none => throw "Missing array"
private def keyValues : List Value → Except String (List JSString) :=
  List.mapM (fun value => match value with | .string key => pure key | _ => throw "Expected string key")

private def integration (collector row selection : List Stmt) (all : Value) (push : Expr) (loop : List Stmt) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let events ← (← jsonList json "names").mapM units
  let keys := StringSet.fromTrace events
  let count ← (← json.getObjVal? "priorCount").getNat?
  let prior := List.replicate count (.object 5)
  let before : State := {
    environment := [("curNode", .object 4), ("method", .string method), ("handler", .function 1),
      ("possibleKeys", .set 0), ("order", .number 7)],
    heap := [prior, []], sets := [keys],
    objects := [objectPrototypeProjection [],
      objectWith emptyNullObject (keys.map (fun key => (key, .string (ascii "node")))),
      objectWith emptyNullObject (keys.map (fun key => (key, .string (ascii "prior")))),
      {prototype := some 0}, {prototype := some 3},
      newDataObject {prototype := some 0} method (.object 6),
      objectWith {prototype := some 0} [(ascii "handler", .function 2), (ascii "possibleKeys", .array 1), (ascii "score", .number (-1))]],
    functions := [⟨CreateNullObject.createProgram, []⟩, ⟨⟨"handler", .null⟩, []⟩, ⟨⟨"prior-handler", .null⟩, []⟩],
    privates := PrivateStore.ofData ([("methods", 17)]) ([(4, [(17, .array 0)])])}
  let (_, registered) ← (evalExpression 64 defaultSplitLimit push before).mapError reprStr
  let collected ← declaration collector registered
  let collectorID ← asArray (← lookup collected "handlerSets")
  let moduleOrder ← lookup registered "order"
  -- Explicit search-to-helper activation/argument/import transport. No chosen
  -- m or handlerSet is staged; the actual declarations below derive both.
  let activation : State := {collected with environment := [("node", .object 4), ("i", .number count),
    ("method", .string method), ("METHOD_NAME_ALL", all), ("handlerSets", .array collectorID),
    ("params", .object 2), ("nodeParams", .object 1), ("createNullObject", .function 0), ("order", moduleOrder)]}
  let loaded ← declaration row activation
  let selected ← declaration selection loaded
  let mapID ← asObject (← lookup selected "m")
  let handlerID ← asObject (← lookup selected "handlerSet")
  let keyID ← asArray (← data selected handlerID "possibleKeys")
  let selectedKeys ← keyValues (← elements selected keyID)
  let completed ← (runBlock (selectedKeys.length + 64) loop selected).mapError reprStr
  let final ← match completed with | .normal value => pure value | _ => throw "Unexpected capture return"
  let outputID ← asObject (← data final handlerID "params")
  let output ← match final.objects[outputID]? with | some value => pure value | none => throw "Missing capture object"
  let captures ← selectedKeys.mapM fun key => do
    let value ← match output.own.lookup key with | some (.data (.string text) _ _ _) => pure text | _ => throw "Missing string capture"
    pure (toJson [toJson (key.map UInt16.toNat), toJson (value.map UInt16.toNat)])
  let next ← declaration collector final
  let nextID ← asArray (← lookup next "handlerSets")
  let methodArray ← elements final 0
  let collectorValues ← elements final collectorID
  let storedHandler := (final.objects[mapID]?.bind (fun object => object.own.lookup method)).map
    (fun descriptor => match descriptor with | .data value _ _ _ => value | _ => .undefined)
  let score ← data final handlerID "score"
  return Json.mkObj [("collectorFresh", toJson (collectorID != 0 && collectorID != keyID)),
    ("collectorLength", toJson collectorValues.length), ("selectedStoredRow", toJson (methodArray[count]? == some (.object mapID))),
    ("selectedStoredHandler", toJson (storedHandler == some (.object handlerID))),
    ("collectorHasSelected", toJson (collectorValues[0]? == some (.object handlerID))),
    ("handlerKept", toJson ((← data final handlerID "handler") == .function 1)),
    ("captures", toJson captures), ("ownCaptureCount", toJson output.own.length), ("nullPrototype", toJson output.prototype.isNone),
    ("descriptors", toJson (selectedKeys.all fun key => match output.own.lookup key with | some (.data _ true true true) => true | _ => false)),
    ("nextCollectorFreshEmpty", toJson (nextID != collectorID && (← elements next nextID).isEmpty)),
    ("firstCollectorKept", toJson (decide ((← elements next collectorID).length = 1))),
    ("methodsCount", toJson methodArray.length), ("prefixKept", toJson (decide (methodArray.take count = prior))),
    ("score", match score with | .number value => toJson value | _ => Json.null),
    ("orderAfter", match final.environment.lookup "order" with | some (.number value) => toJson value | _ => Json.null),
    ("privateArrayKept", toJson (final.privates.slots.lookup 4 |>.bind (List.lookup 17) |>.map (· == .array 0) |>.getD false))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let collector ← parseProgram (← field packet "collectorSource" SearchEntry.pinnedCollectorSource) []
    let selection ← parseProgram (← field packet "selectionSource" SearchEntry.pinnedSelectionSource) ["m", "method", "METHOD_NAME_ALL"]
    let row ← parseProgram (← field packet "rowSource" SearchEntry.pinnedRowSource) ["node", "i"] ["methods"]
    let allExpr ← match parseExpression (← field packet "allSource" SearchEntry.pinnedAllSource) [] with | some value => pure value | none => throw "ALL parse rejected"
    let (all, _) ← (evalExpression 32 defaultSplitLimit allExpr {}).mapError reprStr
    let push ← match parseExpression NodeMethodsPush.pinnedSource ["curNode", "method", "handler", "possibleKeys", "order"] ["methods"] with | some value => pure value | none => throw "Push parse rejected"
    let loop ← parseProgram NodeParamLoop.pinnedSource ["handlerSet", "handlerSets", "params", "nodeParams", "createNullObject"]
    return Json.mkObj [("results", toJson (← (← jsonList packet "cases").mapM (selectionCase selection all))),
      ("integrations", toJson (← (← jsonList packet "integrations").mapM (integration collector row selection all push loop)))]
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
