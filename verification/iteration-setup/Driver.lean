import HonoLean.Upstream.SourceSubset.PrivateControl
import HonoLean.Upstream.SourceSubset.PrivateClass
import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodeIterationSetup.Generated
import HonoLean.Upstream.NodePrivateWrite.Generated
import HonoLean.Upstream.NodeMethodsPush.Generated
import HonoLean.Upstream.RegistrationHistory.Contract
import HonoLean.Upstream.CreateNullObject.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (s : String) : JSString := s.toList.map (UInt16.ofNat ∘ Char.toNat)
private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun x => do
    let n ← x.getNat?
    if n < 65536 then pure (UInt16.ofNat n) else throw "Invalid UTF16 unit"
private def items (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok v => (·.toList) <$> v.getArr? | .error _ => pure []
private def text (json : Json) (key fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok v => v.getStr? | .error _ => pure fallback
private def boolean (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with | .ok v => v.getBool? | .error _ => pure false
private def string (json : Json) (key : String) (fallback : JSString) : Except String JSString :=
  match json.getObjVal? key with | .ok v => units v | .error _ => pure fallback
private def primitive : String → Value
  | "u" => .undefined | "n" => .null | "f" => .boolean false | "t" => .boolean true
  | "z" => .number 0 | "one" => .number 1 | "empty" => .string [] | "text" => .string [120]
  | _ => .undefined
private def inputFields (json : Json) (name : String) : Except String OrdinaryObject := do
  let entries ← (← items json name).mapM fun pair => do
    let pair ← pair.getArr?
    let key ← match pair[0]? with | some v => units v | none => throw "Missing key"
    let value ← match pair[1]? with | some v => v.getStr? | none => throw "Missing value"
    pure (key, primitive value)
  pure <| entries.foldl (fun object (key, value) => newDataObject object key value) emptyNullObject
private def encode : Value → Except String Json
  | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
  | .null => pure <| Json.mkObj [("kind", toJson "null")]
  | .boolean v => pure <| Json.mkObj [("kind", toJson "bool"), ("value", toJson v)]
  | .number v => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson v)]
  | .string v => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (v.map UInt16.toNat))]
  | _ => throw "Unsupported observation value"
private def objectRef : Value → Except String Nat
  | .object n => pure n | _ => throw "Expected object"
private def arrayRef : Value → Except String Nat
  | .array n => pure n | _ => throw "Expected array"
private def own (state : State) (reference : Nat) (key : JSString) : Except String Value := do
  let object ← match state.objects[reference]? with | some v => pure v | none => throw "Missing object"
  match object.own.lookup key with | some (.data v _ _ _) => pure v | _ => throw "Missing own data"
private def values (state : State) (reference : Nat) : Except String (List Value) :=
  match state.heap[reference]? with | some v => pure v | none => throw "Missing array"
private def normal : Completion → Except String State
  | .normal s => pure s | _ => throw "Unexpected return"
private def privateRead (state : State) (definition : SelectedPrivateClass) (owner : Nat) (name : String) : Except String Value :=
  (privateGet (.object owner) name {state with privates := {state.privates with names := definition.names}}).mapError reprStr
private def link (state : State) (owner : Nat) (key : JSString) (value : Value) : Except String State := do
  let reference ← objectRef (← (privateGet (.object owner) "children" state).mapError reprStr)
  let objects ← (setProperty propertyFuel state.objects reference key value).mapError reprStr
  pure {state with objects}
private def registrations (json : Json) (name : String) : Except String (List RegistrationHistory.Request) := do
  (← items json name).mapM fun r => do
    let method ← units (← r.getObjVal? "method")
    let handler ← (← r.getObjVal? "handler").getInt?
    let keys ← (← items r "keys").mapM units
    pure ⟨method, .number handler, keys⟩
private def keyLE : JSString → JSString → Bool
  | [], _ => true | _ :: _, [] => false
  | a :: left, b :: right => if a = b then keyLE left right else decide (a.toNat < b.toNat)
private def captures (state : State) (reference : Nat) : Except String Json := do
  let object ← match state.objects[reference]? with | some v => pure v | none => throw "Missing capture object"
  let fields ← (object.own.mergeSort (fun a b => keyLE a.1 b.1)).mapM fun (key, descriptor) => do
    match descriptor with
    | .data v _ _ _ => pure <| Json.mkObj [("key", toJson (key.map UInt16.toNat)), ("value", ← encode v)]
    | _ => throw "Unsupported capture accessor"
  pure <| toJson fields

private def names : List String := ["methods", "children", "patterns", "pattern", "params", "pushHandlerSets"]
private def searchBindings : List String := ["parts", "curNodes", "handlerSets", "method"]
private def iterationBindings : List String := ["parts", "curNodes", "handlerSets", "method", "len", "partOffsets", "i"]
private def entryBindings : List String := ["parts", "curNodes", "handlerSets", "method", "len", "partOffsets", "i", "part", "isLast", "tempNodes", "j"]
private structure Programs where
  search : List Stmt
  iteration : List Stmt
  entry : List PrivateControlStmt
private def index (input : Json) (key : String) : Except String Nat :=
  match input.getObjVal? key with | .ok v => v.getNat? | .error _ => pure 0

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (seed : Assignment) (push : Expr) (programs : Programs)
    (input : Json) : Except String Json := do
  let base : State := {
    environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL"))]
    objects := [objectPrototypeProjection [], ← inputFields input "entries", ← inputFields input "laterEntries", emptyNullObject]
    functions := [⟨helper, []⟩] }
  let module ← normal (← (execute 64 defaultSplitLimit preamble base).mapError reprStr)
  let shared ← (lookupVariable module "emptyParams").mapError reprStr
  let (first, world, table) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some v => pure v | none => throw "First definition rejected"
  let (second, _, _table) ← match definePrivateClass fields [method] module world table with
    | some v => pure v | none => throw "Second definition rejected"
  let (root, one) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) module).mapError reprStr
  let (parent, two) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) one).mapError reprStr
  let (literal, three) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) two).mapError reprStr
  let (wildcard, four) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) three).mapError reprStr
  let (foreign, five) ← (instantiatePrivateClass 96 defaultSplitLimit second (some 0) four).mapError reprStr
  let owners := [("root", root), ("parent", parent), ("literal", literal), ("wildcard", wildcard), ("foreign", foreign)]
  let decode := fun (code : String) =>
    match owners.lookup code with
    | some n => Value.object n
    | none => if code = "plain" then .object 3 else primitive code
  let partsInput ← match input.getObjVal? "parts" with
    | .ok v => (← v.getArr?).toList.mapM units
    | .error _ => pure [[108, 105, 116]]
  let nodesInput ← match input.getObjVal? "nodes" with
    | .ok v => (← v.getArr?).toList.mapM fun item => decode <$> item.getStr?
    | .error _ => pure [.object parent]
  let i ← index input "i"
  let j ← index input "j"
  let canonicalNode := nodesInput[j]?.getD .undefined
  let canonicalPart := partsInput[i]?.getD []
  let query ← string input "query" [71, 69, 84]
  let child := decode (← text input "child" "literal")
  let star := decode (← text input "wildcard" "u")
  let branded := [root, parent, literal, wildcard]
  let active := {five with privates := {five.privates with names := first.names}}
  let linked ← match canonicalNode with
    | .object n => if branded.contains n then link active n canonicalPart child else pure active
    | _ => pure active
  let linked ← match child with
    | .object n => if branded.contains n then link linked n [42] star else pure linked
    | _ => pure linked
  let seedOwner := fun (state : State) (value : Value) => do
    match canonicalNode with
    | .object n =>
      if branded.contains n then
        let state := {state with environment := [("child", .object n), ("params", value)] ++ module.environment}
        let (_, after) ← executeAssignment 64 defaultSplitLimit seed state
        pure after
      else pure state
    | _ => pure state
  let seeded ← (seedOwner linked (.object 1)).mapError reprStr
  let literalRegs ← registrations input "literal"
  let starRegs ← registrations input "star"
  let registered ← (RegistrationHistory.runSourceHistory push literal literalRegs seeded).mapError reprStr
  let registered ← (RegistrationHistory.runSourceHistory push wildcard starRegs registered).mapError reprStr
  let methodValue ← privateRead registered first root "pushHandlerSets"
  let partsRef := registered.heap.length
  let nodesRef := partsRef + 1
  let collector := partsRef + 2
  let receiver := decode (← text input "receiver" "root")
  let prepared : State := {registered with
    heap := registered.heap ++ [partsInput.map Value.string, nodesInput, []]
    environment := [("parts", .array partsRef), ("curNodes", .array nodesRef),
      ("handlerSets", .array collector), ("method", .string query)] ++ module.environment
    thisValue := receiver}
  let activateOuter := fun (state : State) => {state with
    environment := ("i", .number (Int.ofNat i)) :: withoutBindings state.environment
      ["i", "part", "isLast", "tempNodes", "j", "node", "nextNode"]}
  let executeIteration := fun (state : State) => do
    let outer := activateOuter state
    let completed ← execute 64 defaultSplitLimit programs.iteration outer
    let state ← match completed with | .normal s => .ok s | _ => .error .unsupported
    let tempValue ← lookupVariable state "tempNodes"
    let temp ← match tempValue with | .array n => .ok n | _ => .error .unsupported
    let fresh := decide (state.heap.length = outer.heap.length + 1) && decide (temp = outer.heap.length)
    let inner : State := {state with environment := ("j", .number (Int.ofNat j)) :: state.environment}
    let completed ← executePrivateControl 512 defaultSplitLimit table programs.entry inner
    let after ← match completed with | .normal s => .ok s | _ => .error .unsupported
    let node ← lookupVariable after "node"
    let next ← lookupVariable after "nextNode"
    if !(decide (after.environment = ("nextNode", next) :: ("node", node) :: inner.environment)) then
      throw .unsupported
    pure (after, temp, fresh)
  let repeated ← boolean input "repeat"
  let executed : Except EvalError (State × Nat × Bool) := do
    let completed ← execute 64 defaultSplitLimit programs.search prepared
    let state ← match completed with | .normal s => .ok s | _ => .error .unsupported
    let (after, temp, fresh) ← executeIteration state
    if repeated then
      let saved := after.environment
      let seeded ← seedOwner after (.object 2)
      let (after, nextTemp, nextFresh) ← executeIteration {seeded with environment := saved}
      pure (after, nextTemp, fresh && nextFresh && nextTemp != temp)
    else pure (after, temp, fresh)
  match executed with
  | .error _ => pure <| Json.mkObj [("ok", toJson false)]
  | .ok (after, temp, queueFresh) =>
    let next ← (lookupVariable after "nextNode").mapError reprStr
    let node ← (lookupVariable after "node").mapError reprStr
    let part ← (lookupVariable after "part").mapError reprStr
    let isLast ← (lookupVariable after "isLast").mapError reprStr
    let len ← (lookupVariable after "len").mapError reprStr
    let offsets ← (lookupVariable after "partOffsets").mapError reprStr
    let label := fun (value : Value) => match owners.find? (fun (_, n) => decide (value = .object n)) with
      | some (name, _) => pure <| Json.mkObj [("kind", toJson name)] | none => encode value
    let rows ← (← values after collector).mapM objectRef
    let parameterRefs ← rows.mapM fun r => do objectRef (← own after r (ascii "params"))
    let observedMatches ← rows.mapM fun r => do
      let handler ← own after r (ascii "handler")
      let score ← own after r (ascii "score")
      let keys ← arrayRef (← own after r (ascii "possibleKeys"))
      let keys ← (← values after keys).mapM fun v => match v with | .string k => pure (k.map UInt16.toNat) | _ => throw "Nonstring key"
      let params ← objectRef (← own after r (ascii "params"))
      let number := fun v => match v with | Value.number n => toJson n | _ => Json.null
      pure <| Json.mkObj [("handler", number handler), ("score", number score), ("keys", toJson keys), ("captures", ← captures after params)]
    let params ← owners.mapM fun (name, owner) => do
      let value ← privateRead after (if name = "foreign" then second else first) owner "params"
      let label := if value = shared then "shared" else if value = .object 1 then "A" else if value = .object 2 then "B" else "unknown"
      pure <| toJson [name, label]
    let methodValues ← [root, parent, literal, wildcard].mapM fun o => privateRead after first o "pushHandlerSets"
    let methodIdentity := first.firstIdentity + fields.length
    let methodTags := [root, parent, literal, wildcard].all fun o =>
      decide (((after.privates.elements.lookup o).bind (fun es => es.lookup methodIdentity)) = some (.method methodValue))
    if !(decide (after.thisValue = receiver) && decide (reprStr after.functions = reprStr prepared.functions) &&
        decide (after.privates.names = first.names) && decide (after.sets = prepared.sets)) then throw "Control caller frame changed"
    let order ← (lookupVariable registered "order").mapError reprStr
    let order := match order with | .number n => toJson n | _ => Json.null
    let number := fun v => match v with | Value.number n => toJson n | _ => Json.null
    let bool := fun v => match v with | Value.boolean b => toJson b | _ => Json.null
    pure <| Json.mkObj [("ok", toJson true), ("next", ← label next), ("node", ← label node),
      ("temp", toJson (← (← values after temp).mapM label)),
      ("setup", Json.mkObj [("len", number len), ("part", ← encode part), ("isLast", bool isLast),
        ("offsetsNull", toJson (decide (offsets = .null))), ("queueFresh", toJson queueFresh),
        ("partsKept", toJson (decide (after.heap[partsRef]? = some (partsInput.map Value.string)))),
        ("nodesKept", toJson (decide (after.heap[nodesRef]? = some nodesInput)))]),
      ("matches", toJson observedMatches), ("sameRecords", toJson (rows.map fun a => rows.map fun b => a == b)),
      ("sameParams", toJson (parameterRefs.map fun a => parameterRefs.map fun b => a == b)), ("params", toJson params),
      ("order", order), ("methodKept", toJson (methodTags && methodValues.all (· == methodValue))),
      ("nullPrototypes", toJson (parameterRefs.all fun n => (after.objects[n]?).any fun o => o.prototype.isNone))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock NodeClass.pinnedPreambleSource ["createNullObject"] with
      | some v => pure v | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"] with
      | some v => pure v | none => throw "Field parse rejected"
    let method ← match parsePrivateMethod NodeClass.pinnedMethodSource ["METHOD_NAME_ALL", "createNullObject", "Object"] names with
      | some v => pure v | none => throw "Method parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with
      | some v => pure v | none => throw "Helper parse rejected"
    let seed ← match parseAssignment NodePrivateWrite.pinnedParameterSource ["child", "params"] names with
      | some v => pure v | none => throw "Seed parse rejected"
    let push ← match parseExpression NodeMethodsPush.pinnedSource ["curNode", "method", "handler", "possibleKeys", "order"] names with
      | some v => pure v | none => throw "Push parse rejected"
    let searchSource ← text packet "searchSource" NodeIterationSetup.pinnedSearchSource
    let search ← match parseBlock searchSource searchBindings names with
      | some v => pure v | none => throw "Search setup parse rejected"
    let iterationSource ← text packet "iterationSource" NodeIterationSetup.pinnedIterationSource
    let iteration ← match parseBlock iterationSource iterationBindings names with
      | some v => pure v | none => throw "Iteration setup parse rejected"
    let entrySource ← text packet "entrySource" NodeIterationSetup.pinnedEntrySource
    let entry ← match parsePrivateControl entrySource entryBindings names with
      | some v => pure v | none => throw "Node entry parse rejected"
    let programs : Programs := ⟨search, iteration, entry⟩
    toJson <$> (← items packet "cases").mapM (runCase preamble fields method helper seed push programs)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
