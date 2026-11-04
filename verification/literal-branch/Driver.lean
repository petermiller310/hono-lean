import HonoLean.Upstream.SourceSubset.PrivateControl
import HonoLean.Upstream.SourceSubset.PrivateClass
import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodeLiteralBranch.Generated
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
private def branchBindings : List String := ["node", "part", "isLast", "handlerSets", "tempNodes", "method"]

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (seed : Assignment) (push : Expr) (program : List PrivateControlStmt)
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
  let part ← string input "part" [108, 105, 116]
  let query ← string input "query" [71, 69, 84]
  let child := decode (← text input "child" "literal")
  let star := decode (← text input "wildcard" "u")
  let active := {five with privates := {five.privates with names := first.names}}
  let linked ← link active parent part child
  let linked ← match child with
    | .object n => if [root, parent, literal, wildcard].contains n then link linked n [42] star else pure linked
    | _ => pure linked
  let seeded := {linked with environment := [("child", .object parent), ("params", .object 1)] ++ module.environment}
  let (_, seeded) ← (executeAssignment 64 defaultSplitLimit seed seeded).mapError reprStr
  let literalRegs ← registrations input "literal"
  let starRegs ← registrations input "star"
  let registered ← (RegistrationHistory.runSourceHistory push literal literalRegs seeded).mapError reprStr
  let registered ← (RegistrationHistory.runSourceHistory push wildcard starRegs registered).mapError reprStr
  let methodValue ← privateRead registered first root "pushHandlerSets"
  let collector := registered.heap.length
  let queue := collector + 1
  let priorQueue ← (← items input "prefix").mapM fun item => decode <$> item.getStr?
  let prepared : State := {registered with heap := registered.heap ++ [[], priorQueue]}
  let receiver := decode (← text input "receiver" "root")
  let isLast := decode (← text input "last" "t")
  let activate := fun (state : State) =>
    {state with
      environment := [("node", .object parent), ("part", .string part), ("isLast", isLast),
      ("handlerSets", .array collector), ("tempNodes", .array queue), ("method", .string query)] ++ module.environment
      thisValue := receiver
      privates := {state.privates with names := first.names}}
  let executeBranch := fun (state : State) => executePrivateControl 512 defaultSplitLimit table program (activate state)
  let firstExecution := executeBranch prepared
  let repeated ← boolean input "repeat"
  let executed : Except EvalError Completion := do
    let completed ← firstExecution
    let state ← match completed with | .normal s => .ok s | _ => .error .unsupported
    if repeated then
      let seedState : State := {state with environment := [("child", .object parent), ("params", .object 2)] ++ module.environment}
      let (_, state) ← executeAssignment 64 defaultSplitLimit seed seedState
      executeBranch state
    else pure (.normal state)
  match executed with
  | .error _ => pure <| Json.mkObj [("ok", toJson false)]
  | .ok completed =>
    let after ← normal completed
    let next ← (lookupVariable after "nextNode").mapError reprStr
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
    if !(decide (after.environment = ("nextNode", next) :: (activate prepared).environment) &&
        decide (after.thisValue = receiver) && decide (reprStr after.functions = reprStr prepared.functions) &&
        decide (after.privates.names = first.names) && decide (after.sets = prepared.sets)) then throw "Control caller frame changed"
    let order ← (lookupVariable registered "order").mapError reprStr
    let order := match order with | .number n => toJson n | _ => Json.null
    pure <| Json.mkObj [("ok", toJson true), ("next", ← label next), ("temp", toJson (← (← values after queue).mapM label)),
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
    let source ← text packet "branchSource" NodeLiteralBranch.pinnedSource
    let program ← match parsePrivateControl source branchBindings names with
      | some v => pure v | none => throw "Control parse rejected"
    toJson <$> (← items packet "cases").mapM (runCase preamble fields method helper seed push program)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
