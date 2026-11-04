import HonoLean.Upstream.SourceSubset.PrivateClass
import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodePrivateCall.Program
import HonoLean.Upstream.RegistrationHistory.Correctness
import HonoLean.Upstream.SearchEntry.Collector
import HonoLean.Upstream.CreateNullObject.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)
private def items (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok value => (·.toList) <$> value.getArr? | .error _ => pure []
private def text (json : Json) (key fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok value => value.getStr? | .error _ => pure fallback
private def natural (json : Json) (key : String) (fallback : Nat) : Except String Nat :=
  match json.getObjVal? key with | .ok value => value.getNat? | .error _ => pure fallback
private def lookup (state : State) (name : String) : Except String Value := (lookupVariable state name).mapError reprStr
private def asObject : Value → Except String Nat
  | .object reference => pure reference | _ => throw "Expected object"
private def asArray : Value → Except String Nat
  | .array reference => pure reference | _ => throw "Expected array"
private def readField (state : State) (definition : SelectedPrivateClass) (owner : Nat) (name : String) : Except String Value :=
  (privateGet (.object owner) name {state with privates := {state.privates with names := definition.names}}).mapError reprStr
private def arrayLength (state : State) (value : Value) : Except String Nat := do
  let reference ← asArray value
  match state.heap[reference]? with | some values => pure values.length | none => throw "Missing array"
private def objectAt (state : State) (reference : Nat) : Except String OrdinaryObject :=
  match state.objects[reference]? with | some object => pure object | none => throw "Missing object"

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun unit => do
    let n ← unit.getNat?
    if n < 65536 then pure (UInt16.ofNat n) else throw "Invalid UTF16 unit"
private def decode (code : String) : Value := match code with
  | "u" => .undefined | "n" => .null | "f" => .boolean false | "z" => .number 0
  | "empty" => .string [] | "t" => .boolean true | "one" => .number 1 | "text" => .string [120]
  | _ => .undefined
private def inputObject (json : Json) (name : String) : Except String OrdinaryObject := do
  (← items json name).foldlM (fun object pair => do
    let a ← pair.getArr?
    let key ← match a[0]? with | some x => units x | none => throw "Missing key"
    let value ← match a[1]? with | some x => decode <$> x.getStr? | none => throw "Missing value"
    pure (newDataObject object key value)) emptyNullObject
private def encode : Value → Except String Json
  | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
  | .null => pure <| Json.mkObj [("kind", toJson "null")]
  | .boolean value => pure <| Json.mkObj [("kind", toJson "bool"), ("value", toJson value)]
  | .number value => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson value)]
  | .string value => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (value.map UInt16.toNat))]
  | _ => throw "Unsupported observation"
private def data (state : State) (reference : Nat) (name : String) : Except String Value := do
  let object ← objectAt state reference
  match object.own.lookup (ascii name) with | some (.data value _ _ _) => pure value | _ => throw "Missing data"
private def keyLE : JSString → JSString → Bool
  | [], _ => true | _ :: _, [] => false
  | a :: rest, b :: tail => if a = b then keyLE rest tail else decide (a.toNat < b.toNat)
private def captures (object : OrdinaryObject) : Except String Json := do
  toJson <$> (object.own.mergeSort (fun a b => keyLE a.1 b.1)).mapM (fun (key, descriptor) => do
    match descriptor with
    | .data value _ _ _ => pure <| Json.mkObj [("key", toJson (key.map UInt16.toNat)), ("value", ← encode value)]
    | _ => throw "Expected data capture")

-- Query parameter cells and their handoff are explicit external inputs; this
-- does not execute the surrounding search traversal/private writes.
private def runQuery (initialized : State) (table : PrivateMethodTable)
    (definitions : List SelectedPrivateClass) (instances : List (Nat × Nat)) (input : Json) : Except String Json := do
  let q ← match input.getObjVal? "query" with | .error _ => return Json.null | .ok q => pure q
  let receiverIndex ← natural q "receiver" 0
  let targetIndex ← natural q "target" 0
  let (receiverClass, receiver) ← match instances[receiverIndex]? with | some x => pure x | none => throw "Missing receiver"
  let (targetClass, target) ← match instances[targetIndex]? with | some x => pure x | none => throw "Missing target"
  let receiverDefinition ← match definitions[receiverClass]? with | some x => pure x | none => throw "Missing receiver definition"
  let targetDefinition ← match definitions[targetClass]? with | some x => pure x | none => throw "Missing target definition"
  let requests ← (← items q "registrations").mapM fun r => do
    let method ← units (← r.getObjVal? "method")
    let handler ← (← r.getObjVal? "handler").getInt?
    let events ← (← items r "events").mapM units
    pure (RegistrationHistory.Request.mk method (.number handler) events)
  let push ← match parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames with
    | some value => pure value | none => throw "Push parse rejected"
  let active := {initialized with privates := {initialized.privates with names := targetDefinition.names}}
  let registered ← (RegistrationHistory.runSourceHistory push target requests active).mapError reprStr
  let oldParams ← inputObject q "nodeEntries"
  let temporary ← inputObject q "parameterEntries"
  let oldParamsRef := registered.objects.length
  let tempRef := oldParamsRef + 1
  let ownerElements ← match registered.privates.elements.lookup receiver with | some x => pure x | none => throw "Missing receiver elements"
  let changedElements ← ownerElements.mapM fun (identity, element) => do
    if identity = receiverDefinition.firstIdentity + 4 then
      match element with
      | .data _ => pure (identity, PrivateElement.data (.object oldParamsRef))
      | .method _ => throw "Expected DATA params element"
    else pure (identity, element)
  let staged := {registered with
    objects := registered.objects ++ [oldParams, temporary]
    privates := {registered.privates with
      names := receiverDefinition.names
      elements := (receiver, changedElements) :: registered.privates.elements.filter (fun entry => entry.1 != receiver)}}
  let collectorProgram ← match parseBlock SearchEntry.pinnedCollectorSource [] with
    | some value => pure value | none => throw "Collector parse rejected"
  let collector := staged.heap.length
  let completed ← (runBlock 64 collectorProgram staged).mapError reprStr
  let state ← match completed with | .normal state => pure state | _ => throw "Unexpected collector return"
  let query ← units (← q.getObjVal? "method")
  let caller := {state with environment := [("handlerSets", .array collector), ("node", .object receiver),
    ("nextNode", .object target), ("child", .object target), ("method", .string query), ("params", .object tempRef)] ++ state.environment}
  let kind ← text q "kind" "four"
  let call := if kind = "four" then NodePrivateCall.fourCall else NodePrivateCall.fiveCall
  let (returned, after) ← (runPrivateMethodCall (512 + requests.length * 16 + (requests.map (fun r => r.events.length)).foldl (· + ·) 0)
    defaultSplitLimit table ⟨.object receiver⟩ call caller).mapError reprStr
  if !(decide (after.environment = caller.environment) && decide (after.privates = caller.privates) &&
      decide (after.thisValue = caller.thisValue)) then throw "Caller/private/this frame changed"
  let collected ← match after.heap[collector]? with | some xs => pure xs | none => throw "Missing collector"
  let observedMatches ← collected.mapM fun value => do
    let ref ← asObject value
    let h ← data after ref "handler"
    let score ← data after ref "score"
    let keys ← asArray (← data after ref "possibleKeys")
    let keys ← match after.heap[keys]? with | some xs => xs.mapM (fun v => match v with | .string us => pure (us.map UInt16.toNat) | _ => throw "Bad key") | none => throw "Missing keys"
    let params ← objectAt after (← asObject (← data after ref "params"))
    pure <| Json.mkObj [("handler", ← match h with | .number n => pure (toJson n) | _ => throw "Bad handler"),
      ("score", ← match score with | .number n => pure (toJson n) | _ => throw "Bad score"), ("keys", toJson keys), ("captures", ← captures params)]
  let nulls ← collected.mapM fun value => do pure (← objectAt after (← asObject (← data after (← asObject value) "params"))).prototype.isNone
  let methodKept ← instances.mapM fun (classIndex, owner) => do
    let definition ← match definitions[classIndex]? with | some x => pure x | none => throw "Missing definition"
    pure (decide ((← readField after definition owner "pushHandlerSets") = (← readField initialized definition owner "pushHandlerSets")))
  let order ← lookup after "order"
  return Json.mkObj [("matches", toJson observedMatches), ("returned", ← encode returned),
    ("order", ← match order with | .number n => pure (toJson n) | _ => throw "Bad order"),
    ("nullPrototypes", toJson (nulls.all id)), ("methodValuesKept", toJson (methodKept.all id))]

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod) (helper : NoArgFunction) (json : Json) : Except String Json := do
  let counts ← (← items json "counts").mapM Json.getNat?
  let objectCount ← natural json "baseObjects" 1
  if objectCount = 0 then throw "Base needs a supplied prototype"
  let arrayCount ← natural json "baseArrays" 0
  let stamps ← (← items json "existingStamps").mapM Json.getNat?
  let base : State := {
    environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL")), ("outer", .number 41)],
    objects := objectPrototypeProjection [] :: List.replicate (objectCount - 1) emptyNullObject,
    heap := List.replicate arrayCount [], functions := [⟨helper, []⟩],
    privates := PrivateStore.ofData (stamps.zipIdx.map (fun (stamp, index) => ("old" ++ toString index, stamp)))
      (if stamps.isEmpty then [] else [(0, stamps.map (fun stamp => (stamp, .boolean true)))])}
  let completed ← (execute 64 defaultSplitLimit preamble
    {base with environment := withoutBindings base.environment (declaredNames preamble)}).mapError reprStr
  let module ← match completed with | .normal state => pure state | _ => throw "Unexpected preamble return"
  let emptyParams ← lookup module "emptyParams"
  let emptyReference ← asObject emptyParams
  let priorDefinitions ← natural json "priorDefinitions" 0
  let (world, prefixTable) ← (List.range priorDefinitions).foldlM (fun (world, table) _ => do
    match definePrivateClass fields [method] module world table with
    | some (_, next, changed) => pure (next, changed)
    | none => throw "Prior definition rejected") (initialPrivateClassWorld module (PrivateMethodTable.mk module.functions.length []), PrivateMethodTable.mk module.functions.length [])
  let (after, _, table, definitions, instances) ← counts.zipIdx.foldlM
    (fun (state, world, table, definitions, instances) (count, classIndex) => do
      let (definition, world, table) ← match definePrivateClass fields [method] state world table with
        | some result => pure result | none => throw "Private definition rejected"
      let (state, instances) ← (List.range count).foldlM (fun (current, owners) _ => do
        let (owner, next) ← (instantiatePrivateClass 96 defaultSplitLimit definition (some 0) current).mapError reprStr
        return (next, owners ++ [(classIndex, owner)])) (state, instances)
      return (state, world, table, definitions ++ [definition], instances)) (module, world, prefixTable, [], [])
  let snapshots ← instances.mapM fun (classIndex, owner) => do
    let definition ← match definitions[classIndex]? with | some value => pure value | none => throw "Missing definition"
    let methods ← readField after definition owner "methods"
    let children ← readField after definition owner "children"
    let patterns ← readField after definition owner "patterns"
    let pattern ← readField after definition owner "pattern"
    let params ← readField after definition owner "params"
    let function ← readField after definition owner "pushHandlerSets"
    let elements ← match after.privates.elements.lookup owner with | some xs => pure xs | none => throw "Missing instance elements"
    match elements.lookup (definition.firstIdentity + fields.length) with
    | some (.method value) => if value != function then throw "Method read projection changed"
    | _ => throw "Installed method lost its METHOD kind"
    return (owner, methods, children, patterns, pattern, params, function)
  let observations ← snapshots.mapM fun (owner, methods, children, patterns, pattern, params, function) => do
    let child ← objectAt after (← asObject children)
    let object ← objectAt after owner
    let patternTag := match pattern with
      | .undefined => "undefined" | .null => "null"
      | .object reference => if reference = emptyReference then "module" else "object"
      | .array _ => "object" | .number _ => "number" | .boolean _ => "boolean" | .string _ => "string"
      | _ => "function"
    return Json.mkObj [("methodsLength", toJson (← arrayLength after methods)),
      ("patternsLength", toJson (← arrayLength after patterns)), ("childrenOwnCount", toJson child.own.length),
      ("childrenNullPrototype", toJson child.prototype.isNone), ("pattern", toJson patternTag),
      ("paramsIsModule", toJson (decide (params = emptyParams))), ("methodsPatternsDistinct", toJson (decide (methods ≠ patterns))),
      ("publicOwnCount", toJson object.own.length), ("prototypeKept", toJson (decide (object.prototype = some 0))),
      ("methodIsFunction", toJson (match function with | .function _ => true | _ => false))]
  let arrays ← snapshots.flatMapM fun (_, methods, _, patterns, _, _, _) => do pure [← asArray methods, ← asArray patterns]
  let children ← snapshots.mapM fun (_, _, children, _, _, _, _) => asObject children
  let matrix := definitions.map fun definition => instances.map fun (_, owner) =>
    (privateGet (.object owner) "methods" {after with privates := {after.privates with names := definition.names}}).isOk
  let unbrandedState : State := {after with objects := after.objects ++ [{prototype := some 0}]}
  let unbrandedRejected := definitions.all fun definition =>
    !(privateGet (.object after.objects.length) "methods" {unbrandedState with privates := {unbrandedState.privates with names := definition.names}}).isOk
  let oldObjectsKept := (List.range base.objects.length).all (fun reference => decide (after.objects[reference]? = base.objects[reference]?))
  let oldArraysKept := (List.range base.heap.length).all (fun reference => decide (after.heap[reference]? = base.heap[reference]?))
  let oldSlotsKept := base.privates.slots.all (fun (owner, fields) => decide (after.privates.slots.lookup owner = some fields))
  if !(oldObjectsKept && oldArraysKept && oldSlotsKept && decide (after.environment = module.environment) &&
      decide (after.privates.names = base.privates.names) && decide (after.thisValue = module.thisValue)) then
    throw "Old storage or caller scope/this frame changed"
  let order ← lookup module "order"
  let methodValues : List Value := snapshots.map (fun (_, _, _, _, _, _, fn) => fn)
  let methodMatrix := methodValues.map (fun f => methodValues.map (fun g => decide (f = g)))
  let query ← runQuery after table definitions instances json
  return Json.mkObj [("instances", toJson observations), ("arraysIsolated", toJson (decide arrays.Nodup)),
    ("childrenIsolated", toJson (decide children.Nodup && !children.contains emptyReference)),
    ("sharedParams", toJson (snapshots.all (fun (_, _, _, _, _, value, _) => decide (value = emptyParams)))),
    ("moduleNullPrototype", toJson (← objectAt after emptyReference).prototype.isNone),
    ("helperCalls", toJson (after.objects.length - base.objects.length - instances.length)),
    ("order", match order with | .number value => toJson value | _ => Json.null),
    ("classBrandMatrix", toJson matrix),
    ("methodSharedMatrix", toJson methodMatrix),
    ("query", query), ("unbrandedRejected", toJson unbrandedRejected)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock (← text packet "preambleSource" NodeClass.pinnedPreambleSource) ["createNullObject"] with
      | some value => pure value | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields (← text packet "fieldsSource" NodeClass.pinnedFieldsSource) ["createNullObject", "emptyParams"] with
      | some value => pure value | none => throw "Field parse rejected"
    let method ← match parsePrivateMethod (← text packet "methodSource" NodeClass.pinnedMethodSource)
      NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames with
      | some value => pure value | none => throw "Method parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some value => pure value | none => throw "Helper parse rejected"
    return toJson (← (← items packet "cases").mapM (runCase preamble fields method helper))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
