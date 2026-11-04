import HonoLean.Upstream.SourceSubset.PrivateControl
import HonoLean.Upstream.SourceSubset.ForHeader
import HonoLean.Upstream.SourceSubset.FunctionCall
import HonoLean.Upstream.NodeSearchSetup.Program
import HonoLean.Upstream.NodeLoopEntry.Program
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

private structure Programs where
  startup : List Stmt
  outer : ForHeader
  iteration : List Stmt
  inner : ForHeader
  entry : List PrivateControlStmt

private def runFirst (programs : Programs) (methods : PrivateMethodTable) (functions : FunctionTable)
    (before : State) : Except EvalError (State × Bool) := do
  let started ← executeFunctionStatements 128 defaultSplitLimit methods functions programs.startup before
  let started ← match started with | .normal s => pure s | _ => throw .unsupported
  let entered ← enterForHeader 64 defaultSplitLimit programs.outer started
  let (go, entered) ← testForHeader 64 defaultSplitLimit programs.outer entered
  if !go then pure (entered,false) else do
    let iterated ← execute 64 defaultSplitLimit programs.iteration entered
    let iterated ← match iterated with | .normal s => pure s | _ => throw .unsupported
    let entered ← enterForHeader 64 defaultSplitLimit programs.inner iterated
    let (go, entered) ← testForHeader 64 defaultSplitLimit programs.inner entered
    if !go then throw .unsupported else do
      -- Finite test budget only; the symbolic theorem derives its own budget.
      let completed ← executePrivateControl 8192 defaultSplitLimit methods programs.entry entered
      let after ← match completed with | .normal s => pure s | _ => throw .unsupported
      pure (after,true)

private def natural (json : Json) (key : String) (fallback : Nat) : Except String Nat :=
  match json.getObjVal? key with | .ok v => v.getNat? | .error _ => pure fallback

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (seed : Assignment) (push : Expr) (split : SourceSubset.Function)
    (programs : Programs) (input : Json) : Except String Json := do
  let base : State := {
    environment := [("createNullObject",.function 0),("METHOD_NAME_ALL",.string (ascii "ALL"))]
    objects := [objectPrototypeProjection [],← inputFields input "entries",← inputFields input "laterEntries",emptyNullObject]
    functions := [⟨helper,[]⟩] }
  let module ← normal (← (execute 64 defaultSplitLimit preamble base).mapError reprStr)
  let shared ← (lookupVariable module "emptyParams").mapError reprStr
  let (first,world,methods) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1,[]⟩) ⟨1,[]⟩ with
    | some v => pure v | none => throw "First class rejected"
  let (second,_,methods) ← match definePrivateClass fields [method] module world methods with
    | some v => pure v | none => throw "Second class rejected"
  let (root,one) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) module).mapError reprStr
  let (parent,two) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) one).mapError reprStr
  let (literal,three) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) two).mapError reprStr
  let (wildcard,four) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) three).mapError reprStr
  let (foreign,five) ← (instantiatePrivateClass 96 defaultSplitLimit second (some 0) four).mapError reprStr
  let owners := [("root",root),("parent",parent),("literal",literal),("wildcard",wildcard),("foreign",foreign)]
  let branded := [root,parent,literal,wildcard]
  let decode := fun (code : String) => match owners.lookup code with
    | some n => Value.object n | none => if code = "plain" then .object 3 else primitive code
  let path ← string input "path" [47,108,105,116]
  let query ← string input "query" [71,69,84]
  let child := decode (← text input "child" "literal")
  let star := decode (← text input "wildcard" "u")
  -- Independent fixture key scan, not the faulted startup's output.
  let field := if path.head? = some 47 then (path.drop 1).takeWhile (· != 47) else path.takeWhile (· != 47)
  let active : State := {five with privates := {five.privates with names := first.names}}
  let linked ← if path.isEmpty then pure active else link active root field child
  let linked ← match child with
    | .object n => if branded.contains n then link linked n [42] star else pure linked
    | _ => pure linked
  let seedOwner := fun (state : State) (owner : Nat) (value : Value) => do
    let state : State := {state with environment := [("child",Value.object owner),("params",value)] ++ module.environment}
    let (_,after) ← executeAssignment 64 defaultSplitLimit seed state
    pure after
  let seeded ← (branded.foldlM (fun state owner => seedOwner state owner (.object 1)) linked).mapError reprStr
  let rootRegs ← registrations input "root"
  let literalRegs ← registrations input "literal"
  let starRegs ← registrations input "star"
  let registered ← (RegistrationHistory.runSourceHistory push root rootRegs seeded).mapError reprStr
  let registered ← (RegistrationHistory.runSourceHistory push literal literalRegs registered).mapError reprStr
  let registered ← (RegistrationHistory.runSourceHistory push wildcard starRegs registered).mapError reprStr
  let methodValue ← privateRead registered first root "pushHandlerSets"
  let handle := methods.base + methods.entries.length
  let functions : FunctionTable := ⟨handle,[⟨split,[],[]⟩]⟩
  let receiver := decode (← text input "receiver" "root")
  let caller : State := {registered with
    environment := [("splitPath",.function handle),("path",.string path),("method",.string query)] ++ registered.environment
    thisValue := receiver}
  let arrayValue := fun value => match value with | Value.array n => Except.ok n | _ => Except.error EvalError.unsupported
  let remember := fun (state : State) (entered : Bool) (oldLength : Nat) => do
    let collector ← arrayValue (← lookupVariable state "handlerSets")
    let refs ← ["handlerSets","curNodes","parts","curNodesQueue"].mapM fun name => do
      arrayValue (← lookupVariable state name)
    let refs ← if entered then do pure (refs ++ [← arrayValue (← lookupVariable state "tempNodes")]) else pure refs
    pure (collector,decide (refs.Pairwise (· ≠ ·)) && refs.all (fun n => decide (oldLength ≤ n)))
  let repeated ← boolean input "repeat"
  let executed : Except EvalError (State × Bool × List Nat × Bool × Bool) := do
    let (after,entered) ← runFirst programs methods functions caller
    let (collector,firstFresh) ← remember after entered caller.heap.length
    if repeated then
      let seeded ← seedOwner after root (.object 2)
      let next : State := {seeded with environment := caller.environment,thisValue := receiver}
      let (last,lastEntered) ← runFirst programs methods functions next
      let (nextCollector,secondFresh) ← remember last lastEntered next.heap.length
      pure (last,lastEntered,[collector,nextCollector],firstFresh && secondFresh,
        decide (after.heap.take caller.heap.length = caller.heap) && decide (last.heap.take next.heap.length = next.heap))
    else pure (after,entered,[collector],firstFresh,true)
  match executed with
  | .error _ => pure <| Json.mkObj [("ok",toJson false)]
  | .ok (after,entered,collectors,allFresh,intermediateFrame) =>
    let fresh := allFresh && decide (collectors.Pairwise (· ≠ ·))
    let partsRef ← arrayRef (← (lookupVariable after "parts").mapError reprStr)
    let parts ← (← values after partsRef).mapM fun value => match value with
      | .string units => pure (units.map UInt16.toNat) | _ => throw "Expected string part"
    let readOrUndefined := fun (name : String) => if entered then (lookupVariable after name).mapError reprStr else pure Value.undefined
    let next ← readOrUndefined "nextNode"
    let node ← readOrUndefined "node"
    let part ← readOrUndefined "part"
    let isLast ← readOrUndefined "isLast"
    let i ← readOrUndefined "i"
    let j ← readOrUndefined "j"
    let len2 ← readOrUndefined "len2"
    let len ← (lookupVariable after "len").mapError reprStr
    let offsets ← (lookupVariable after "partOffsets").mapError reprStr
    let label := fun (value : Value) => match owners.find? (fun (_,n) => decide (value = .object n)) with
      | some (name,_) => pure <| Json.mkObj [("kind",toJson name)] | none => encode value
    let temp ← if entered then do values after (← arrayRef (← (lookupVariable after "tempNodes").mapError reprStr)) else pure []
    let groups ← collectors.mapM (values after)
    let rows ← groups.flatten.mapM objectRef
    let parameterRefs ← rows.mapM fun record => do objectRef (← own after record (ascii "params"))
    let observedMatches ← rows.mapM fun record => do
      let handler ← own after record (ascii "handler")
      let score ← own after record (ascii "score")
      let keys ← (← values after (← arrayRef (← own after record (ascii "possibleKeys")))).mapM fun value => match value with
        | .string units => pure (units.map UInt16.toNat) | _ => throw "Expected key"
      let params ← objectRef (← own after record (ascii "params"))
      let number := fun value => match value with | Value.number n => toJson n | _ => Json.null
      pure <| Json.mkObj [("handler",number handler),("score",number score),("keys",toJson keys),("captures",← captures after params)]
    let params ← owners.mapM fun (name,owner) => do
      let value ← privateRead after (if name = "foreign" then second else first) owner "params"
      pure <| toJson [name,if value = shared then "shared" else if value = .object 1 then "A" else if value = .object 2 then "B" else "unknown"]
    let methodsKept ← branded.mapM fun owner => privateRead after first owner "pushHandlerSets"
    if !(decide (after.thisValue = receiver) && decide (after.sets = caller.sets) &&
        decide (reprStr after.functions = reprStr caller.functions) && decide (after.privates.names = first.names)) then throw "Caller frame changed"
    let order ← (lookupVariable after "order").mapError reprStr
    let number := fun value => match value with | Value.number n => toJson n | _ => Json.null
    pure <| Json.mkObj [("ok",toJson true),("entered",toJson entered),("next",← label next),("node",← label node),("temp",toJson (← temp.mapM label)),
      ("setup",Json.mkObj [("parts",toJson parts),("len",number len),("part",← encode part),
        ("isLast",match isLast with | .boolean b => toJson b | _ => Json.null),("i",number i),("j",number j),("len2",number len2),
        ("offsetsNull",toJson (decide (offsets = .null))),("fresh",toJson fresh),
        ("oldArraysKept",toJson (intermediateFrame && decide (after.heap.take caller.heap.length = caller.heap)))]),
      ("matches",toJson observedMatches),("collectorSizes",toJson (groups.map List.length)),
      ("sameRecords",toJson (rows.map fun a => rows.map fun b => a == b)),
      ("sameParams",toJson (parameterRefs.map fun a => parameterRefs.map fun b => a == b)),
      ("params",toJson params),("order",number order),("methodKept",toJson (methodsKept.all (· == methodValue))),
      ("nullPrototypes",toJson (parameterRefs.all fun n => (after.objects[n]?).any fun o => o.prototype.isNone))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock NodeClass.pinnedPreambleSource ["createNullObject"] with
      | some v => pure v | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject","emptyParams"] with
      | some v => pure v | none => throw "Fields parse rejected"
    let method ← match parsePrivateMethod NodeClass.pinnedMethodSource ["METHOD_NAME_ALL","createNullObject","Object"] names with
      | some v => pure v | none => throw "Method parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some v => pure v | none => throw "Helper parse rejected"
    let seed ← match parseAssignment NodePrivateWrite.pinnedParameterSource ["child","params"] names with
      | some v => pure v | none => throw "Seed parse rejected"
    let push ← match parseExpression NodeMethodsPush.pinnedSource ["curNode","method","handler","possibleKeys","order"] names with
      | some v => pure v | none => throw "Push parse rejected"
    let split ← match parse SourceSubset.pinnedSource with | some v => pure v | none => throw "Split parse rejected"
    let startupSource ← text packet "startupSource" NodeSearchSetup.pinnedSource
    let startup ← match parseFunctionStatements startupSource NodeSearchSetup.bindings names true with
      | some v => pure v | none => throw "Startup parse rejected"
    let outer ← match parseForHeader NodeLoopEntry.pinnedOuterSource NodeLoopEntry.outerBindings with
      | some v => pure v | none => throw "Outer parse rejected"
    let iteration ← match parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings with
      | some v => pure v | none => throw "Iteration parse rejected"
    let inner ← match parseForHeader NodeLoopEntry.pinnedInnerSource NodeLoopEntry.innerBindings with
      | some v => pure v | none => throw "Inner parse rejected"
    let entrySource ← text packet "entrySource" NodeIterationSetup.pinnedEntrySource
    let entry ← match parsePrivateControl entrySource NodeIterationSetup.nodeBranchBindings names with
      | some v => pure v | none => throw "Entry parse rejected"
    let programs : Programs := ⟨startup,outer,iteration,inner,entry⟩
    toJson <$> (← items packet "cases").mapM (runCase preamble fields method helper seed push split programs)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
