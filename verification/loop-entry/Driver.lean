import HonoLean.Upstream.NodeSearchSetup.Program
import HonoLean.Upstream.NodeLoopEntry.Generated
import HonoLean.Upstream.SourceSubset.ForHeader
import HonoLean.Upstream.SourceSubset.FunctionCall
import HonoLean.Upstream.SourceSubset.PrivateClass
import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodeIterationSetup.Program
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
private def natural (json : Json) (key : String) : Except String Nat :=
  match json.getObjVal? key with | .ok v => v.getNat? | .error _ => pure 0
private def arrayRef : Value → Except String Nat
  | .array n => pure n | _ => throw "Expected array"
private def values (state : State) (reference : Nat) : Except String (List Value) :=
  match state.heap[reference]? with | some v => pure v | none => throw "Missing array"
private def normal : Completion → Except String State
  | .normal s => pure s | _ => throw "Unexpected return"
private def privateRead (state : State) (definition : SelectedPrivateClass) (owner : Nat) (name : String) : Except String Value :=
  (privateGet (.object owner) name {state with privates := {state.privates with names := definition.names}}).mapError reprStr
private def stringValues (contents : List Value) : Except String (List (List Nat)) :=
  contents.mapM fun value => match value with
    | .string s => pure (s.map UInt16.toNat) | _ => throw "Expected string contents"
private def names : List String := ["methods", "children", "patterns", "pattern", "params", "pushHandlerSets"]

private def runPrefix (methods : PrivateMethodTable) (functions : FunctionTable)
    (startup iteration : List Stmt) (node : List PrivateControlStmt) (outer inner : ForHeader)
    (before : State) : Except EvalError (State × Bool × Bool) := do
  let started ← executeFunctionStatements 128 defaultSplitLimit methods functions startup before
  let started ← match started with | .normal s => pure s | _ => throw .unsupported
  let entered ← enterForHeader 64 defaultSplitLimit outer started
  let (go, entered) ← testForHeader 64 defaultSplitLimit outer entered
  if !go then pure (entered, false, false) else do
    let iterated ← execute 64 defaultSplitLimit iteration entered
    let iterated ← match iterated with | .normal s => pure s | _ => throw .unsupported
    let entered ← enterForHeader 64 defaultSplitLimit inner iterated
    let (go, entered) ← testForHeader 64 defaultSplitLimit inner entered
    if !go then pure (entered, true, false) else do
      let completed ← executePrivateControl 64 defaultSplitLimit methods node entered
      let after ← match completed with | .normal s => pure s | _ => throw .unsupported
      pure (after, true, true)

private def encode : Value → Except String Json
  | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
  | .string s => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (s.map UInt16.toNat))]
  | .number n => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson n)]
  | _ => throw "Unsupported observation"
private def number (value : Value) : Json := match value with | .number n => toJson n | _ => Json.null

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (seed : Assignment) (push : Expr) (split : SourceSubset.Function)
    (startup iteration : List Stmt) (node : List PrivateControlStmt) (outer inner : ForHeader)
    (input : Json) : Except String Json := do
  let base : State := {
    environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL"))]
    objects := [objectPrototypeProjection [], newDataObject emptyNullObject (ascii "id") (.string (ascii "stale"))]
    functions := [⟨helper, []⟩] }
  let module ← normal (← (execute 64 defaultSplitLimit preamble base).mapError reprStr)
  let shared ← (lookupVariable module "emptyParams").mapError reprStr
  let (definition, _, methods) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some v => pure v | none => throw "Class definition rejected"
  let (root, one) ← (instantiatePrivateClass 96 defaultSplitLimit definition (some 0) module).mapError reprStr
  let (other, two) ← (instantiatePrivateClass 96 defaultSplitLimit definition (some 0) one).mapError reprStr
  let seedOwner := fun (state : State) (owner : Nat) => do
    let state : State := {state with
      environment := [("child", Value.object owner), ("params", Value.object 1)] ++ module.environment
      privates := {state.privates with names := definition.names}}
    let (_, after) ← executeAssignment 64 defaultSplitLimit seed state
    pure after
  let seeded ← (seedOwner two root).mapError reprStr
  let seeded ← (seedOwner seeded other).mapError reprStr
  let count ← natural input "registrations"
  let requests := (List.range count).map fun n => RegistrationHistory.Request.mk
    (ascii (if n % 2 = 0 then "GET" else "ALL")) (.number (Int.ofNat n)) [ascii "id", ascii "id", ascii "name"]
  let registered ← (RegistrationHistory.runSourceHistory push root requests seeded).mapError reprStr
  let methodValue ← privateRead registered definition root "pushHandlerSets"
  let path ← match input.getObjVal? "path" with | .ok v => units v | .error _ => pure []
  let handle := methods.base + methods.entries.length
  let functions : FunctionTable := ⟨handle, [⟨split, [], []⟩]⟩
  let caller : State := {registered with
    environment := [("splitPath", .function handle), ("path", .string path), ("method", .string (ascii "GET"))] ++ registered.environment
    thisValue := .object root
    privates := {registered.privates with names := definition.names}}
  let observe := fun (before after : State) (outerEntered innerEntered : Bool) => do
    let refs ← ["handlerSets", "curNodes", "parts", "curNodesQueue"].mapM fun name => do
      arrayRef (← (lookupVariable after name).mapError reprStr)
    let refs ← if outerEntered then do
        pure (refs ++ [← arrayRef (← (lookupVariable after "tempNodes").mapError reprStr)])
      else pure refs
    let parts ← stringValues (← values after refs[2]!)
    let len ← (lookupVariable after "len").mapError reprStr
    let offsets ← (lookupVariable after "partOffsets").mapError reprStr
    let outerObservation ← if outerEntered then do
        let index ← (lookupVariable after "i").mapError reprStr
        let part ← (lookupVariable after "part").mapError reprStr
        let last ← (lookupVariable after "isLast").mapError reprStr
        pure <| Json.mkObj [("index", number index), ("part", ← encode part),
          ("isLast", match last with | .boolean b => toJson b | _ => Json.null),
          ("queueEmpty", toJson (decide ((← values after refs[4]!) = [])))]
      else pure Json.null
    let innerObservation ← if innerEntered then do
        let index ← (lookupVariable after "j").mapError reprStr
        let bound ← (lookupVariable after "len2").mapError reprStr
        let node ← (lookupVariable after "node").mapError reprStr
        pure <| Json.mkObj [("index", number index), ("bound", number bound),
          ("nodeIsRoot", toJson (decide (node = .object root))), ("nodeUndefined", toJson (decide (node = .undefined)))]
      else pure Json.null
    let rootParams ← privateRead after definition root "params"
    let otherParams ← privateRead after definition other "params"
    let methodValues ← [root,other].mapM fun owner => privateRead after definition owner "pushHandlerSets"
    let snapshot := Json.mkObj [("parts", toJson parts), ("len", number len), ("offsetsNull", toJson (decide (offsets = .null))),
      ("collectorEmpty", toJson (decide ((← values after refs[0]!) = []))),
      ("pendingEmpty", toJson (decide ((← values after refs[3]!) = []))),
      ("singletonNodes", toJson (decide ((← values after refs[1]!) = [.object root]))),
      ("resetShared", toJson (decide (rootParams = shared))), ("otherKept", toJson (decide (otherParams = .object 1))),
      ("methodKept", toJson (methodValues.all (· == methodValue))), ("outer", outerObservation), ("inner", innerObservation)]
    let fresh := decide (refs.Pairwise (· ≠ ·)) && refs.all (fun ref => decide (before.heap.length ≤ ref))
    if !(decide (after.thisValue = caller.thisValue) && decide (after.objects = caller.objects) &&
        decide (after.sets = caller.sets) && decide (reprStr after.functions = reprStr caller.functions) &&
        decide (after.privates.names = caller.privates.names)) then throw "Prefix caller frame changed"
    pure (snapshot, fresh, decide (after.heap.take before.heap.length = before.heap))
  let (after, outerEntered, innerEntered) ← (runPrefix methods functions startup iteration node outer inner caller).mapError reprStr
  let (snapshot, fresh, frame) ← observe caller after outerEntered innerEntered
  let (snapshots, fresh, frame) ← if ← boolean input "repeat" then do
      let seeded ← (seedOwner after root).mapError reprStr
      let active : State := {seeded with environment := caller.environment, thisValue := .object root}
      let (finalState, outerEntered, innerEntered) ← (runPrefix methods functions startup iteration node outer inner active).mapError reprStr
      let (secondSnapshot, secondFresh, secondFrame) ← observe active finalState outerEntered innerEntered
      pure ([snapshot,secondSnapshot],fresh && secondFresh,frame && secondFrame)
    else pure ([snapshot],fresh,frame)
  let order ← (lookupVariable after "order").mapError reprStr
  pure <| Json.mkObj [("snapshots",toJson snapshots),("fresh",toJson fresh),("oldArraysKept",toJson frame),("order",number order)]

private def probeSteps : Nat → Nat → String → ForHeader → State → List Json → Except String (State × List Json × Bool)
  | 0, _, _, _, _, _ => throw "Probe budget exhausted"
  | fuel+1, cap, action, header, before, trace => do
    let (go, before) ← (testForHeader 64 defaultSplitLimit header before).mapError reprStr
    if !go then pure (before,trace,false) else do
      let index ← (lookupVariable before "j").mapError reprStr
      let bound ← (lookupVariable before "len2").mapError reprStr
      let (value, before) ← (evalExpression 64 defaultSplitLimit (.index (.variable "curNodes") (.variable "j")) before).mapError reprStr
      let trace := trace ++ [Json.mkObj [("index",number index),("bound",number bound),("value",← encode value)]]
      let before ← if action = "grow" then do
          pure (← (evalExpression 64 defaultSplitLimit (.call (.variable "curNodes") "push" [.number 99]) before).mapError reprStr).2
        else if action = "shrink" then do
          pure (← (evalExpression 64 defaultSplitLimit (.call (.variable "curNodes") "shift" []) before).mapError reprStr).2
        else pure before
      if cap ≤ trace.length then pure (before,trace,true) else do
        let after ← (advanceForHeader header before).mapError reprStr
        probeSteps fuel cap action header after trace
private def runProbe (header : ForHeader) (input : Json) : Except String Json := do
  let count ← natural input "length"
  let cap ← match input.getObjVal? "cap" with | .ok v => v.getNat? | .error _ => pure 16
  let action ← text input "action" "keep"
  let before : State := {
    environment := [("curNodes",.array 0),("j",.number 99),("len2",.number 88)]
    heap := [(List.range count).map (fun n => .number (Int.ofNat n))]}
  let entered ← (enterForHeader 64 defaultSplitLimit header before).mapError reprStr
  let (after, trace, capped) ← probeSteps (cap+4) cap action header entered []
  let nodes ← (← values after 0).mapM fun value => pure (number value)
  pure <| Json.mkObj [("trace",toJson trace),("capped",toJson capped),("nodes",toJson nodes)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock NodeClass.pinnedPreambleSource ["createNullObject"] with
      | some v => pure v | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"] with
      | some v => pure v | none => throw "Fields parse rejected"
    let method ← match parsePrivateMethod NodeClass.pinnedMethodSource ["METHOD_NAME_ALL", "createNullObject", "Object"] names with
      | some v => pure v | none => throw "Method parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with
      | some v => pure v | none => throw "Helper parse rejected"
    let seed ← match parseAssignment NodePrivateWrite.pinnedParameterSource ["child", "params"] names with
      | some v => pure v | none => throw "Seed parse rejected"
    let push ← match parseExpression NodeMethodsPush.pinnedSource ["curNode", "method", "handler", "possibleKeys", "order"] names with
      | some v => pure v | none => throw "Push parse rejected"
    let split ← match parse SourceSubset.pinnedSource with | some v => pure v | none => throw "Split parse rejected"
    let startup ← match parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings names true with
      | some v => pure v | none => throw "Startup parse rejected"
    let iteration ← match parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings with
      | some v => pure v | none => throw "Iteration parse rejected"
    let node ← match parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings names with
      | some v => pure (v.take 1) | none => throw "Node declaration parse rejected"
    let outerSource ← text packet "outerSource" NodeLoopEntry.pinnedOuterSource
    let innerSource ← text packet "innerSource" NodeLoopEntry.pinnedInnerSource
    let outer ← match parseForHeader outerSource ["len"] with | some v => pure v | none => throw "Outer header parse rejected"
    let inner ← match parseForHeader innerSource ["curNodes"] with | some v => pure v | none => throw "Inner header parse rejected"
    let results ← (← items packet "cases").mapM (runCase preamble fields method helper seed push split startup iteration node outer inner)
    let probes ← (← items packet "probes").mapM (runProbe inner)
    pure <| Json.mkObj [("results",toJson results),("probes",toJson probes)]
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
