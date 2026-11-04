import HonoLean.Upstream.NodeSearchSetup.Program
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

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (seed : Assignment) (push : Expr) (split : SourceSubset.Function)
    (startup iteration : List Stmt) (input : Json) : Except String Json := do
  let base : State := {
    environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL"))]
    objects := [objectPrototypeProjection [], newDataObject emptyNullObject (ascii "id") (.string (ascii "stale")), emptyNullObject]
    functions := [⟨helper, []⟩] }
  let module ← normal (← (execute 64 defaultSplitLimit preamble base).mapError reprStr)
  let shared ← (lookupVariable module "emptyParams").mapError reprStr
  let (first, world, methodTable) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
    | some v => pure v | none => throw "First definition rejected"
  let (second, _, methodTable) ← match definePrivateClass fields [method] module world methodTable with
    | some v => pure v | none => throw "Second definition rejected"
  let (root, one) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) module).mapError reprStr
  let (other, two) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) one).mapError reprStr
  let (foreign, three) ← (instantiatePrivateClass 96 defaultSplitLimit second (some 0) two).mapError reprStr
  let seedOwner := fun (state : State) (owner : Nat) => do
    let state : State := {state with
      environment := [("child", Value.object owner), ("params", Value.object 1)] ++ module.environment
      privates := {state.privates with names := first.names}}
    let (_, after) ← executeAssignment 64 defaultSplitLimit seed state
    pure after
  let seeded ← (seedOwner three root).mapError reprStr
  let seeded ← (seedOwner seeded other).mapError reprStr
  let count ← natural input "registrations"
  let requests := (List.range count).map fun n => RegistrationHistory.Request.mk
    (ascii (if n % 2 = 0 then "GET" else "ALL")) (.number (Int.ofNat n)) [ascii "id", ascii "id", ascii "name"]
  let registered ← (RegistrationHistory.runSourceHistory push root requests seeded).mapError reprStr
  let methodValue ← privateRead registered first root "pushHandlerSets"
  let receiver := match ← text input "receiver" "root" with
    | "root" => Value.object root | "other" => .object other | "foreign" => .object foreign
    | "plain" => .object 2 | "n" => .null | _ => .undefined
  let path ← match input.getObjVal? "path" with | .ok v => units v | .error _ => pure []
  let handle := methodTable.base + methodTable.entries.length
  let functionTable : FunctionTable := ⟨handle, [⟨split, [], []⟩]⟩
  let caller : State := {registered with
    environment := [("splitPath", .function handle), ("path", .string path), ("method", .string (ascii "GET"))] ++ registered.environment
    thisValue := receiver
    privates := {registered.privates with names := first.names}}
  let i ← natural input "i"
  let observe := fun (before after : State) => do
    let refs ← ["handlerSets", "curNodes", "parts", "curNodesQueue"].mapM fun name => do
      arrayRef (← (lookupVariable after name).mapError reprStr)
    let collector := refs[0]!
    let nodes := refs[1]!
    let partsRef := refs[2]!
    let pending := refs[3]!
    let parts ← stringValues (← values after partsRef)
    let len ← (lookupVariable after "len").mapError reprStr
    let offset ← (lookupVariable after "partOffsets").mapError reprStr
    let alias ← (lookupVariable after "curNode").mapError reprStr
    let rootParams ← privateRead after first root "params"
    let otherParams ← privateRead after first other "params"
    let methodValues ← [root, other].mapM fun owner => privateRead after first owner "pushHandlerSets"
    let (outer, observedState) ← if i < parts.length then do
        let active : State := {after with environment := ("i", .number i) :: after.environment}
        let observed ← normal (← (execute 64 defaultSplitLimit iteration active).mapError reprStr)
        let part ← (lookupVariable observed "part").mapError reprStr
        let part ← match part with | .string s => pure (s.map UInt16.toNat) | _ => throw "Expected indexed string"
        let last ← (lookupVariable observed "isLast").mapError reprStr
        let temp ← arrayRef (← (lookupVariable observed "tempNodes").mapError reprStr)
        let observation := Json.mkObj [("part", toJson part), ("isLast", match last with | .boolean b => toJson b | _ => Json.null),
          ("queueFresh", toJson (decide (temp = after.heap.length) && decide (observed.heap[temp]? = some []))),
          ("nodeIsReceiver", toJson (decide ((← values after nodes)[0]? = some receiver)))]
        pure (observation, observed)
      else pure (Json.null, after)
    let snapshot := Json.mkObj [("parts", toJson parts), ("len", match len with | .number n => toJson n | _ => Json.null),
      ("offsetsNull", toJson (decide (offset = .null))), ("collectorEmpty", toJson (decide ((← values after collector) = []))),
      ("pendingEmpty", toJson (decide ((← values after pending) = []))), ("rootAlias", toJson (decide (alias = receiver))),
      ("singletonNodes", toJson (decide ((← values after nodes) = [receiver]))),
      ("resetShared", toJson (decide (rootParams = shared))), ("otherKept", toJson (decide (otherParams = .object 1))),
      ("methodKept", toJson (methodValues.all (· == methodValue))), ("outer", outer)]
    let fresh := decide (refs.Pairwise (· ≠ ·)) && refs.all (fun ref => decide (before.heap.length ≤ ref))
    if !(decide (after.thisValue = caller.thisValue) && decide (after.objects = caller.objects) &&
        decide (after.sets = caller.sets) && decide (reprStr after.functions = reprStr caller.functions) &&
        decide (after.privates.names = caller.privates.names)) then throw "Startup caller frame changed"
    pure (snapshot, fresh, decide (after.heap.take before.heap.length = before.heap), observedState)
  let repeated ← boolean input "repeat"
  let executeStartup := fun (state : State) => executeFunctionStatements 128 defaultSplitLimit methodTable functionTable startup state
  match executeStartup caller with
  | .error _ => pure <| Json.mkObj [("ok", toJson false)]
  | .ok completion =>
    let after ← normal completion
    let (snapshot, fresh, frame, retained) ← observe caller after
    let (snapshots, fresh, frame) ← if repeated then do
        let seeded ← (seedOwner retained root).mapError reprStr
        let active : State := {seeded with environment := caller.environment, thisValue := receiver}
        match executeStartup active with
        | .error _ => throw "Repeated startup failed"
        | .ok completion =>
          let finalState ← normal completion
          let (secondSnapshot, secondFresh, secondFrame, _) ← observe active finalState
          pure ([snapshot, secondSnapshot], fresh && secondFresh, frame && secondFrame)
      else pure ([snapshot], fresh, frame)
    let order ← (lookupVariable after "order").mapError reprStr
    pure <| Json.mkObj [("ok", toJson true), ("snapshots", toJson snapshots), ("fresh", toJson fresh),
      ("oldArraysKept", toJson frame), ("order", match order with | .number n => toJson n | _ => Json.null)]

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
    let splitSource ← text packet "splitSource" SourceSubset.pinnedSource
    let split ← match parse splitSource with | some v => pure v | none => throw "splitPath parse rejected"
    let startupSource ← text packet "startupSource" NodeSearchSetup.pinnedSource
    let startup ← match parseFunctionStatements startupSource NodeSearchSetup.bindings names true with
      | some v => pure v | none => throw "Startup parse rejected"
    let iteration ← match parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings with
      | some v => pure v | none => throw "Iteration parse rejected"
    toJson <$> (← items packet "cases").mapM (runCase preamble fields method helper seed push split startup iteration)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
