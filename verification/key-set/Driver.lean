import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.NodeKeySet.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"

private def stringField (json : Json) (name fallback : String) : Except String String :=
  match json.getObjVal? name with | .ok value => value.getStr? | .error _ => pure fallback

private def namesField (json : Json) (name : String) : Except String (List JSString) :=
  match json.getObjVal? name with
  | .error _ => pure []
  | .ok value => do (← value.getArr?).toList.mapM units

private def runAdds (expression : Expr) : List JSString → State → Except String (State × Bool × Bool)
  | [], state => pure (state, true, true)
  | key :: rest, state => do
    -- The same explicit caller staging as the proved supplied trace: a fresh
    -- pattern array with primitive string at1. Surrounding insert is not run.
    let pattern := state.heap.length
    let prepared : State := {state with
      environment := ("pattern", .array pattern) :: withoutBindings state.environment ["pattern"]
      heap := state.heap ++ [[.undefined, .string key]]}
    let (value, after) ← (evalExpression 32 defaultSplitLimit expression prepared).mapError reprStr
    let frame := decide (after.heap[pattern]? = prepared.heap[pattern]?)
    let (last, alias, inputFrame) ← runAdds expression rest after
    return (last, decide (value = .set 1) && alias, frame && inputFrame)

private def spread (expression : Expr) (state : State) : Except String (Nat × State × Json) := do
  let (value, after) ← (evalExpression 32 defaultSplitLimit expression state).mapError reprStr
  let reference ← match value with | .array reference => pure reference | _ => throw "Expected array"
  let contents ← match after.heap[reference]? with | some value => pure value | none => throw "Missing array"
  let keys ← contents.mapM fun value => match value with
    | .string key => pure (key.map UInt16.toNat) | _ => throw "Non-string spread observation"
  return (reference, after, Json.mkObj [("ref", toJson reference), ("keys", toJson keys)])

private def runCase (createProgram : List Stmt) (addExpression spreadExpression : Expr) (json : Json) : Except String Json := do
  let names ← namesField json "names"
  let later ← namesField json "later"
  let before : State := {
    environment := [("Set", .setConstructor), ("Factory", .setConstructor), ("possibleKeys", .string (ascii "outer")),
      ("pattern", .array 0), ("frame", .object 0)]
    heap := [[.undefined, .undefined], [.string (ascii "frame-array")]]
    objects := [newDataObject emptyNullObject (ascii "marker") (.string (ascii "frame-object"))]
    sets := [[ascii "frame-set"]]
  }
  let createdCompletion ← (execute 32 defaultSplitLimit createProgram
    {before with environment := withoutBindings before.environment (declaredNames createProgram)}).mapError reprStr
  let created ← match createdCompletion with | .normal state => pure state | _ => throw "Unexpected create return"
  let reference ← match ← (lookupVariable created "possibleKeys").mapError reprStr with
    | .set reference => pure reference | _ => throw "Expected Set"
  let scopeCompletion ← (runBlock 32 createProgram before).mapError reprStr
  let scope ← match scopeCompletion with | .normal state => pure state | _ => throw "Unexpected scope return"
  let outerKept := decide (scope.environment = before.environment)
  let (added, aliasFirst, frameFirst) ← runAdds addExpression names created
  let (first, afterFirst, firstJson) ← spread spreadExpression added
  let (second, afterSecond, secondJson) ← spread spreadExpression afterFirst
  let firstContents := afterSecond.heap[first]?
  let (extended, aliasLater, frameLater) ← runAdds addExpression later afterSecond
  let (third, final, thirdJson) ← spread spreadExpression extended
  let setKeys ← match final.sets[reference]? with | some keys => pure keys | none => throw "Missing Set"
  let firstUnchanged := decide (final.heap[first]? = firstContents)
  let frame := decide (final.sets[(0 : Nat)]? = before.sets[(0 : Nat)]?) &&
    decide (final.heap[(0 : Nat)]? = before.heap[(0 : Nat)]?) &&
    decide (final.heap[(1 : Nat)]? = before.heap[(1 : Nat)]?) &&
    decide (final.objects = before.objects) && decide (final.functions.length = before.functions.length)
  return Json.mkObj [("setRef", toJson reference), ("freshSet", toJson (decide (reference ≥ before.sets.length))),
    ("outerKept", toJson outerKept), ("addReturnedAlias", toJson (aliasFirst && aliasLater)),
    ("inputFrameKept", toJson (frameFirst && frameLater)), ("snapshots", toJson [firstJson, secondJson, thirdJson]),
    ("firstUnchanged", toJson firstUnchanged), ("distinctArrays", toJson (first != second && second != third && first != third)),
    ("setKeys", toJson (setKeys.map (List.map UInt16.toNat))), ("frameKept", toJson frame)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let create ← stringField packet "createSource" NodeKeySet.pinnedCreateSource
    let add ← stringField packet "addSource" NodeKeySet.pinnedAddSource
    let spreadSource ← stringField packet "spreadSource" NodeKeySet.pinnedSpreadSource
    let createProgram ← match parseBlock create ["Set", "Factory"] with
      | some value => pure value | none => throw "Create parse rejected"
    let addExpression ← match parseExpression add ["possibleKeys", "pattern"] with
      | some value => pure value | none => throw "Add parse rejected"
    let spreadExpression ← match parseExpression spreadSource ["possibleKeys"] with
      | some value => pure value | none => throw "Spread parse rejected"
    let cases ← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase createProgram addExpression spreadExpression)
    return toJson cases
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
