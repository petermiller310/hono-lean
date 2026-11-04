import HonoLean.Upstream.GetPatternInvocation.Source
import HonoLean.Upstream.LexicalArrow.Runtime
import Lean.Data.Json
open Lean HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025
set_option autoImplicit false

/-- Deliberately lacks the normal String/RegExp realm. Source setup needs only
the two projected prototype objects; the actual wildcard never reads globals. -/
private def seed (tdz : Bool) : LexicalArrow.Runtime :=
  {data := {base := {regexp := {ambient := {objects := [⟨[],none,true⟩,⟨[],some 0,true⟩]}}}}
   cells := if tdz then [⟨.mutable,none⟩] else []
   environments := [⟨if tdz then [("RegExp",0)] else [],none⟩]}

private def packet : Except String Json := do
  let some setup := GetPatternInvocation.parseSetup GetPatternInvocation.pinnedSetup | throw "Actual setup parser refused"
  let results ← [false,true].mapM fun tdz => do
    let (_,created) ← (LexicalArrow.initializeModule setup.initializer setup.arrow 1 (seed tdz)).mapError reprStr
    let caller := {created with current := 0, thisValue := .number 17}
    let outcome := LexicalArrow.invokeBinding 32 defaultSplitLimit ⟨labelStandardContext⟩ created.current "getPattern"
      [.string [42],.object 999,.object 998] caller
    match outcome with
    | .outsideModel error => throw (reprStr error)
    | .returned value after =>
      pure <| Json.mkObj [("value",toJson (reprStr value)),
        ("sameEntireData",toJson (reprStr after.data == reprStr caller.data)),
        ("callerRestored",toJson (decide (after.current=caller.current ∧ after.thisValue=caller.thisValue))),
        ("oldCellsPreserved",toJson (decide (after.cells.take caller.cells.length=caller.cells))),
        ("cellsAdded",toJson (after.cells.length-caller.cells.length)),
        ("environmentsAdded",toJson (after.environments.length-caller.environments.length)),
        ("objects",toJson after.data.base.regexp.ambient.objects.length),
        ("arrays",toJson after.data.base.regexp.ambient.heap.length)]
  pure (toJson results)

def main : IO UInt32 := do
  match packet with
  | .ok result => (← IO.getStdout).putStrLn result.compress; pure 0
  | .error error => (← IO.getStderr).putStrLn error; pure 1
