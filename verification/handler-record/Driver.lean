import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.HandlerRecord.Generated
import HonoLean.Upstream.ECMA2025.StringSet
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 65536 then pure (UInt16.ofNat value) else throw "Invalid code unit"

private def names (json : Json) (field : String) : Except String (List JSString) := do
  (← (← json.getObjVal? field).getArr?).toList.mapM units

private def data (object : Option OrdinaryObject) (key : JSString) : Option Value := do
  let descriptor ← (← object).own.lookup key
  match descriptor with | .data value true true true => some value | _ => none

private def handlerValue (kind : String) : Value :=
  match kind with
  | "array" => .array 1 | "set" => .set 1 | "function" => .function 0
  | "undefined" => .undefined | "null" => .null | "boolean" => .boolean false
  | "number" => .number 17 | "string" => .string (ascii "handler")
  | _ => .object 2

private def observe (before after : State) (returned handler : Value) (method : JSString) : Json := Id.run do
  let outerRef := match returned with | .object reference => some reference | _ => none
  let outer := outerRef.bind (fun reference => after.objects[reference]?)
  let innerRef := match data outer method with | some (.object reference) => some reference | _ => none
  let inner := innerRef.bind (fun reference => after.objects[reference]?)
  let keysRef := match data inner (ascii "possibleKeys") with | some (.array reference) => some reference | _ => none
  let keys := keysRef.bind (fun reference => after.heap[reference]?)
  let keyJson := match keys with
    | none => Json.null
    | some values => toJson (values.map fun value => match value with
        | .string contents => toJson (contents.map UInt16.toNat) | _ => Json.null)
  let score := match data inner (ascii "score") with | some (.number value) => toJson value | _ => Json.null
  return Json.mkObj [
    ("outerOwnCount", toJson (outer.map (fun value => value.own.length) |>.getD 0)),
    ("outerHasMethod", toJson (data outer method |>.isSome)),
    ("outerPrototypeStandard", toJson (outer.map (fun value => value.prototype == some 0) |>.getD false)),
    ("outerExtensible", toJson (outer.map OrdinaryObject.extensible |>.getD false)),
    ("innerOwnCount", toJson (inner.map (fun value => value.own.length) |>.getD 0)),
    ("innerPrototypeStandard", toJson (inner.map (fun value => value.prototype == some 0) |>.getD false)),
    ("innerExtensible", toJson (inner.map OrdinaryObject.extensible |>.getD false)),
    ("handlerKept", toJson (data inner (ascii "handler") == some handler)),
    ("paramsAbsent", toJson (inner.map (fun value => (value.own.lookup (ascii "params")).isNone) |>.getD false)),
    ("freshObjects", toJson (match outerRef, innerRef with
      | some outer, some inner => outer ≥ before.objects.length && inner ≥ before.objects.length && outer != inner
      | _, _ => false)),
    ("freshKeys", toJson (keysRef.map (fun reference => decide (reference ≥ before.heap.length)) |>.getD false)),
    ("keys", keyJson), ("score", score)]

private def runCase (expression : Expr) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let events ← names json "names"
  let later ← names json "later"
  let order ← (← json.getObjVal? "order").getInt?
  let handler := handlerValue (← (← json.getObjVal? "handler").getStr?)
  let before : State := {
    environment := [("method", .string method), ("handler", handler), ("possibleKeys", .set 1),
      ("order", .number order), ("frame", .string (ascii "binding"))]
    heap := [[.string (ascii "frame-array")], [.string (ascii "handler-array")]]
    objects := [objectPrototypeProjection [], newDataObject emptyNullObject (ascii "frame") (.number 23), emptyNullObject]
    functions := [⟨⟨"frame", .null⟩, []⟩]
    sets := [[ascii "frame-set"], StringSet.fromTrace events]}
  let (first, afterFirst) ← (evalExpression 64 defaultSplitLimit expression before).mapError reprStr
  let firstJson := observe before afterFirst first handler method
  -- Explicit caller-threaded state and later add events; neither executes the
  -- private push nor proves persistent module lexical cells across Node calls.
  let current ← match afterFirst.sets[1]? with | some entries => pure entries | none => throw "Missing Set"
  let extended : State := {afterFirst with sets := afterFirst.sets.set 1 (later.foldl StringSet.add current)}
  let (second, final) ← (evalExpression 64 defaultSplitLimit expression extended).mapError reprStr
  let finalOrder := match final.environment.lookup "order" with | some (.number value) => toJson value | _ => Json.null
  let oldObjects := decide (final.objects.take before.objects.length = before.objects)
  let oldArrays := decide (final.heap.take before.heap.length = before.heap)
  let bindings := decide (final.environment.filter (fun entry => entry.1 != "order") =
    before.environment.filter (fun entry => entry.1 != "order"))
  return Json.mkObj [("first", firstJson), ("second", observe extended final second handler method),
    ("firstUnchanged", toJson (observe before final first handler method == firstJson)),
    ("orderAfter", finalOrder), ("distinctOuter", toJson (first != second)),
    ("otherBindingsKept", toJson bindings),
    ("setKept", toJson (decide (afterFirst.sets = before.sets) && decide (final.sets = extended.sets))),
    ("frameKept", toJson (oldObjects && oldArrays &&
      decide (final.sets[0]? = before.sets[0]?) && (reprStr final.functions == reprStr before.functions)))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let source ← match packet.getObjVal? "source" with | .ok value => value.getStr? | .error _ => pure HandlerRecord.pinnedSource
    let expression ← match parseExpression source ["method", "handler", "possibleKeys", "order"] with
      | some value => pure value | none => throw "Source parse rejected"
    return toJson (← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase expression))
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
