import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.NodeMethodsPush.Generated
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
  | "array" => .array 3 | "set" => .set 1 | "function" => .function 0
  | "undefined" => .undefined | "null" => .null | "boolean" => .boolean false
  | "number" => .number 17 | "string" => .string (ascii "handler")
  | "methods-array" => .array 0 | "owner" => .object 5
  | _ => .object 3

private def observe (before after : State) (returned : Option Value) (handler : Value) (method : JSString) : Json := Id.run do
  let outerRef := match returned with | some (.object reference) => some reference | _ => none
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

private def asNumber : Value → Json
  | .number value => toJson value
  | _ => Json.null

private def runCase (expression : Expr) (json : Json) : Except String Json := do
  let method ← units (← json.getObjVal? "method")
  let events ← names json "names"
  let later ← names json "later"
  let order ← (← json.getObjVal? "order").getInt?
  let count ← (← json.getObjVal? "priorCount").getNat?
  let handler := handlerValue (← (← json.getObjVal? "handler").getStr?)
  let prior : List Value := List.replicate count (.object 2)
  let before : State := {
    environment := [("curNode", .object 5), ("method", .string method), ("handler", handler),
      ("possibleKeys", .set 1), ("order", .number order)]
    heap := [prior, [], [.string (ascii "frame-array")], [.string (ascii "handler-array")]]
    objects := [objectPrototypeProjection [], newDataObject emptyNullObject (ascii "marker") (.number 23),
      {prototype := some 0}, emptyNullObject, {prototype := some 0},
      newDataObject {prototype := some 4} (ascii "#methods") (.array 2)]
    functions := [⟨⟨"frame", .null⟩, []⟩]
    sets := [[ascii "frame-set"], StringSet.fromTrace events]
    privates := PrivateStore.ofData ([("methods", 7), ("patterns", 8)]) ([(5, [(7, .array 0), (8, .array 1)])])}
  let (firstReturn, afterFirst) ← (evalExpression 64 defaultSplitLimit expression before).mapError reprStr
  let first := afterFirst.heap[0]?.bind (fun entries => entries[count]?)
  let firstJson := observe before afterFirst first handler method
  let current ← match afterFirst.sets[1]? with | some entries => pure entries | none => throw "Missing Set"
  -- Explicit later events and caller-threaded environment/private state. No
  -- constructor, module-cell persistence or surrounding traversal is executed.
  let extended : State := {afterFirst with sets := afterFirst.sets.set 1 (later.foldl StringSet.add current)}
  let (secondReturn, final) ← (evalExpression 64 defaultSplitLimit expression extended).mapError reprStr
  let methods := final.heap[0]?.getD []
  let second := methods[count+1]?
  let oldObjects := decide (final.objects.take before.objects.length = before.objects)
  let otherArrays := decide ((final.heap.take before.heap.length).drop 1 = before.heap.drop 1)
  return Json.mkObj [("firstReturn", asNumber firstReturn), ("secondReturn", asNumber secondReturn),
    ("methodCount", toJson methods.length), ("prefixKept", toJson (decide (methods.take count = prior))),
    ("first", firstJson), ("second", observe extended final second handler method),
    ("firstUnchanged", toJson (observe before final first handler method == firstJson)),
    ("distinctStoredMaps", toJson (first != second)),
    ("privateSlotsKept", toJson (decide (final.privates = before.privates))),
    ("publicShadowKept", toJson (data final.objects[5]? (ascii "#methods") == some (.array 2))),
    ("orderAfter", match final.environment.lookup "order" with | some value => asNumber value | none => Json.null),
    ("setKept", toJson (decide (afterFirst.sets = before.sets) && decide (final.sets = extended.sets))),
    ("frameKept", toJson (oldObjects && otherArrays && decide (final.sets[0]? = before.sets[0]?) &&
      (reprStr final.functions == reprStr before.functions)))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let source ← match packet.getObjVal? "source" with | .ok value => value.getStr? | .error _ => pure NodeMethodsPush.pinnedSource
    let expression ← match parseExpression source ["curNode", "method", "handler", "possibleKeys", "order"] ["methods", "patterns"] with
      | some value => pure value | none => throw "Source parse rejected"
    return toJson (← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase expression))
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
