import HonoLean.Upstream.SourceSubset.PrivateInitialization
import HonoLean.Upstream.NodeInitialization.Generated
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
private def readField (state : State) (definition : DataClass) (owner : Nat) (name : String) : Except String Value :=
  (privateGet (.object owner) name {state with privates := {state.privates with names := definition.names}}).mapError reprStr
private def arrayLength (state : State) (value : Value) : Except String Nat := do
  let reference ← asArray value
  match state.heap[reference]? with | some values => pure values.length | none => throw "Missing array"
private def objectAt (state : State) (reference : Nat) : Except String OrdinaryObject :=
  match state.objects[reference]? with | some object => pure object | none => throw "Missing object"

private def runCase (preamble : List Stmt) (fields : List PrivateField) (helper : NoArgFunction) (json : Json) : Except String Json := do
  let counts ← (← items json "counts").mapM Json.getNat?
  let objectCount ← natural json "baseObjects" 1
  if objectCount = 0 then throw "Base needs a supplied prototype"
  let arrayCount ← natural json "baseArrays" 0
  let stamps ← (← items json "existingStamps").mapM Json.getNat?
  let base : State := {
    environment := [("createNullObject", .function 0), ("outer", .number 41)],
    objects := objectPrototypeProjection [] :: List.replicate (objectCount - 1) emptyNullObject,
    heap := List.replicate arrayCount [], functions := [⟨helper, []⟩],
    privates := PrivateStore.ofData (stamps.zipIdx.map (fun (stamp, index) => ("old" ++ toString index, stamp))) (if stamps.isEmpty then [] else [(0, stamps.map (fun stamp => (stamp, .boolean true)))])}
  let completed ← (execute 64 defaultSplitLimit preamble
    {base with environment := withoutBindings base.environment (declaredNames preamble)}).mapError reprStr
  let module ← match completed with | .normal state => pure state | _ => throw "Unexpected preamble return"
  let emptyParams ← lookup module "emptyParams"
  let emptyReference ← asObject emptyParams
  let (after, _, definitions, instances) ← counts.zipIdx.foldlM
    (fun (state, world, definitions, instances) (count, classIndex) => do
      let (definition, world) ← match defineDataClass fields state world with
        | some result => pure result | none => throw "Data definition rejected"
      let (state, instances) ← (List.range count).foldlM (fun (current, owners) _ => do
        let (owner, next) ← (instantiateDataClass 96 defaultSplitLimit definition (some 0) current).mapError reprStr
        return (next, owners ++ [(classIndex, owner)])) (state, instances)
      return (state, world, definitions ++ [definition], instances)) (module, initialPrivateWorld module, [], [])
  let snapshots ← instances.mapM fun (classIndex, owner) => do
    let definition ← match definitions[classIndex]? with | some value => pure value | none => throw "Missing definition"
    let methods ← readField after definition owner "methods"
    let children ← readField after definition owner "children"
    let patterns ← readField after definition owner "patterns"
    let pattern ← readField after definition owner "pattern"
    let params ← readField after definition owner "params"
    return (owner, methods, children, patterns, pattern, params)
  let observations ← snapshots.mapM fun (owner, methods, children, patterns, pattern, params) => do
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
      ("publicOwnCount", toJson object.own.length), ("prototypeKept", toJson (decide (object.prototype = some 0)))]
  let arrays ← snapshots.flatMapM fun (_, methods, _, patterns, _, _) => do pure [← asArray methods, ← asArray patterns]
  let children ← snapshots.mapM fun (_, _, children, _, _, _) => asObject children
  let matrix := definitions.map fun definition => instances.map fun (_, owner) =>
    (privateGet (.object owner) "methods" {after with privates := {after.privates with names := definition.names}}).isOk
  let unbrandedState : State := {after with objects := after.objects ++ [{prototype := some 0}]}
  let unbrandedRejected := definitions.all fun definition =>
    !(privateGet (.object after.objects.length) "methods" {unbrandedState with privates := {unbrandedState.privates with names := definition.names}}).isOk
  let oldObjectsKept := (List.range base.objects.length).all (fun reference => decide (after.objects[reference]? = base.objects[reference]?))
  let oldArraysKept := (List.range base.heap.length).all (fun reference => decide (after.heap[reference]? = base.heap[reference]?))
  let oldSlotsKept := base.privates.slots.all (fun (owner, fields) => decide (after.privates.slots.lookup owner = some fields))
  if !(oldObjectsKept && oldArraysKept && oldSlotsKept && decide (after.environment = module.environment) && decide (after.privates.names = base.privates.names)) then
    throw "Old storage or caller scope frame changed"
  let order ← lookup module "order"
  return Json.mkObj [("instances", toJson observations), ("arraysIsolated", toJson (decide arrays.Nodup)),
    ("childrenIsolated", toJson (decide children.Nodup && !children.contains emptyReference)),
    ("sharedParams", toJson (snapshots.all (fun (_, _, _, _, _, value) => decide (value = emptyParams)))),
    ("moduleNullPrototype", toJson (← objectAt after emptyReference).prototype.isNone),
    ("helperCalls", toJson (after.objects.length - base.objects.length - instances.length)),
    ("order", match order with | .number value => toJson value | _ => Json.null),
    ("classBrandMatrix", toJson matrix), ("unbrandedRejected", toJson unbrandedRejected)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock (← text packet "preambleSource" NodeInitialization.pinnedPreambleSource) ["createNullObject"] with
      | some value => pure value | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields (← text packet "fieldsSource" NodeInitialization.pinnedFieldsSource) ["createNullObject", "emptyParams"] with
      | some value => pure value | none => throw "Field parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with | some value => pure value | none => throw "Helper parse rejected"
    return toJson (← (← items packet "cases").mapM (runCase preamble fields helper))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
