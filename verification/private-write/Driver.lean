import HonoLean.Upstream.SourceSubset.PrivateClass
import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodePrivateWrite.Generated
import HonoLean.Upstream.CreateNullObject.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

private def ascii (text : String) : JSString := text.toList.map (UInt16.ofNat ∘ Char.toNat)
private def items (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with | .ok value => (·.toList) <$> value.getArr? | .error _ => pure []
private def text (json : Json) (key fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok value => value.getStr? | .error _ => pure fallback
private def boolean (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with | .ok value => value.getBool? | .error _ => pure false

private def privateNames : List String :=
  ["methods", "children", "patterns", "pattern", "params", "pushHandlerSets"]
private def bindings : List String :=
  ["emptyParams", "nextNode", "node", "child", "params", "createNullObject", "METHOD_NAME_ALL", "Object"]

private structure Programs where
  seed : Assignment
  reset : Assignment
  propagation : Assignment
  wildcard : Assignment
  parameter : Assignment

private def parseWrite (source : String) : Except String Assignment :=
  match parseAssignment source bindings privateNames true with
  | some assignment => pure assignment
  | none => throw "Private assignment source rejected"

private def readPrivate (state : State) (definition : SelectedPrivateClass) (owner : Nat) (name : String) :
    Except String Value :=
  (privateGet (.object owner) name
    {state with privates := {state.privates with names := definition.names}}).mapError reprStr

private def runCase (preamble : List Stmt) (fields : List PrivateField) (method : PrivateMethod)
    (helper : NoArgFunction) (programs : Programs) (input : Json) : Except String Json := do
  let base : State := {
    environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string (ascii "ALL"))]
    objects := [objectPrototypeProjection []]
    functions := [⟨helper, []⟩, ⟨⟨"inputFunction", .number 7⟩, []⟩] }
  let completed ← (execute 64 defaultSplitLimit preamble
    {base with environment := withoutBindings base.environment (declaredNames preamble)}).mapError reprStr
  let module ← match completed with | .normal state => pure state | _ => throw "Unexpected preamble return"
  let shared ← (lookupVariable module "emptyParams").mapError reprStr
  let initialTable : PrivateMethodTable := ⟨2, []⟩
  let (first, world, table) ← match definePrivateClass fields [method] module
      (initialPrivateClassWorld module initialTable) initialTable with
    | some result => pure result | none => throw "First class definition rejected"
  let (second, _, _table) ← match definePrivateClass fields [method] module world table with
    | some result => pure result | none => throw "Second class definition rejected"
  let (parent, one) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) module).mapError reprStr
  let (child, two) ← (instantiatePrivateClass 96 defaultSplitLimit first (some 0) one).mapError reprStr
  let (foreign, initialized) ← (instantiatePrivateClass 96 defaultSplitLimit second (some 0) two).mapError reprStr
  let objectA := initialized.objects.length
  let objectB := objectA + 1
  let plain := objectA + 2
  let clone := objectA + 3
  let proxy := objectA + 4
  let array := initialized.heap.length
  let allocated : State := {initialized with
    objects := initialized.objects ++ [emptyNullObject, emptyNullObject, emptyNullObject,
      {prototype := some 0}, {prototype := some 0}]
    heap := initialized.heap ++ [[]]}
  let methodValue ← readPrivate allocated first parent "pushHandlerSets"
  let named : List (String × Value) := [
    ("shared", shared), ("objectA", .object objectA), ("objectB", .object objectB),
    ("array", .array array), ("fn", .function 1), ("method", methodValue),
    ("parent", .object parent), ("child", .object child), ("foreign", .object foreign),
    ("plain", .object plain), ("clone", .object clone), ("proxy", .object proxy)]
  let decode : String → Value := fun code => match named.lookup code with
    | some value => value
    | none => match code with
      | "u" => .undefined | "n" => .null | "f" => .boolean false
      | "z" => .number 0 | "empty" => .string [] | "one" => .number 1
      | "text" => .string [120] | "unicode" => .string [55296, 233] | _ => .undefined
  let select : String → Value := fun name => match name with
    | "null" => .null | "undefined" => .undefined | "zero" => .number 0
    | _ => decode name
  let encode : Value → Except String Json := fun value => do
    match named.find? (fun entry => decide (entry.2 = value)) with
    | some (name, _) => pure <| Json.mkObj [("kind", toJson name)]
    | none => match value with
      | .undefined => pure <| Json.mkObj [("kind", toJson "undefined")]
      | .null => pure <| Json.mkObj [("kind", toJson "null")]
      | .boolean value => pure <| Json.mkObj [("kind", toJson "bool"), ("value", toJson value)]
      | .number value => pure <| Json.mkObj [("kind", toJson "number"), ("value", toJson value)]
      | .string value => pure <| Json.mkObj [("kind", toJson "string"), ("units", toJson (value.map UInt16.toNat))]
      | _ => throw "Unknown observation"
  let activation := fun (state : State) (thisValue nextNode node child params : Value) =>
    {state with
      thisValue := thisValue
      environment := [("nextNode", nextNode), ("node", node), ("child", child), ("params", params)] ++ module.environment
      privates := {state.privates with names := first.names}}
  -- Fixed source202 seeds the input cells in separate activations. Packet
  -- source faults affect only the main operation, never this initialization.
  let a := decode (← text input "a" "u")
  let b := decode (← text input "b" "n")
  let seedA := activation allocated (.object parent) (.object parent) (.object parent) (.object parent) a
  let (_, seededA) ← (executeAssignment 64 defaultSplitLimit programs.seed seedA).mapError reprStr
  let seedB := activation seededA (.object parent) (.object child) (.object parent) (.object child) b
  let (_, seededB) ← (executeAssignment 64 defaultSplitLimit programs.seed seedB).mapError reprStr
  let observedBefore ← [readPrivate seededB first parent "params", readPrivate seededB first child "params",
    readPrivate seededB second foreign "params"].mapM id
  let frozen ← boolean input "frozen"
  -- The ordinary hooks are deliberately unsupported by the object interpreter.
  -- Private operations must frame these exact descriptors without invoking them.
  let shadow := fun (object : OrdinaryObject) => {object with
    own := [(ascii "params", .accessor .unsupported .unsupported true (!frozen))]
    extensible := !frozen}
  let parentObject ← match seededB.objects[parent]? with | some object => pure object | none => throw "Missing parent"
  let childObject ← match seededB.objects[child]? with | some object => pure object | none => throw "Missing child"
  let prepared : State := {seededB with objects := (seededB.objects.set parent (shadow parentObject)).set child (shadow childObject)}
  let target := select (← text input "target" "child")
  let source := select (← text input "source" "parent")
  let rhs := decode (← text input "rhs" "one")
  let caller := activation prepared target target source target rhs
  let op ← text input "op" "propagation"
  let executed := match op with
    | "reset" => executeAssignment 64 defaultSplitLimit programs.reset caller
    | "propagation" => executeAssignment 64 defaultSplitLimit programs.propagation caller
    | "wildcard" => executeAssignment 64 defaultSplitLimit programs.wildcard caller
    | "parameter" => executeAssignment 64 defaultSplitLimit programs.parameter caller
    | _ => .ok (.undefined, caller)
  match executed with
  | .error _ => pure <| Json.mkObj [("ok", toJson false)]
  | .ok (returned, after) =>
    let observedAfter ← [readPrivate after first parent "params", readPrivate after first child "params",
      readPrivate after second foreign "params"].mapM id
    let methodIdentity := first.firstIdentity + fields.length
    let methodTagKept := [parent, child].all fun owner =>
      decide (((after.privates.elements.lookup owner).bind (fun elements => elements.lookup methodIdentity)) =
        some (.method methodValue))
    let methodParent ← readPrivate after first parent "pushHandlerSets"
    let methodChild ← readPrivate after first child "pushHandlerSets"
    let frozenKept := [parent, child].all fun owner =>
      (after.objects[owner]?).any (fun object => object.extensible == !frozen)
    if !(decide (after.environment = caller.environment) && decide (after.thisValue = caller.thisValue) &&
        decide (after.privates.names = caller.privates.names) && decide (after.heap = caller.heap) &&
        decide (after.sets = caller.sets)) then throw "Private-write caller/array/Set frame changed"
    pure <| Json.mkObj [("ok", toJson true), ("returned", ← encode returned),
      ("before", toJson (← observedBefore.mapM encode)), ("after", toJson (← observedAfter.mapM encode)),
      ("setterCalls", toJson (0 : Nat)), ("methodKept", toJson (methodTagKept &&
        decide (methodParent = methodValue) && decide (methodChild = methodValue))),
      ("publicUnchanged", toJson (decide (after.objects = caller.objects))), ("frozenKept", toJson frozenKept)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let preamble ← match parseBlock NodeClass.pinnedPreambleSource ["createNullObject"] with
      | some program => pure program | none => throw "Preamble parse rejected"
    let fields ← match parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"] with
      | some program => pure program | none => throw "Fields parse rejected"
    let method ← match parsePrivateMethod NodeClass.pinnedMethodSource ["METHOD_NAME_ALL", "createNullObject", "Object"] privateNames with
      | some program => pure program | none => throw "Method parse rejected"
    let helper ← match parseNoArg CreateNullObject.pinnedSource with
      | some program => pure program | none => throw "Helper parse rejected"
    let programs : Programs := ⟨← parseWrite NodePrivateWrite.pinnedParameterSource,
      ← parseWrite (← text packet "resetSource" NodePrivateWrite.pinnedResetSource),
      ← parseWrite (← text packet "propagationSource" NodePrivateWrite.pinnedPropagationSource),
      ← parseWrite (← text packet "wildcardSource" NodePrivateWrite.pinnedWildcardSource),
      ← parseWrite (← text packet "parameterSource" NodePrivateWrite.pinnedParameterSource)⟩
    toJson <$> (← items packet "cases").mapM (runCase preamble fields method helper programs)
  match output with
  | .ok value => (← IO.getStdout).putStrLn value.compress
  | .error message => throw (IO.userError message)
