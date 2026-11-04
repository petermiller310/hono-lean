import HonoLean.Upstream.SourceSubset.RegExpConstructRules
import HonoLean.Upstream.PatternConstruct.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean

set_option autoImplicit false

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let unit ← value.getNat?
    if unit < 65536 then pure (UInt16.ofNat unit) else throw "Invalid UTF16 unit"

private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "array" => .array <$> (← json.getObjVal? "ref").getNat?
  | "object" => .object <$> (← json.getObjVal? "ref").getNat?
  | "function" => .function <$> (← json.getObjVal? "ref").getNat?
  | "constructor" => pure .objectConstructor
  | _ => throw "Unsupported fixture value"

private def encode (value : Value) : Except String Json := do
  let kind (name : String) (fields : List (String × Json) := []) := Json.mkObj (("kind",toJson name)::fields)
  match value with
  | .undefined => pure <| kind "undefined"
  | .null => pure <| kind "null"
  | .boolean value => pure <| kind "bool" [("value",toJson value)]
  | .number value => pure <| kind "number" [("value",toJson value)]
  | .string value => pure <| kind "string" [("units",toJson (value.map UInt16.toNat))]
  | .array ref => pure <| kind "array" [("ref",toJson ref)]
  | .object ref => pure <| kind "object" [("ref",toJson ref)]
  | .function ref => pure <| kind "function" [("ref",toJson ref)]
  | .objectConstructor => pure <| kind "constructor"
  | _ => throw "Unregistered output value"

private def encodeObject (object : OrdinaryObject) : Except String Json := do
  let own ← object.own.mapM fun (key,descriptor) => do
    let common := [("key",toJson (key.map UInt16.toNat))]
    let fields ← match descriptor with
      | .data value writable enumerable configurable => pure [("kind",toJson "data"),("value",← encode value),
          ("writable",toJson writable),("enumerable",toJson enumerable),("configurable",toJson configurable)]
      | .accessor getter setter enumerable configurable =>
        let getter := match getter with | .missing => "missing" | .prototype => "prototype" | .unsupported => "unsupported"
        let setter := match setter with | .missing => "missing" | .prototype => "prototype" | .unsupported => "unsupported"
        pure [("kind",toJson "accessor"),("getter",toJson getter),("setter",toJson setter),
          ("enumerable",toJson enumerable),("configurable",toJson configurable)]
    pure <| Json.mkObj (common++fields)
  pure <| Json.mkObj [("prototype",toJson object.prototype),("extensible",toJson object.extensible),("own",toJson own)]

private def ascii (s : String) : JSString := s.toList.map (UInt16.ofNat ∘ Char.toNat)
private def field (json : Json) (key : String) (fallback : String) : Except String String :=
  match json.getObjVal? key with | .ok value => value.getStr? | .error _ => pure fallback
private def flag (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with | .ok value => value.getBool? | .error _ => pure false
private def data (o : OrdinaryObject) (name : String) (v : Value) : OrdinaryObject := newDataObject o (ascii name) v

private def boolField (json : Json) (key : String) (fallback : Bool) : Except String Bool :=
  match json.getObjVal? key with | .ok value => value.getBool? | .error _ => pure fallback

private def encodeDescriptor : Option PropertyDescriptor → Except String Json
  | none => pure .null
  | some (.data value writable enumerable configurable) => do pure <| Json.mkObj [
    ("kind",toJson "data"),("value",← encode value),("writable",toJson writable),
    ("enumerable",toJson enumerable),("configurable",toJson configurable)]
  | some _ => throw "Expected projected data descriptor"
private def view (state : RegExpCallState) (ref : Nat) : Except String Json := do
  if (state.results.lookup ref).isNone then pure .null else do
    let properties : List (String × RegExpMatchProperty) := [("zero",.zero),("length",.length),("index",.index),("input",.input),("groups",.groups)]
    pure <| Json.mkObj (← properties.mapM fun (name,property) => do pure (name, ← encodeDescriptor (observeRegExpResult state ref property)))

private def encodeInstruction (op : RangeRegExp.Instruction) : Json :=
  match op with
  | .assertStart => Json.mkObj [("op",toJson "assertStart")]
  | .consumeRange lo hi => Json.mkObj [("op",toJson "consumeRange"),("lower",toJson lo.toNat),("upper",toJson hi.toNat)]
  | .repeatRange lo hi => Json.mkObj [("op",toJson "repeatRange"),("lower",toJson lo.toNat),("upper",toJson hi.toNat)]
  | .assertEnd => Json.mkObj [("op",toJson "assertEnd")]
  | .accept => Json.mkObj [("op",toJson "accept")]

private def runCase (program : RegExpConstructExpr) (json : Json) : Except String (Json × Json) := do
  let label ← units (← json.getObjVal? "label")
  let name ← units (← json.getObjVal? "name")
  let body ← units (← json.getObjVal? "body")
  let input ← match json.getObjVal? "input" with | .ok value => units value | .error _ => pure [49,50]
  let calleeKind ← field json "calleeKind" "constructor"
  let callee := if calleeKind = "number" then Value.number 0 else if calleeKind = "undefined" then .undefined else .function 6
  let some priorRecord := initializeRangeRecord (ascii "^[p-r]+$") [] | throw "Invalid fixed prior fixture"
  let proto : OrdinaryObject := {own := [(ascii "exec",.data (.function 5) true false true)],prototype := some 0}
  let caller := data emptyNullObject "kept" (.string (ascii "canary"))
  let previous : OrdinaryObject := ⟨[(lastIndexKey,.data (.number 17) false false false)],some 1,true⟩
  let methods : PrivateMethodTable := ⟨1,[⟨⟨"old",[],.named "void",[]⟩,[],[]⟩]⟩
  let functions : FunctionTable := ⟨2,[⟨⟨"old","value",[]⟩,[],[]⟩]⟩
  let members : MemberTable := ⟨3,[⟨⟨"exec","input",[.ret (.variable "input")]⟩,[],[]⟩,
    ⟨⟨"exec","input",[.ret (.arrayLiteral [(false,.variable "input")])]⟩,[],[]⟩]⟩
  let builtins : RegExpBuiltinTable := ⟨5,[.regexpExec]⟩
  let context : RegExpConstructContext := ⟨methods,functions,members,builtins,⟨6,[⟨1⟩]⟩⟩
  let before : RegExpCallState := {
    ambient := {
      environment := [("label",.string label),("match",.array 1),("RegExp",callee),("Alias",.function 6),
        ("alternateLabel",.string (ascii "alternate-label")),("alternateName",.string (ascii "alternate-name")),
        ("alternateBody",.string (ascii "[A-Z]+"))],
      objects := [objectPrototypeProjection [],proto,caller,previous],
      heap := [[.string (ascii "prior")],[.string label,.string name,.string body]],
      functions := [⟨⟨"old",.number 0⟩,[]⟩],
      thisValue := .object 2}
    brands := [(3,priorRecord)]
    results := [(0,⟨0,ascii "prior"⟩)]
  }
  match evalRegExpConstruct 128 defaultSplitLimit context program before with
  | .error _ => pure (Json.mkObj [("ok",toJson false)],.null)
  | .ok (returned, constructed) =>
    let .array tuple := returned | throw "Outside bounded tuple observer"
    let some values := constructed.ambient.heap[tuple]? | throw "Missing tuple"
    let some (Value.object reference) := values[2]? | throw "Outside bounded tuple slot2 observer"
    let some record := constructed.brands.lookup reference | throw "Missing initialized record"
    let (matched,after) ← (invokeRegExpExec (.object reference) [.string input] constructed).mapError reprStr
    let currentView ← match matched with | .array ref => view after ref | _ => pure .null
    let scope := decide (after.ambient.environment=before.ambient.environment) && after.ambient.thisValue==before.ambient.thisValue &&
      decide (after.ambient.privates=before.ambient.privates) && reprStr after.ambient.functions==reprStr before.ambient.functions &&
      after.ambient.sets==before.ambient.sets
    let oldFrames := decide (after.ambient.objects.take 4=before.ambient.objects) && decide (after.ambient.heap.take 2=before.ambient.heap)
    let objects ← after.ambient.objects.zipIdx.mapM fun (o,index) =>
      if index=0 then pure <| Json.mkObj [("intrinsic",toJson "Object.prototype")]
      else if index=1 then pure <| Json.mkObj [("intrinsic",toJson "RegExp.prototype")]
      else encodeObject o
    let execIsBuiltin := match getProperty propertyFuel after.ambient.objects reference (ascii "exec") with
      | .ok (.function handle) => handle == 5
      | _ => false
    let regexp := Json.mkObj [("ref",toJson reference),("source",toJson (record.originalSource.map UInt16.toNat)),
      ("flags",toJson (record.originalFlags.map UInt16.toNat)),
      ("execIsBuiltin",toJson execIsBuiltin)]
    let observed := Json.mkObj [("ok",toJson true),("returnedValue",← encode returned),
      ("heap",toJson (← after.ambient.heap.mapM (List.mapM encode))),("objects",toJson objects),("regexp",regexp),
      ("lookup",← encode matched),("view",currentView),("priorView",← view after 0),("scope",toJson scope),
      ("brandsKept",toJson (decide (after.brands.lookup 3=some priorRecord))),
      ("oldFrames",toJson (oldFrames && decide (after.results.lookup 0=before.results.lookup 0)))]
    let internal := Json.mkObj [("source",toJson (record.originalSource.map UInt16.toNat)),
      ("flags",toJson (record.originalFlags.map UInt16.toNat)),("compiled",toJson (record.compiled.map encodeInstruction))]
    pure (observed,internal)

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let source ← field packet "source" PatternConstruct.pinnedSource
    let bindings := ["label","match","RegExp","Alias","alternateLabel","alternateName","alternateBody"]
    match parseRegExpConstruct source bindings [] with
    | none => pure <| Json.mkObj [("parsed",toJson false)]
    | some program =>
      let results ← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase program)
      pure <| Json.mkObj [("parsed",toJson true),("results",toJson (results.map Prod.fst)),("modelOnlyRecords",toJson (results.map Prod.snd))]
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
