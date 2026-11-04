import HonoLean.Upstream.SourceSubset.RegExpCallRules
import HonoLean.Upstream.NodeRegExpExec.Generated
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

private def coreCase (json : Json) : Except String Json := do
  let pattern ← units (← json.getObjVal? "pattern")
  let input ← units (← json.getObjVal? "input")
  match RangeRegExp.parse pattern with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some ast =>
    let code ← match RangeRegExp.compile ast with | some code => pure code | none => throw "Parsed grammar did not compile"
    let outcome := match json.getObjVal? "fuel" with
      | .ok value => match value.getNat? with | .ok fuel => RangeRegExp.run fuel code 0 input | .error _ => .exhausted
      | .error _ => RangeRegExp.execute code input
    let result := match outcome with
      | .exhausted => Json.mkObj [("kind",toJson "exhausted")]
      | .noMatch => Json.mkObj [("kind",toJson "noMatch")]
      | .matched value => Json.mkObj [("kind",toJson "matched"),("start",toJson value.start),("stop",toJson value.stop),("captures",toJson value.captures.length)]
    let compiled := code.map fun op => match op with
      | .assertStart => Json.mkObj [("op",toJson "assertStart")]
      | .consumeRange lo hi => Json.mkObj [("op",toJson "consumeRange"),("lower",toJson lo.toNat),("upper",toJson hi.toNat)]
      | .repeatRange lo hi => Json.mkObj [("op",toJson "repeatRange"),("lower",toJson lo.toNat),("upper",toJson hi.toNat)]
      | .assertEnd => Json.mkObj [("op",toJson "assertEnd")]
      | .accept => Json.mkObj [("op",toJson "accept")]
    pure <| Json.mkObj [("parsed",toJson true),("compiled",toJson compiled),("outcome",result)]

private def runCase (decl : Stmt) (json : Json) : Except String Json := do
  let pattern ← units (← json.getObjVal? "pattern")
  let input ← units (← json.getObjVal? "input")
  match initializeRangeRecord pattern [] with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some record =>
    let last ← match json.getObjVal? "lastIndex" with | .ok value => value.getInt? | .error _ => pure 0
    let writable ← boolField json "writable" true
    let extensible ← boolField json "extensible" true
    let branded ← boolField json "brand" true
    let own ← boolField json "ownExec" false
    let handle ← match json.getObjVal? "handle" with | .ok value => value.getNat? | .error _ => pure 5
    let calleeKind ← field json "calleeKind" "method"
    let matcher := data (data emptyLiteralObject "other" (.function 3)) "borrowed" (.function 5)
    let matcher := {matcher with prototype := some 2, own := (lastIndexKey,.data (.number last) writable false false)::matcher.own}
    let matcher := if own || handle != 5 || calleeKind != "method" then
      data matcher "exec" (if calleeKind = "number" then .number 0 else .function handle) else matcher
    let matcher ← match json.getObjVal? "spoofSource" with
      | .ok value => do pure {matcher with own := (ascii "source",.data (.string (← units value)) true false true)::matcher.own}
      | .error _ => pure matcher
    let matcher := {matcher with extensible := extensible}
    let proto : OrdinaryObject := {own := [(ascii "exec",.data (.function 5) true false true)],prototype := some 0}
    let alternate := data emptyNullObject "exec" (.function 3)
    let methods : PrivateMethodTable := ⟨1,[⟨⟨"old",[],.named "void",[]⟩,[],[]⟩]⟩
    let functions : FunctionTable := ⟨2,[⟨⟨"old","value",[]⟩,[],[]⟩]⟩
    let members : MemberTable := ⟨3,[⟨⟨"exec","input",[.ret (.variable "input")]⟩,[],[]⟩,
      ⟨⟨"exec","input",[.ret (.arrayLiteral [(false,.variable "input")])]⟩,[],[]⟩]⟩
    let builtins : RegExpBuiltinTable := ⟨5,[.regexpExec]⟩
    let before : RegExpCallState := {
      ambient := {
        environment := [("matcher",.object 1),("restPathString",.string input),("m",.object 3),
          ("alternate",.object 3),("alternateInput",.string (ascii "x"))],
        objects := [objectPrototypeProjection [],matcher,proto,alternate],
        heap := [[.string (ascii "prior")]],
        functions := [⟨⟨"old",.number 0⟩,[]⟩],
        thisValue := .object 3}
      brands := if branded then [(1,record)] else []
      results := [(0,⟨0,ascii "prior"⟩)]
    }
    match executeRegExpDeclaration 1024 defaultSplitLimit methods functions members builtins decl before with
    | .error _ => pure <| Json.mkObj [("parsed",toJson true),("ok",toJson false)]
    | .ok after =>
      let name ← match decl with | .declare name _ => pure name | _ => throw "Expected declaration"
      let declared ← (lookupVariable after.ambient name).mapError reprStr
      let m ← (lookupVariable after.ambient "m").mapError reprStr
      let scope := decide (after.ambient.environment = (name,declared)::before.ambient.environment) &&
        after.ambient.thisValue==before.ambient.thisValue && decide (after.ambient.privates=before.ambient.privates) &&
        reprStr after.ambient.functions == reprStr before.ambient.functions && after.ambient.sets==before.ambient.sets &&
        after.ambient.objects[0]? == before.ambient.objects[0]? && after.ambient.objects[2]? == before.ambient.objects[2]?
      let objects ← after.ambient.objects.zipIdx.mapM fun (o,index) =>
        if index=0 then pure <| Json.mkObj [("intrinsic",toJson "Object.prototype")]
        else if index=2 then pure <| Json.mkObj [("intrinsic",toJson "RegExp.prototype")]
        else encodeObject o
      let currentView ← match declared with | .array ref => view after ref | _ => pure .null
      pure <| Json.mkObj [("parsed",toJson true),("ok",toJson true),("declaredName",toJson name),
        ("declaredValue",← encode declared),("m",← encode m),("guard",toJson (truthy m)),
        ("heap",toJson (← after.ambient.heap.mapM (List.mapM encode))),("objects",toJson objects),
        ("view",currentView),("priorView",← view after 0),("scope",toJson scope),
        ("brandsKept",toJson (decide (after.brands = before.brands))),
        ("priorKept",toJson (after.ambient.heap[0]? == before.ambient.heap[0]? && decide (after.results.lookup 0 = before.results.lookup 0)))]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    match packet.getObjVal? "coreCases" with
    | .ok values => pure <| toJson (← (← values.getArr?).toList.mapM coreCase)
    | .error _ =>
      let source ← field packet "source" NodeRegExpExec.pinnedSource
      match parseMemberDeclaration source ["matcher","restPathString","alternate","alternateInput"] [] with
      | none => pure <| Json.mkObj [("parsed",toJson false)]
      | some decl => pure <| toJson (← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase decl))
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
