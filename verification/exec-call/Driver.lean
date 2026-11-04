import HonoLean.Upstream.SourceSubset.MemberCall
import HonoLean.Upstream.NodeExecCall.Generated
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

private def runCase (decl : Stmt) (method : MemberMethod) (json : Json) : Except String Json := do
  let input ← units (← json.getObjVal? "input")
  let inherited ← flag json "inherited"
  let handle ← match json.getObjVal? "methodHandle" with | .ok value => value.getNat? | .error _ => pure 3
  let calleeKind ← field json "calleeKind" "method"
  let boxValue ← match json.getObjVal? "boxValue" with | .ok value => decode value | .error _ => pure (.string (ascii "captured"))
  let execDescriptor ← match calleeKind with
    | "method" => pure <| PropertyDescriptor.data (.function handle) true true true
    | "undefined" => pure <| PropertyDescriptor.data .undefined true true true
    | "number" => pure <| PropertyDescriptor.data (.number 7) true true true
    | "null" => pure <| PropertyDescriptor.data .null true true true
    | "missingGetter" => pure <| PropertyDescriptor.accessor .missing .missing true true
    | "prototypeGetter" => pure <| PropertyDescriptor.accessor .prototype .missing true true
    | _ => throw "Unknown callee fixture"
  let matcher : OrdinaryObject := {own := [(ascii "other", .data (.function 4) true true true)] ++
    (if inherited then [] else [(ascii "exec",execDescriptor)]), prototype := some 2}
  let prototype := if inherited then data emptyNullObject "exec" (.function 3) else emptyNullObject
  let box := data (data emptyNullObject "value" boxValue) "calls" (.array 0)
  let captures := [("box",Value.object 3),("input",.string (ascii "captured parameter shadow"))]
  let methodTable : MemberTable := ⟨3,[⟨method,captures,[("secret",41)]⟩,
    ⟨⟨"other","input",[.ret .null]⟩,captures,[("secret",41)]⟩]⟩
  let methods : PrivateMethodTable := ⟨1,[⟨⟨"old",[],.named "void",[]⟩,[],[]⟩]⟩
  let functions : FunctionTable := ⟨2,[⟨⟨"old","value",[]⟩,[],[]⟩]⟩
  let before : State := {
    environment := [("matcher",.object 1),("restPathString",.string input),("m",.object 4),
      ("box",.object 4),("input",.string (ascii "caller parameter shadow"))]
    objects := [objectPrototypeProjection [],matcher,prototype,box,emptyNullObject]
    heap := [[]]
    functions := [⟨⟨"old",.number 0⟩,[]⟩]
    thisValue := .object 4
    privates := ⟨[("caller",9)],[(1,[(41,.data (.number 7))]),(4,[(9,.data (.number 17))])]⟩
  }
  match executeMemberDeclaration 1024 defaultSplitLimit methods functions methodTable decl before with
  | .error _ => pure <| Json.mkObj [("ok",toJson false)]
  | .ok after =>
    let name ← match decl with | .declare name _ => pure name | _ => throw "Expected declaration"
    let declared ← (lookupVariable after name).mapError reprStr
    let m ← (lookupVariable after "m").mapError reprStr
    let secret ← (privateGet (.object 1) "secret" {after with privates := {after.privates with names := [("secret",41)]}}).mapError reprStr
    let caller ← (privateGet (.object 4) "caller" after).mapError reprStr
    let scope := decide (after.environment = (name,declared)::before.environment) &&
      after.thisValue==before.thisValue && after.privates.names==before.privates.names && caller==.number 17 &&
      after.functions.length==before.functions.length && after.sets==before.sets && after.objects[0]?==before.objects[0]?
    let objects ← after.objects.zipIdx.mapM fun (object,index) =>
      if index=0 then pure <| Json.mkObj [("intrinsic",toJson "Object.prototype")] else encodeObject object
    pure <| Json.mkObj [("ok",toJson true),("declaredName",toJson name),("declaredValue",← encode declared),("m",← encode m),
      ("guard",toJson (truthy m)),("heap",toJson (← after.heap.mapM (List.mapM encode))),
      ("objects",toJson objects),("secret",← encode secret),("scope",toJson scope)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let result : Except String Json := do
    let packet ← Json.parse input
    let source ← field packet "source" NodeExecCall.pinnedSource
    let methodSource ← field packet "methodSource" "exec(input) { return [input] }"
    match parseMemberDeclaration source ["matcher","restPathString","box"] [],
        parseMemberMethod methodSource ["box","input"] ["secret"] with
    | some decl, some method => pure <| Json.mkObj [("parsed",toJson true),
        ("results",toJson (← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase decl method)))]
    | _,_ => pure <| Json.mkObj [("parsed",toJson false)]
  match result with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
