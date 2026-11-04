import HonoLean.Upstream.SourceSubset.ArrayBindingRules
import HonoLean.Upstream.PatternConstruct.Source
import HonoLean.Upstream.NodeRegExpExec.Source
import HonoLean.Upstream.NodePatternBinding.Generated
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

private def encodeEvent (event : ArrayIteratorEvent) : Except String Json := do
  let make (name : String) (fields : List (String × Json)) := Json.mkObj (("event",toJson name)::fields)
  match event with
  | .symbolGet array value => pure <| make "symbolGet" [("array",toJson array),("value",← encode value)]
  | .iteratorAllocated reference array => pure <| make "iteratorAllocated" [("ref",toJson reference),("array",toJson array)]
  | .nextGet reference value => pure <| make "nextGet" [("ref",toJson reference),("value",← encode value)]
  | .lengthGet array length => pure <| make "lengthGet" [("array",toJson array),("length",toJson length)]
  | .elementGet array index value => pure <| make "elementGet" [("array",toJson array),("index",toJson index),("value",← encode value)]
  | .resultAllocated reference value done => pure <| make "resultAllocated" [("ref",toJson reference),("value",← encode value),("done",toJson done)]
  | .doneGet result value => pure <| make "doneGet" [("ref",toJson result),("value",← encode value)]
  | .valueGet result value => pure <| make "valueGet" [("ref",toJson result),("value",← encode value)]
  | .returnGet iterator value => pure <| make "returnGet" [("ref",toJson iterator),("value",← encode value)]
  | .initialized name value => pure <| make "initialized" [("name",toJson name),("value",← encode value)]

private def runCase (program : ArrayBindingDecl) (pipeline : Bool) (json : Json) : Except String (Json × Json) := do
  let label ← match json.getObjVal? "label" with | .ok value => units value | .error _ => pure []
  let name ← match json.getObjVal? "name" with | .ok value => units value | .error _ => pure []
  let body ← match json.getObjVal? "body" with | .ok value => units value | .error _ => pure []
  let input ← match json.getObjVal? "input" with | .ok value => units value | .error _ => pure [49,50]
  let values ← if pipeline then pure [.string label,.string name,.string body] else
    (← (← json.getObjVal? "values").getArr?).toList.mapM decode
  let alternate ← match json.getObjVal? "alternateValues" with
    | .ok values => (← values.getArr?).toList.mapM decode
    | .error _ => pure [.string (ascii "alternate-label"),.string (ascii "alternate-name"),.object 6]
  let iteratorKind ← field json "iteratorKind" "inherited"
  let patternKind ← field json "patternKind" "array"
  let pattern := if patternKind="number" then Value.number 0 else if patternKind="undefined" then .undefined else
    if patternKind="string" then .string (ascii "abc") else .array 1
  let ownIterator := if iteratorKind="alias" then Value.function 7 else if iteratorKind="number" then .number 0 else .undefined
  let some priorRecord := initializeRangeRecord (ascii "^[p-r]+$") [] | throw "Bad prior fixture"
  let regexpPrototype : OrdinaryObject := ⟨[(ascii "exec",.data (.function 5) true false true)],some 0,true⟩
  let arrayPrototype : OrdinaryObject := ⟨[],some 0,true⟩
  let iteratorPrototype : OrdinaryObject := ⟨[],some 0,true⟩
  let arrayIteratorPrototype : OrdinaryObject := ⟨[(iteratorNextKey,.data (.function 8) true false true)],some 3,true⟩
  let caller := data emptyNullObject "kept" (.string (ascii "canary"))
  let previous : OrdinaryObject := ⟨[(lastIndexKey,.data (.number 17) false false false)],some 1,true⟩
  let methods : PrivateMethodTable := ⟨1,[⟨⟨"old",[],.named "void",[]⟩,[],[]⟩]⟩
  let functions : FunctionTable := ⟨2,[⟨⟨"old","value",[]⟩,[],[]⟩]⟩
  let members : MemberTable := ⟨3,[⟨⟨"exec","input",[.ret (.variable "input")]⟩,[],[]⟩,
    ⟨⟨"exec","input",[.ret (.arrayLiteral [(false,.variable "input")])]⟩,[],[]⟩]⟩
  let builtins : RegExpBuiltinTable := ⟨5,[.regexpExec]⟩
  let constructors : RegExpConstructContext := ⟨methods,functions,members,builtins,⟨6,[⟨1⟩]⟩⟩
  let context : ArrayIteratorContext := ⟨constructors,⟨7,[.arrayValues,.arrayNext]⟩,2,4,0⟩
  let realmSymbols : List (ArraySymbolOwner × List (ArraySymbol × PropertyDescriptor)) :=
    [(.object 2,[(.iterator,.data (.function 7) true false true)])]
  let symbols := if !pipeline && iteratorKind != "inherited" then
    (.array 1,[(ArraySymbol.iterator,.data ownIterator true true true)])::realmSymbols else realmSymbols
  let before : ArrayBindingState := {
    regexp := {
      ambient := {
        environment := [("pattern",pattern),("alternatePattern",.array 2),("restPathString",.string input),
          ("name",.string (ascii "outer-name")),("matcher",.object 6),("m",.object 5),
          ("label",.string label),("match",.array 1),("RegExp",.function 6)]
        objects := [objectPrototypeProjection [],regexpPrototype,arrayPrototype,iteratorPrototype,arrayIteratorPrototype,caller,previous]
        heap := [[.string (ascii "prior")],values,alternate]
        functions := [⟨⟨"old",.number 0⟩,[]⟩]
        thisValue := .object 5}
      brands := [(6,priorRecord)]
      results := [(0,⟨0,ascii "prior"⟩)]}
    symbols := symbols}
  let failed := (Json.mkObj [("ok",toJson false)],Json.null)
  let prepared ← if pipeline then do
    let some ctor := parseRegExpConstruct PatternConstruct.pinnedSource PatternConstruct.bindings [] | throw "Original constructor parser failed"
    match evalRegExpConstruct 128 defaultSplitLimit constructors ctor before.regexp with
    | .error _ => pure none
    | .ok (tuple,after) => pure (some (tuple,{before with regexp := {after with ambient := {after.ambient with environment := ("pattern",tuple)::after.ambient.environment}}}))
    else pure (some (Value.undefined,before))
  let some (produced,initial) := prepared | return failed
  match runArrayBinding 128 defaultSplitLimit context program initial with
  | .error _ => pure failed
  | .ok (record,bound) =>
    let outcome := if pipeline then
      match parseMemberDeclaration NodeRegExpExec.pinnedSource NodeRegExpExec.bindings [] with
      | none => Except.error (RegExpCallError.representation)
      | some declaration => executeRegExpDeclaration 128 defaultSplitLimit methods functions members builtins declaration bound.regexp
      else .ok bound.regexp
    match outcome with
    | .error _ => pure failed
    | .ok regexp =>
      let after := {bound with regexp := regexp}
      let actualName ← (lookupVariable after.regexp.ambient "name").mapError reprStr
      let actualMatcher ← (lookupVariable after.regexp.ambient "matcher").mapError reprStr
      let m ← (lookupVariable after.regexp.ambient "m").mapError reprStr
      let visibleCount := if pipeline then 8 else 7
      let intrinsicNames := ["Object.prototype","RegExp.prototype","Array.prototype","Iterator.prototype","ArrayIterator.prototype"]
      let visibleObjects ← (after.regexp.ambient.objects.take visibleCount).zipIdx.mapM fun (object,index) =>
        if index<5 then pure <| Json.mkObj [("intrinsic",toJson (intrinsicNames[index]!))] else encodeObject object
      let symbolView := fun owner kind reference => do
        pure <| Json.mkObj [("kind",toJson (kind : String)),("ref",toJson (reference : Nat)),("descriptor",← encodeDescriptor (symbolOwn after owner))]
      let symbols ← ([symbolView (.array 1) "array" 1,symbolView (.array 2) "array" 2,symbolView (.object 2) "object" 2] ++
        (if pipeline then [symbolView (.array 3) "array" 3] else [])).mapM id
      let currentView ← match m with | .array ref => view after.regexp ref | _ => pure .null
      let producedView ← if pipeline then do
        let some newRecord := after.regexp.brands.lookup 7 | throw "Missing produced record"
        pure <| Json.mkObj [("tuple",← encode produced),("regex",← encode (.object 7)),
          ("source",toJson (newRecord.originalSource.map UInt16.toNat)),("flags",toJson (newRecord.originalFlags.map UInt16.toNat))]
        else pure .null
      let scope := decide (after.regexp.ambient.environment.drop ((arrayBindingNames program.elements).length + if pipeline then 1 else 0)=initial.regexp.ambient.environment) &&
        after.regexp.ambient.thisValue==before.regexp.ambient.thisValue && decide (after.regexp.ambient.privates=before.regexp.ambient.privates) &&
        after.regexp.ambient.sets==before.regexp.ambient.sets && reprStr after.regexp.ambient.functions==reprStr before.regexp.ambient.functions
      let oldFrames := decide (after.regexp.ambient.objects.take 7=before.regexp.ambient.objects) &&
        decide (after.regexp.ambient.heap.take 3=before.regexp.ambient.heap) && decide (after.symbols=before.symbols) &&
        decide (after.regexp.results.lookup 0=before.regexp.results.lookup 0)
      let observed := Json.mkObj [("ok",toJson true),("name",← encode actualName),("matcher",← encode actualMatcher),("m",← encode m),
        ("heap",toJson (← after.regexp.ambient.heap.mapM (List.mapM encode))),("visibleObjects",toJson visibleObjects),("symbols",toJson symbols),
        ("view",currentView),("priorView",← view after.regexp 0),("produced",producedView),("scope",toJson scope),("oldFrames",toJson oldFrames),
        ("brandsKept",toJson (decide (after.regexp.brands.lookup 6=some priorRecord)))]
      let cursor ← match after.iterators.lookup record.iterator with | some cursor => pure cursor | none => throw "Missing iterator projection"
      let internal := Json.mkObj [("record",Json.mkObj [("iterator",toJson record.iterator),("nextMethod",← encode record.nextMethod),("done",toJson record.done)]),
        ("cursor",Json.mkObj [("array",toJson cursor.array),("nextIndex",toJson cursor.nextIndex)]),
        ("allocated",toJson (← (after.regexp.ambient.objects.drop visibleCount).mapM encodeObject)),
        ("trace",toJson (← after.trace.mapM encodeEvent))]
      pure (observed,internal)

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output : Except String Json := do
    let packet ← Json.parse input
    let source ← field packet "source" NodePatternBinding.pinnedSource
    let mode ← field packet "mode" "binding"
    let bindings := ["pattern","alternatePattern","restPathString","label","match","RegExp","name","matcher","m"]
    match parseArrayBinding source bindings [] with
    | none => pure <| Json.mkObj [("parsed",toJson false)]
    | some program =>
      let results ← (← (← packet.getObjVal? "cases").getArr?).toList.mapM (runCase program (mode="pipeline"))
      pure <| Json.mkObj [("parsed",toJson true),("results",toJson (results.map Prod.fst)),("modelOnlyProtocol",toJson (results.map Prod.snd))]
  match output with | .ok value => (← IO.getStdout).putStrLn value.compress | .error message => throw (IO.userError message)
