import HonoLean.Upstream.SourceSubset.PatternCache
import HonoLean.Upstream.PatternCache.Generated
import Lean.Data.Json
open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean
set_option autoImplicit false

private def units (json : Json) : Except String JSString := do
  (← json.getArr?).toList.mapM fun value => do
    let n ← value.getNat?
    if n < 65536 then pure (UInt16.ofNat n) else throw "Invalid UTF16 unit"
private def field (json : Json) (name fallback : String) : Except String String :=
  match json.getObjVal? name with | .ok value => value.getStr? | .error _ => pure fallback
private def flag (json : Json) (name : String) (fallback : Bool) : Except String Bool :=
  match json.getObjVal? name with | .ok value => value.getBool? | .error _ => pure fallback
private def entries (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with | .ok value => return (← value.getArr?).toList | .error _ => pure []
private def decode (json : Json) : Except String Value := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => .boolean <$> (← json.getObjVal? "value").getBool?
  | "number" => .number <$> (← json.getObjVal? "value").getInt?
  | "string" => .string <$> units (← json.getObjVal? "units")
  | "array" => .array <$> (← json.getObjVal? "ref").getNat?
  | "object" => do
    let ref ← (← json.getObjVal? "ref").getNat?
    match ref with | 0 => pure (.object 5) | 1 => pure (.object 6) | 2 => pure (.object 7) | 3 => pure (.object 8) | _ => throw "Unknown fixture object"
  | "function" => .function <$> (← json.getObjVal? "ref").getNat?
  | _ => throw "Outside fixture input domain"
private def descriptors (items : List Json) : Except String (List (JSString × PropertyDescriptor)) :=
  items.mapM fun item => do pure (← units (← item.getObjVal? "key"),.data (← decode (← item.getObjVal? "value"))
    (← flag item "writable" true) (← flag item "enumerable" true) (← flag item "configurable" true))
private def ambient (s : LabelMatchState) (a : State) : LabelMatchState := cacheWithAmbient s a
private def encode (visible : List (Value × String)) (value : Value) : Except String Json := do
  let make (kind : String) (fields : List (String × Json) := []) := Json.mkObj (("kind",toJson kind)::fields)
  match value with
  | .undefined => pure <| make "undefined"
  | .null => pure <| make "null"
  | .boolean b => pure <| make "bool" [("value",toJson b)]
  | .number n => pure <| make "number" [("value",toJson n)]
  | .string s => pure <| make "string" [("units",toJson (s.map UInt16.toNat))]
  | other =>
    let some (_,id) := visible.find? (fun p => decide (p.1=other)) | throw "Unexposed reference"
    pure <| make "reference" [("id",toJson id)]
private def descriptor (visible : List (Value × String)) : PropertyDescriptor → Except String Json
  | .data value w e c => do pure <| Json.mkObj [("kind",toJson "data"),("value",← encode visible value),
    ("writable",toJson w),("enumerable",toJson e),("configurable",toJson c)]
  | _ => throw "Visible accessor is outside DATA fixture domain"
private def register (s : LabelMatchState) (v : Value) (visible : List (Value × String)) (count : Nat) : List (Value × String) × Nat := Id.run do
  let reference := match v with | .array _ | .object _ | .function _ => true | _ => false
  if !reference || (visible.any (fun p => decide (p.1=v))) then return (visible,count)
  let name := "r"++toString count
  let mut result := visible++[(v,name)]
  match v with
  | .array ref =>
    for item in s.base.regexp.ambient.heap[ref]?.getD [] do
      match item with
      | .object ref => if (s.base.regexp.brands.lookup ref).isSome && !(result.any (fun p => decide (p.1=item))) then result := result++[(item,name++".regex")]
      | _ => pure ()
  | _ => pure ()
  return (result,count+1)
private def cacheView (visible : List (Value × String)) (s : LabelMatchState) : Except String Json := do
  let some object := s.base.regexp.ambient.objects[7]? | throw "Missing cache"
  let sorted := object.own.mergeSort (fun a b => compare a.1 b.1 != .gt)
  let own ← sorted.mapM fun (key,d) => do
    let fields ← (← descriptor visible d).getObj?
    pure <| Json.mkObj (("key",toJson (key.map UInt16.toNat))::fields.toList)
  let prototype := if object.prototype=some 8 then "parent" else if object.prototype=some 0 then "Object.prototype" else "unknown"
  pure <| Json.mkObj [("own",toJson own),("prototype",toJson prototype),("extensible",toJson object.extensible)]
private def graph (visible : List (Value × String)) (s : LabelMatchState) : Except String Json := do
  let nodes ← (visible.filter (fun p => p.2.startsWith "r")).mapM fun (value,id) => do
    match value with
    | .array ref =>
      let some values := s.base.regexp.ambient.heap[ref]? | throw "Missing returned array"
      pure <| Json.mkObj [("id",toJson id),("kind",toJson "array"),("values",toJson (← values.mapM (encode visible)))]
    | .object ref =>
      let some record := s.base.regexp.brands.lookup ref | throw "Unregistered returned object"
      let some object := s.base.regexp.ambient.objects[ref]? | throw "Missing returned regex"
      let some last := object.own.lookup lastIndexKey | throw "Missing lastIndex"
      pure <| Json.mkObj [("id",toJson id),("kind",toJson "regexp"),("source",toJson (record.originalSource.map UInt16.toNat)),
        ("flags",toJson (record.originalFlags.map UInt16.toNat)),("lastIndex",← descriptor visible last)]
    | _ => throw "Unexpected new exposed function"
  pure (toJson nodes)
private def oldFrames (before after : LabelMatchState) : Bool :=
  let b := before.base.regexp.ambient
  let a := after.base.regexp.ambient
  decide (a.heap.take b.heap.length = b.heap) && ((List.range b.objects.length).all (fun reference => reference == 7 || decide (a.objects[reference]? = b.objects[reference]?))) &&
  decide (a.privates = b.privates) && decide (a.sets = b.sets) && decide (a.thisValue = b.thisValue) &&
  decide (after.base.symbols = before.base.symbols) && decide (after.base.iterators = before.base.iterators) &&
  decide (after.symbols = before.symbols) && decide (after.accessors = before.accessors) && (reprStr a.functions == reprStr b.functions)
private def labelProjection (record : Option LabelRegExpRecord) :=
  record.map (fun record => (record.source,record.flags,record.compiled))
private def metadataFrames (before after : LabelMatchState) : Bool :=
  let old := before.base.regexp.ambient
  ((List.range old.objects.length).all fun reference =>
    decide (after.base.regexp.brands.lookup reference = before.base.regexp.brands.lookup reference) &&
    decide (labelProjection (after.brands.lookup reference) = labelProjection (before.brands.lookup reference))) &&
  ((List.range old.heap.length).all fun reference =>
    decide (after.base.regexp.results.lookup reference = before.base.regexp.results.lookup reference) &&
    decide (after.results.lookup reference = before.results.lookup reference)) &&
  decide (after.trace.take before.trace.length = before.trace) && decide (after.base.trace = before.base.trace)
private def runHistory (program : List PatternCacheStmt) (fixture : Json) : Except String Json := do
  let seed ← descriptors (← entries fixture "seed")
  let parent ← descriptors (← entries fixture "inherited")
  let extensible ← flag fixture "extensible" true
  let constructorKind ← field fixture "constructorKind" "builtin"
  let cacheKind ← field fixture "cacheKind" "object"
  let original := labelStandardState []
  let start := ambient original {original.base.regexp.ambient with
    environment := ("RegExp", if constructorKind = "number" then .number 0 else .function 6) :: original.base.regexp.ambient.environment
    heap := original.base.regexp.ambient.heap ++ [[]]}
  let some initializer := parsePatternCacheInit PatternCache.pinnedInit | throw "Original typed init parser refused"
  let initialized ← (initializePatternCache 512 defaultSplitLimit ⟨labelStandardContext⟩ initializer start).mapError reprStr
  let object : OrdinaryObject := ⟨seed,some (if parent.isEmpty then 0 else 8),extensible⟩
  let objects := (initialized.base.regexp.ambient.objects.set 7 object)++[⟨parent,none,true⟩]
  let initial := ambient initialized {initialized.base.regexp.ambient with objects}
  let globals := initial.base.regexp.ambient.environment
  let mut state := initial
  let mut visible : List (Value × String) := [(.array 0,"a0"),(.array 1,"a1"),(.object 5,"caller"),(.object 6,"oldRegex"),(.object 7,"cache"),(.object 8,"parent"),(.function 6,"RegExp")]
  let mut count := 0
  let mut observations : List Json := []
  for step in ← entries fixture "steps" do
    let label ← units (← step.getObjVal? "label")
    let next ← match step.getObjVal? "next" with | .ok value => decode value | .error _ => pure .undefined
    let matched ← match step.getObjVal? "match" with | .ok value => decode value | .error _ => pure .undefined
    let entry := ambient state {state.base.regexp.ambient with environment := [("label",.string label),("next",next),("match",matched),
      ("patternCache",if cacheKind="undefined"then .undefined else .object 7)]++globals}
    match runPatternCache 2048 defaultSplitLimit ⟨labelStandardContext⟩ program entry with
    | .error _ => observations := observations++[Json.mkObj [("ok",toJson false)]]; break
    | .ok (value,after) =>
      let restored := decide (after.base.regexp.ambient.environment = entry.base.regexp.ambient.environment)
      let metadata := metadataFrames entry after
      state := ambient after {after.base.regexp.ambient with environment := globals}
      let pair := register state value visible count
      visible := pair.1;count := pair.2
      let some currentCache := state.base.regexp.ambient.objects[7]? | throw "Missing actual cache"
      for (_,property) in currentCache.own.mergeSort (fun a b => compare a.1 b.1 != .gt) do
        match property with
        | .data exposed _ _ _ =>
          let pair := register state exposed visible count
          visible := pair.1;count := pair.2
        | _ => throw "Outside DATA fixture observation domain"
      observations := observations++[Json.mkObj [("ok",toJson true),("value",← encode visible value),("cache",← cacheView visible state),
        ("visibleGraph",← graph visible state),("oldFrames",toJson (oldFrames initial state && restored && metadata))]]
  pure (toJson observations)
private def packet (json : Json) : Except String Json := do
  let mode ← field json "mode" "full"
  let source ← field json "source" (if mode="block"then PatternCache.pinnedBlock else PatternCache.pinnedSource)
  let bindings := if mode="block"then ["label","next","patternCache","RegExp","match"] else ["label","next","patternCache","RegExp"]
  match parsePatternCacheBody source bindings with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some program => pure <| Json.mkObj [("parsed",toJson true),("results",toJson (← (← entries json "cases").mapM (runHistory program)))]
def main : IO UInt32 := do
  let stdin ← IO.getStdin;let stdout ← IO.getStdout;let stderr ← IO.getStderr
  match Json.parse (← stdin.readToEnd) >>= packet with
  | .ok result => stdout.putStrLn result.compress;pure 0
  | .error error => stderr.putStrLn error;pure 1
