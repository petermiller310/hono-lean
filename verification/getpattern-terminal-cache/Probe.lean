import HonoLean.Upstream.SourceSubset.PatternCache
import HonoLean.Upstream.PatternCache.Generated
import Lean.Data.Json

open HonoLean.Upstream HonoLean.Upstream.SourceSubset ECMA2025 Lean
set_option autoImplicit false

private def units (value : Json) : Except String JSString := do
  (← value.getArr?).toList.mapM fun item => do
    let n ← item.getNat?
    if n < 65536 then pure (UInt16.ofNat n) else throw "Invalid UTF16 unit"
private def array (value : Json) (name : String) : Except String (List Json) := do
  let values ← (← value.getObjVal? name).getArr?
  pure values.toList
private def string (value : JSString) : Json := toJson (value.map UInt16.toNat)
private def nextValue (value : Json) : Except String Value := do
  match ← (← value.getObjVal? "kind").getStr? with
  | "undefined" => pure .undefined
  | "string" => .string <$> units (← value.getObjVal? "units")
  | _ => throw "Outside optional-string probe domain"
private def tuple (value : Value) (state : LabelMatchState) : Except String (Nat × JSString × JSString × Nat) := do
  let .array reference := value | throw "Not a returned tuple"
  let some [.string label, .string name, .object regex] := state.base.regexp.ambient.heap[reference]? | throw "Not a regex tuple"
  pure (reference,label,name,regex)
private def query (record : RangeRegExpRecord) (input : JSString) : Except String Json := do
  match RangeRegExp.execute record.compiled input with
  | .exhausted => throw "Unexpected VM exhaustion"
  | .noMatch => pure .null
  | .matched result =>
    pure <| Json.mkObj [("index",toJson result.start),("value",string (input.drop result.start |>.take (result.stop-result.start))),
      ("captures",toJson (result.captures.map (fun capture => capture.map (fun (start,stop) => string (input.drop start |>.take (stop-start))))))]
private def labelProjection (record : Option LabelRegExpRecord) :=
  record.map (fun record => (record.source,record.flags,record.compiled))
private def metadataFrames (before after : LabelMatchState) : Bool :=
  ((List.range before.base.regexp.ambient.objects.length).all fun reference =>
    decide (after.base.regexp.brands.lookup reference = before.base.regexp.brands.lookup reference) &&
    decide (labelProjection (after.brands.lookup reference) = labelProjection (before.brands.lookup reference))) &&
  ((List.range before.base.regexp.ambient.heap.length).all fun reference =>
    decide (after.base.regexp.results.lookup reference = before.base.regexp.results.lookup reference) &&
    decide (after.results.lookup reference = before.results.lookup reference)) &&
  decide (after.trace.take before.trace.length = before.trace) && decide (after.base.trace = before.base.trace) &&
  decide (after.base.symbols = before.base.symbols) && decide (after.base.iterators = before.base.iterators) &&
  decide (after.symbols = before.symbols) && decide (after.accessors = before.accessors)
private def run (program : List PatternCacheStmt) (fixture : Json) : Except String Json := do
  let label ← units (← fixture.getObjVal? "label")
  let next ← nextValue (← fixture.getObjVal? "next")
  let initial := labelStandardState label
  let initial := cacheWithAmbient initial {initial.base.regexp.ambient with environment :=
    [("RegExp",.function 6),("label",.string label),("next",next)]++initial.base.regexp.ambient.environment}
  let some declaration := parsePatternCacheInit PatternCache.pinnedInit | throw "Typed init parser refused"
  let initialized ← (initializePatternCache 512 defaultSplitLimit ⟨labelStandardContext⟩ declaration initial).mapError reprStr
  let (value,after) ← (runPatternCache 2048 defaultSplitLimit ⟨labelStandardContext⟩ program initialized).mapError reprStr
  let (reference,actualLabel,name,regex) ← tuple value after
  let (again,reused) ← (runPatternCache 2048 defaultSplitLimit ⟨labelStandardContext⟩ program after).mapError reprStr
  let (referenceAgain,_,_,regexAgain) ← tuple again reused
  let some record := reused.base.regexp.brands.lookup regex | throw "No actual constructed range brand"
  let some object := reused.base.regexp.ambient.objects[regex]? | throw "No actual constructed regex object"
  let some (.data (.number lastIndex) writable enumerable configurable) := object.own.lookup lastIndexKey | throw "No lastIndex DATA"
  let property ← (patternCacheKey label next).mapError reprStr
  let stored ← (getProperty propertyFuel reused.base.regexp.ambient.objects initial.base.regexp.ambient.objects.length property).mapError reprStr
  let queries ← (← array fixture "queries").mapM fun value => units value >>= query record
  let old := initial.base.regexp.ambient
  let framed := decide (reused.base.regexp.ambient.heap.take old.heap.length = old.heap) &&
    (List.range old.objects.length).all (fun ref => decide (reused.base.regexp.ambient.objects[ref]? = old.objects[ref]?)) &&
    decide (reused.base.regexp.ambient.environment = initialized.base.regexp.ambient.environment) &&
    decide (reused.base.regexp.ambient.privates = old.privates) &&
    decide (reused.base.regexp.ambient.sets = old.sets) &&
    decide (reused.base.regexp.ambient.thisValue = old.thisValue) &&
    (reprStr reused.base.regexp.ambient.functions == reprStr old.functions) &&
    metadataFrames initial after && metadataFrames after reused &&
    decide (reused.base.regexp.ambient.heap.take after.base.regexp.ambient.heap.length = after.base.regexp.ambient.heap) &&
    decide (reused.base.regexp.ambient.objects.take after.base.regexp.ambient.objects.length = after.base.regexp.ambient.objects)
  pure <| Json.mkObj [("ok",toJson true),("label",string actualLabel),("name",string name),
    ("source",string record.originalSource),("flags",string record.originalFlags),
    ("lastIndex",Json.mkObj [("value",toJson lastIndex),("writable",toJson writable),("enumerable",toJson enumerable),("configurable",toJson configurable)]),
    ("sameTuple",toJson (decide (reference=referenceAgain))),("sameRegex",toJson (decide (regex=regexAgain))),
    ("cacheReturnsSameTuple",toJson (decide (stored=value))),("oldFrames",toJson framed),("queries",toJson queries)]
private def packet (value : Json) : Except String Json := do
  let source ← match value.getObjVal? "source" with | .ok text => text.getStr? | .error _ => pure PatternCache.pinnedSource
  match parsePatternCacheBody source ["label","next","patternCache","RegExp"] with
  | none => pure <| Json.mkObj [("parsed",toJson false)]
  | some program =>
    let results := (← array value "cases").map fun fixture =>
      match run program fixture with
      | .ok result => result
      | .error _ => Json.mkObj [("ok",toJson false)]
    pure <| Json.mkObj [("parsed",toJson true),("results",toJson results)]

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  match Json.parse (← stdin.readToEnd) >>= packet with
  | .ok result => stdout.putStrLn result.compress; pure 0
  | .error error => stderr.putStrLn error; pure 1
