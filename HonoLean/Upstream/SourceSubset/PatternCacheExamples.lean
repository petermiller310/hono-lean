import HonoLean.Upstream.SourceSubset.PatternCacheRules
import HonoLean.Upstream.PatternCache.Generated
import HonoLean.Upstream.SourceSubset.LabelMatchRules

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace HonoLean.Upstream.SourceSubset.PatternCacheChecks
open ECMA2025

private def context : PatternCacheContext := ⟨labelStandardContext⟩
private def bindings : List String := ["label", "next", "patternCache", "RegExp"]
private def declaration : PatternCacheInit := ⟨"patternCache", "key", .named "string", .named "Pattern", .emptyObject⟩

private def v (name : String) : PatternCacheExpr := .ordinary (.variable name)
private def idx (name : String) (index : Nat) : PatternCacheExpr := .index (v name) (.ordinary (.number index))
private def keyTemplate : PatternCacheExpr := .template [] [(.variable "label", [35]), (.variable "next", [])]
private def cacheExpr : PatternCacheExpr := .index (v "patternCache") (v "cacheKey")
private def plain : PatternCacheExpr := .arrayLiteral [v "label", idx "match" 1, .ordinary (.boolean true)]
private def terminal : PatternCacheExpr := .arrayLiteral [v "label", idx "match" 1,
  .construct (.variable "RegExp") (.template [94] [(.index (.variable "match") (.number 2), [36])])]
private def lookahead : PatternCacheExpr := .arrayLiteral [v "cacheKey", idx "match" 1,
  .construct (.variable "RegExp") (.template [94]
    [(.index (.variable "match") (.number 2), [40,63,61,47]), (.variable "next", [41])])]
private def nextCondition : PatternCacheExpr :=
  .logicalAnd (.logicalAnd (v "next") (.strictNotEqual (idx "next" 0) (.ordinary (.string [58]))))
    (.strictNotEqual (idx "next" 0) (.ordinary (.string [42])))
private def block : List PatternCacheStmt :=
  [.declare "cacheKey" keyTemplate,
   .branch (.logicalNot cacheExpr)
     [.branch (idx "match" 2) [.assign cacheExpr (.conditional nextCondition lookahead terminal)] [.assign cacheExpr plain]] [],
   .ret cacheExpr]
private def program : List PatternCacheStmt :=
  [.declare "match" (.labelMatch (.variable "label") "match" labelActualLiteral), .branch (v "match") block [], .ret (.ordinary .null)]

theorem parses_complete_source_block_and_typed_initializer :
    parsePatternCacheBody PatternCache.pinnedSource bindings = some program ∧
    parsePatternCacheBlock PatternCache.pinnedBlock ("match" :: bindings) = some block ∧
    parsePatternCacheInit PatternCache.pinnedInit = some declaration := by cbv <;> repeat' constructor

private def idLabel : JSString := [58,105,100]
private def idName : JSString := [105,100]
private def initial (label : JSString) (next : Value) : LabelMatchState :=
  let old := labelStandardState label
  cacheWithAmbient old {old.base.regexp.ambient with environment :=
    ("next", next) :: ("RegExp", .function 6) :: old.base.regexp.ambient.environment}
private def activate (label : JSString) (next : Value) (before : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with environment :=
    ("label", .string label) :: ("next", next) :: ("RegExp", .function 6) :: before.base.regexp.ambient.environment}
private def call (label : JSString) (next : Value) (before : LabelMatchState) :=
  runPatternCache 256 defaultSplitLimit context program (activate label next before)
private def freshCall (label : JSString) (next : Value) := do
  let initialized ← initializePatternCache 8 defaultSplitLimit context declaration (initial label next)
  call label next initialized
private def entry (before : LabelMatchState) (key : JSString) :=
  getProperty propertyFuel before.base.regexp.ambient.objects 7 key
private def preload (value : Value) (label : JSString) (next : Value) := do
  let initialized ← initializePatternCache 8 defaultSplitLimit context declaration (initial label next)
  let key ← patternCacheKey label next
  let objects ← (setProperty propertyFuel initialized.base.regexp.ambient.objects 7 key value).mapError
    (PatternCacheError.evaluation ∘ EvalError.objectError)
  pure (cacheWithAmbient initialized {initialized.base.regexp.ambient with objects})

theorem primitive_raw_keys_and_string_index :
    patternCacheKey idLabel .undefined = patternCacheKey idLabel (.string (cacheAscii "undefined")) ∧
    patternCacheKey (cacheAscii ":a#b") (.string (cacheAscii "c")) = patternCacheKey (cacheAscii ":a") (.string (cacheAscii "b#c")) ∧
    cachePrimitiveToString (.number (-17)) = .ok [45,49,55] ∧
    cacheReadProperty (.string []) (.number 0) {} = .ok .undefined ∧
    cacheReadProperty (.string [55296]) (.number 0) {} = .ok (.string [55296]) := by cbv <;> repeat' constructor

/-- Actual50 creates ordinary{}; actual60 computes the capture array before
actual70 reserves/fills the tuple and ordinary Set stores it. No supplied m. -/
theorem full_source_cold_plain_uses_actual_producer_and_ordinary_store :
    (freshCall idLabel .undefined).map (fun (returned, after) =>
      (returned, after.base.regexp.ambient.heap[1]?, after.base.regexp.ambient.heap[2]?,
       entry after (idLabel ++ [35] ++ cacheAscii "undefined"),
       after.base.regexp.ambient.environment.lookup "match", after.base.regexp.ambient.thisValue,
       after.base.regexp.ambient.objects[7]?.map OrdinaryObject.prototype)) =
      .ok (.array 2, some [.string idLabel, .string idName, .undefined], some [.string idLabel, .string idName, .boolean true],
        .ok (.array 2), some (.array 0), .object 5, some (some 0)) := by cbv <;> repeat' constructor

/-- Any truthy value may be a hit; no tuple/RegExp/readiness is required. The
capture body '(' would fail if its cold constructor branch were evaluated. -/
theorem truthy_hits_skip_invalid_cold_constructor_and_keep_any_value :
    ([.boolean true, .number 1, .string [120], .array 0, .object 5, .function 0] : List Value).all
      (fun existing => match preload existing (cacheAscii ":id{(}") .undefined with
        | .ok before => match call (cacheAscii ":id{(}") .undefined before with
          | .ok (returned, after) => returned == existing && decide (after.base.regexp.ambient.heap.length = 2)
          | _ => false
        | _ => false) = true := by cbv <;> repeat' constructor

/-- Falsy PRESENT data values enter the store branch just like absence. -/
theorem present_falsy_data_values_are_replaced :
    ([.boolean false, .number 0, .string [], .null, .undefined] : List Value).all
      (fun existing => match preload existing idLabel .undefined with
        | .ok before => match call idLabel .undefined before with
          | .ok (returned, after) => returned == .array 2 &&
            (match entry after (idLabel ++ [35] ++ cacheAscii "undefined") with
             | .ok value => value == .array 2
             | .error _ => false)
          | _ => false
        | _ => false) = true := by cbv <;> repeat' constructor

private def pairCall (firstLabel : JSString) (firstNext : Value) (secondLabel : JSString) (secondNext : Value) := do
  let (first, middle) ← freshCall firstLabel firstNext
  let (second, after) ← call secondLabel secondNext middle
  pure (first, second, after.base.regexp.ambient.heap[2]?, after.base.regexp.ambient.heap.length,
    entry after (cacheAscii ":a#b#c"))

theorem persistent_same_cache_raw_separator_collision_both_orders :
    pairCall (cacheAscii ":a#b") (.string (cacheAscii "c")) (cacheAscii ":a") (.string (cacheAscii "b#c")) =
      .ok (.array 2, .array 2, some [.string (cacheAscii ":a#b"), .string (cacheAscii "a#b"), .boolean true], 4, .ok (.array 2)) ∧
    pairCall (cacheAscii ":a") (.string (cacheAscii "b#c")) (cacheAscii ":a#b") (.string (cacheAscii "c")) =
      .ok (.array 2, .array 2, some [.string (cacheAscii ":a"), .string (cacheAscii "a"), .boolean true], 4, .ok (.array 2)) := by cbv <;> repeat' constructor

theorem persistent_undefined_string_collision_both_orders :
    (pairCall idLabel .undefined idLabel (.string (cacheAscii "undefined"))).map (fun (first, second, row, length, _) => (first, second, row, length)) =
      .ok (.array 2, .array 2, some [.string idLabel, .string idName, .boolean true], 4) ∧
    (pairCall idLabel (.string (cacheAscii "undefined")) idLabel .undefined).map (fun (first, second, row, length, _) => (first, second, row, length)) =
      .ok (.array 2, .array 2, some [.string idLabel, .string idName, .boolean true], 4) := by cbv <;> repeat' constructor

/-- Miss returnsnull; terminalsafe68 constructs through the existing real
parser/compiler. Reached67 retains genuineAST and honestly refuses lookahead. -/
theorem miss_terminal_and_reached_lookahead_limits :
    (freshCall (cacheAscii "ordinary") .undefined).map (fun (value, after) => (value, after.base.regexp.ambient.heap.length)) = .ok (.null, 1) ∧
    (freshCall (cacheAscii ":id{[0-9]+}") .undefined).map (fun (value, after) =>
      (value, after.base.regexp.ambient.heap[2]?, after.base.regexp.brands.lookup 9)) =
      .ok (.array 2, some [.string (cacheAscii ":id{[0-9]+}"), .string idName, .object 9], some digitsRecord) ∧
    freshCall (cacheAscii ":id{[0-9]+}") (.string (cacheAscii "tail")) = .error (.constructor .grammarDomain) := by cbv <;> repeat' constructor

/-- Nativepreflight's raw invalid-body warmhit is reproduced with the same
actual ordinary cache and both actual calls. Reverseorder reaches constructor. -/
theorem warm_collision_skips_invalid_future_regexp_but_reverse_reaches_it :
    (do
      let (first, middle) ← freshCall idLabel (.string (cacheAscii "{(}#undefined"))
      let (second, after) ← call (cacheAscii ":id#{(}") .undefined middle
      pure (first, second, after.base.regexp.ambient.heap[2]?)) =
      .ok (.array 2, .array 2, some [.string idLabel, .string idName, .boolean true]) ∧
    freshCall (cacheAscii ":id#{(}") .undefined = .error (.constructor .grammarDomain) := by cbv <;> repeat' constructor

/-- Source74 is an actual current Get. This generic program changes the same
property after an earlier read; returning the earlier saved Value would fail. -/
theorem return_re_reads_current_cache_and_strict_set_rejects_readonly :
    (do
      let before ← preload (.number 1) idLabel .undefined
      let before := cacheWithAmbient before {before.base.regexp.ambient with environment :=
        ("cacheKey", .string (idLabel ++ [35] ++ cacheAscii "undefined")) :: before.base.regexp.ambient.environment}
      runPatternCache 32 defaultSplitLimit context
        [.declare "saved" cacheExpr, .assign cacheExpr (.ordinary (.number 2)), .ret cacheExpr] before).map Prod.fst = .ok (.number 2) ∧
    (do
      let before ← preload (.number 0) idLabel .undefined
      let object := {emptyLiteralObject with own := [(idLabel ++ [35] ++ cacheAscii "undefined", .data (.number 0) false true true)]}
      let before := cacheWithAmbient before {before.base.regexp.ambient with objects := before.base.regexp.ambient.objects.set 7 object}
      call idLabel .undefined before) = .error (.evaluation (.objectError .notWritable)) := by cbv <;> repeat' constructor

theorem frontend_scope_and_syntax_frontiers :
    (["const match = match", "const x = 9007199254740993", "return\npatternCache[cacheKey]", "next = label", "const k = `${f()}`", "const k = `a\\n${next}`"] |>.all
      (fun text => (parsePatternCacheBody text ("cacheKey" :: bindings)).isNone)) = true ∧
    (parsePatternCacheInit "const c: { [return: string]: Pattern } = {}\n").isNone = true := by cbv <;> repeat' constructor

/-- info: 'HonoLean.Upstream.SourceSubset.evalPatternCache_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalPatternCache_key
/-- info: 'HonoLean.Upstream.SourceSubset.executePatternCache_declare_label' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms executePatternCache_declare_label
/-- info: 'HonoLean.Upstream.SourceSubset.executePatternCacheAssignment_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms executePatternCacheAssignment_reference
/-- info: 'HonoLean.Upstream.SourceSubset.initializePatternCache_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initializePatternCache_empty
/-- info: 'HonoLean.Upstream.SourceSubset.evalPatternCache_array3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalPatternCache_array3
/-- info: 'HonoLean.Upstream.SourceSubset.runPatternCache_restores_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runPatternCache_restores_caller

end HonoLean.Upstream.SourceSubset.PatternCacheChecks
