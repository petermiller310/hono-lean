import HonoLean.Upstream.SourceSubset.RegExpConstructRules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.SourceSubset.RegExpConstructChecks
open ECMA2025

private def context : RegExpConstructContext :=
  ⟨⟨1, [⟨⟨"old", [], .named "void", []⟩, [], []⟩]⟩,
   ⟨2, [⟨⟨"oldFunction", "x", []⟩, [], []⟩]⟩,
   ⟨3, [⟨⟨"ordinary", "x", [.ret (.variable "x")]⟩, [], []⟩]⟩,
   ⟨4, [.regexpExec]⟩, ⟨5, [⟨2⟩]⟩⟩
private def label : JSString := [58, 110, 97, 109, 101]
private def name : JSString := [110, 97, 109, 101]
private def body : JSString := [91, 48, 45, 57, 93, 43]
private def sourceText : String := "[label, match[1], new RegExp(`^${match[2]}$`)]"
private def sourceProgram : RegExpConstructExpr :=
  .arrayLiteral [.ordinary (.variable "label"), .ordinary (.index (.variable "match") (.number 1)),
    .construct (.variable "RegExp") (.template [94] (.index (.variable "match") (.number 2)) [36])]
private def before : RegExpCallState :=
  {ambient := {
    environment := [("label", .string label), ("match", .array 0), ("RegExp", .function 5), ("Alias", .function 5)]
    heap := [[.undefined, .string name, .string body], [.number 17]]
    objects := [objectPrototypeProjection, initializedRegExpObject 2, ⟨[], some 0, true⟩]
    functions := [⟨⟨"old", .number 7⟩, []⟩]
    privates := .ofData [("secret", 9)] [(1, [(9, .number 17)])]
    sets := [[name]]
    thisValue := .object 1}
   brands := [(1, digitsRecord)]
   results := [(1, ⟨0, name⟩)]}

private def observe (result : Except RegExpConstructError (Value × RegExpCallState)) :=
  result.map (fun (value, after) => (value, after.ambient.heap, after.ambient.objects,
    after.brands, after.results, after.ambient.environment, after.ambient.privates,
    after.ambient.functions.length, after.ambient.sets, after.ambient.thisValue))

/-- Actual template, NewExpression and three array elements are retained. -/
theorem parses_original_tuple_and_constructor :
    parseRegExpConstruct sourceText ["label", "match", "RegExp"] = some sourceProgram ∧
    parseRegExpConstruct "new RegExp(`^${match[2]}$`)" ["match", "RegExp"] =
      some (.construct (.variable "RegExp") (.template [94] (.index (.variable "match") (.number 2)) [36])) := by
  cbv
  exact ⟨rfl, rfl⟩

/-- Supported syntax is intentionally bounded; malformed/coercive/full-template
frontiers are not silently transformed into the selected source. -/
theorem rejects_unsupported_templates_new_and_array_syntax :
    (["new RegExp(`^${match[2]}${match[1]}$`)", "new RegExp(`^${match[2]}\\n$`)",
      "new RegExp(tag`^${match[2]}$`)", "new RegExp(`^[0-9]+$`)",
      "new RegExp()", "new RegExp(`^${match[2]}$`, 'g')", "[, label]",
      "[label,, match[1]]", "[label, match[1], new RegExp(`^${match[2]}$`)] garbage",
      "new RegExp(`^${++match[2]}$`)", "new RegExp(`^${match[2]}\n$`)"]
      |>.all (fun text => (parseRegExpConstruct text ["label", "match", "RegExp"]).isNone)) = true := by cbv

/-- The literal result is checked on the actual source parser's output. Old
arrays, ordinary cells, initialized brands and all nonallocation frames survive. -/
theorem parsed_tuple_constructs_actual_record_and_preserves_frames :
    (parseRegExpConstruct sourceText ["label", "match", "RegExp"]).map (fun program =>
      observe (evalRegExpConstruct 32 defaultSplitLimit context program before)) =
    some (.ok (.array 2,
      before.ambient.heap ++ [[.string label, .string name, .object 3]],
      before.ambient.objects ++ [initializedRegExpObject 2],
      (3, digitsRecord) :: before.brands, before.results, before.ambient.environment,
      before.ambient.privates, 1, before.ambient.sets, .object 1)) := by cbv

/-- Identity is carried by the current value, independent of the spelling. -/
theorem current_constructor_alias_and_replacement :
    (evalRegExpConstruct 16 defaultSplitLimit context
      (.construct (.variable "Alias") (.template [94] (.index (.variable "match") (.number 2)) [36])) before).map Prod.fst =
      .ok (.object 3) ∧
    evalRegExpConstruct 16 defaultSplitLimit context
      (.construct (.number 5) (.template [94] (.index (.variable "match") (.number 2)) [36])) before =
      .error .constructorDomain := by cbv

/-- Saved constructor comes from a real array element. Argument evaluation
shifts that same old array, but dispatch still invokes its saved identity. -/
theorem saves_constructor_before_operand_mutates_its_source :
    let state := {before with ambient := {before.ambient with
      environment := ("constructors", .array 2) :: before.ambient.environment
      heap := before.ambient.heap ++ [[.function 5]]}}
    (parseRegExpConstruct "new constructors[0](`^${constructors.shift() && match[2]}$`)" ["constructors", "match"]).map
      (fun program => (evalRegExpConstruct 32 defaultSplitLimit context program state).map
        (fun (value, after) => (value, after.ambient.heap))) =
      some (.ok (.object 3, before.ambient.heap ++ [[]])) := by cbv

/-- NoArray constructor/species hook: outer[] exists before the inner[] is
created, so the fresh references distinguish allocation order. -/
theorem array_create_precedes_element_evaluation :
    (parseRegExpConstruct "[[], new RegExp(`^${match[2]}$`)]" ["RegExp", "match"]).map
      (fun program => (evalRegExpConstruct 32 defaultSplitLimit context program before).map
        (fun (value, after) => (value, after.ambient.heap))) =
      some (.ok (.array 2, before.ambient.heap ++ [[.array 3, .object 3], []])) := by cbv

/-- Operand errors precede constructor admission. Unbound callee Get fails
before the argument, unlike a saved nonconstructor's later domain check. -/
theorem callee_get_and_argument_error_priority :
    let invalid := .template [94] (.index (.variable "label") (.number 0)) [36]
    evalRegExpConstruct 16 defaultSplitLimit context (.construct (.variable "missing") invalid) before =
      .error (.evaluation .missingVariable) ∧
    evalRegExpConstruct 16 defaultSplitLimit context
      (.construct (.number 7) (.template [94] (.variable "missing") [36])) before =
      .error (.evaluation .missingVariable) ∧
    evalRegExpConstruct 16 defaultSplitLimit context
      (.construct (.number 7) (.template [94] (.number 42) [36])) before =
      .error .coercionDomain := by cbv

/-- Raw runtime template values preserve even lone surrogates/backslashes;
they fail the genuine selected regexp grammar instead of being escaped. -/
theorem raw_utf16_substitution_and_bad_grammar :
    constructTemplateValue [94] (.string [55296, 92, 233]) [36] =
      .ok (.string [94, 55296, 92, 233, 36]) ∧
    invokeRegExpConstructor context (.function 5) (.string [94, 91, 57, 45, 48, 93, 43, 36]) before =
      .error .grammarDomain ∧
    invokeRegExpConstructor context (.function 5) (.string [94, 55296, 36]) before =
      .error .grammarDomain := by cbv

/-- The intermediate descriptor is undefined, final descriptor is+0, and old
cells survive. This is the model's initialized-record projection, not a
claim that native intermediate internal slots are absent. -/
theorem allocation_initialization_and_table_frontiers :
    (regExpAllocatedState before 2).ambient.objects[3]? = some (uninitializedRegExpObject 2) ∧
    invokeRegExpConstructor {context with constructors := ⟨0, [⟨2⟩]⟩} (.function 0) (.string digitsPattern) before =
      .error .representation ∧
    invokeRegExpConstructor {context with constructors := ⟨5, [⟨19⟩]⟩} (.function 5) (.string digitsPattern) before =
      .error .prototypeDomain := by cbv

/-- Symbolic arbitrary safe endpoints, not a switch on the digit string. -/
theorem arbitrary_safe_endpoints_construct (lower upper : UInt16)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) :
    invokeRegExpConstructor context (.function 5) (.string [94, 91, lower, 45, upper, 93, 43, 36]) before =
      .ok (.object 3, regExpConstructedState before 2 (constructedRangeRecord lower upper)) := by
  exact invokeRegExpConstructor_range context (.function 5) before ⟨2⟩ ⟨[], some 0, true⟩ lower upper
    rfl rfl rfl safeLower safeUpper ordered

/-- info: 'HonoLean.Upstream.SourceSubset.initializeRangeRecord_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms initializeRangeRecord_safe
/-- info: 'HonoLean.Upstream.SourceSubset.invokeRegExpConstructor_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms invokeRegExpConstructor_range
/-- info: 'HonoLean.Upstream.SourceSubset.construction_old_object' depends on axioms: [propext] -/
#guard_msgs in
#print axioms construction_old_object
/-- info: 'HonoLean.Upstream.SourceSubset.evalRegExpConstruct_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalRegExpConstruct_saved

end HonoLean.Upstream.SourceSubset.RegExpConstructChecks
