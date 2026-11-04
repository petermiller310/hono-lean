import HonoLean.Upstream.SourceSubset.RegExpCallRules

set_option autoImplicit false

namespace HonoLean.Upstream.SourceSubset.RegExpCallChecks

open ECMA2025
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def execKey : JSString := [101, 120, 101, 99]
private def borrowedKey : JSString := [98, 111, 114, 114, 111, 119, 101, 100]
private def sourceKey : JSString := [115, 111, 117, 114, 99, 101]
private def priorText : JSString := [112, 114, 105, 111, 114]
private def input : JSString := [49, 50]
private def echo : MemberClosure := ⟨⟨"exec", "input", [.ret (.variable "input")]⟩, [], []⟩
private def arrayMethod : MemberClosure := ⟨⟨"exec", "input", [.ret (.arrayLiteral [(false, .variable "input")])]⟩, [], []⟩
private def methods : PrivateMethodTable := ⟨1, [⟨⟨"old", [], .named "void", []⟩, [], []⟩]⟩
private def functions : FunctionTable := ⟨2, [⟨⟨"old", "input", []⟩, [], []⟩]⟩
private def members : MemberTable := ⟨3, [echo, arrayMethod]⟩
private def builtins : RegExpBuiltinTable := ⟨5, [.regexpExec]⟩
private def matcher (last : Int) (writable : Bool) : OrdinaryObject :=
  {own := [(lastIndexKey, .data (.number last) writable false false),
     (borrowedKey, .data (.function 5) true true true)]
   prototype := some 2
   extensible := false}
private def before (last : Int := 17) (writable : Bool := false) : RegExpCallState :=
  {ambient := {
      environment := [("matcher", .object 1), ("restPathString", .string input), ("prior", .array 0),
        ("builtin", .function 5), ("m", .object 3)]
      objects := [objectPrototypeProjection [], matcher last writable,
        {own := [(execKey, .data (.function 5) true true true)], prototype := some 0}, emptyNullObject]
      heap := [[.string priorText]]
      functions := [⟨⟨"old", .number 0⟩, []⟩]
      thisValue := .object 3
      privates := ⟨[("caller", 9)], [(3, [(9, .data (.number 17))])]⟩ }
   brands := [(1, digitsRecord)]
   results := [(0, ⟨0, priorText⟩)]}
private def withExec (handle : Nat) (state : RegExpCallState) : RegExpCallState :=
  {state with ambient := {state.ambient with objects := (state.ambient.objects.set 1
    (newDataObject (matcher 0 true) execKey (.function handle)))}}
private def call (method : String) (arguments : List Expr) (state : RegExpCallState) :=
  runRegExpCall 64 defaultSplitLimit methods functions members builtins (.variable "matcher") method arguments state
private def view (state : RegExpCallState) (reference : Nat) : List (Option PropertyDescriptor) :=
  [.zero, .length, .index, .input, .groups].map (observeRegExpResult state reference)

/-- A real parser/compiler initializer, not a desired-match callback. Flags
and unsupported grammar remain visible boundaries rather than erased input. -/
theorem initialization_retains_source_code_and_rejects_other_profiles :
    initializeRangeRecord digitsPattern [] = some digitsRecord ∧
    initializeRangeRecord digitsPattern [103] = none ∧
    initializeRangeRecord [94, 91, 57, 45, 48, 93, 43, 36] [] = none := by decide

/-- Copied builtin identity under borrowed has precisely the same branch as
inherited exec. No method-spelling test selects builtin behavior. -/
theorem builtin_identity_under_borrowed_alias :
    (call "exec" [.variable "restPathString"] before).map (fun (returned, after) => (returned, after.ambient.heap, view after 1)) =
      (call "borrowed" [.variable "restPathString"] before).map (fun (returned, after) => (returned, after.ambient.heap, view after 1)) ∧
    (call "borrowed" [.variable "restPathString"] before).map Prod.fst = .ok (.array 1) := by cbv

/-- Fresh match1 retains ALL five own descriptors, including OWN undefined
 groups; old match0 and its view are not overwritten by the new result. -/
theorem successful_builtin_allocates_only_visible_result_and_preserves_prior_view :
    (call "exec" [.variable "restPathString"] before).map (fun (returned, after) =>
      (returned, after.ambient.heap, view after 1, view after 0, decide (after.brands = before.brands))) =
      .ok (.array 1, [[.string priorText], [.string input]],
        [some (.data (.string input) true true true), some (.data (.number 1) true false false),
         some (.data (.number 0) true true true), some (.data (.string input) true true true), some (.data .undefined true true true)],
        [some (.data (.string priorText) true true true), some (.data (.number 1) true false false),
         some (.data (.number 0) true true true), some (.data (.string priorText) true true true), some (.data .undefined true true true)], true) := by cbv

/-- Failure to match does not allocate a global@@match accumulator or a fresh
result array. This is the closed builtin's logical-heap projection. -/
theorem builtin_miss_returns_null_without_changing_state :
    invokeRegExpExec (.object 1) [.string []] before = .ok (.null, before) ∧
    invokeRegExpExec (.object 1) [.string [49, 50, 10]] before = .ok (.null, before) := by cbv

/-- The receiver brand is checked before argument coercion admission. Argument
EXPRESSION errors still occur before invoking any builtin brand operation. -/
theorem brand_precedes_coercion_but_follows_argument_evaluation :
    invokeRegExpExec (.object 1) [.object 0] {before with brands := []} = .error .unbrandedReceiver ∧
    invokeRegExpExec (.object 1) [.object 0] before = .error .unsupportedCoercion ∧
    call "exec" [.variable "missing"] {before with brands := []} = .error (.evaluation .missingVariable) := by cbv

/-- Invalid numeric state and absent brands are irrelevant to an ordinary
current callee. It returns the actual primitive and frames regex metadata. -/
theorem ordinary_replacement_has_no_builtin_brand_or_numeric_checks :
    let state := withExec 3 {before with brands := []}
    let state := {state with ambient := {state.ambient with objects := (state.ambient.objects.set 1
      (newDataObject (newDataObject (matcher 0 true) execKey (.function 3)) lastIndexKey (.string [120])))}}
    (call "exec" [.number 42] state).map (fun (returned, after) => (returned, after.ambient.heap, after.brands, after.results)) =
      .ok (.number 42, [[.string priorText]], [], [(0, ⟨0, priorText⟩)]) := by cbv

/-- An ordinary returned array has numeric contents in the heap but is not
registered as a BUILTIN match metadata view. This does not deny native array
length or other ordinary properties outside this observation projection. -/
theorem ordinary_array_return_does_not_gain_builtin_metadata :
    (call "exec" [.string input] (withExec 4 before)).map (fun (returned, after) =>
      (returned, after.ambient.heap, observeRegExpResult after 1 .length, view after 0)) =
      .ok (.array 1, [[.string priorText], [.string input]], none,
        [some (.data (.string priorText) true true true), some (.data (.number 1) true false false),
         some (.data (.number 0) true true true), some (.data (.string priorText) true true true), some (.data .undefined true true true)]) := by cbv

/-- Every modeled exact safe integer is read from the CURRENT public data
property, ToLength-converted, then retained unchanged even when readonly. -/
theorem current_numeric_lastIndex_is_retained_for_every_safe_integer (last : Int) (writable : Bool)
    (safe : last.natAbs ≤ maximumSafeInteger) :
    invokeRegExpExec (.object 1) [.string input] (before last writable) =
      .ok (.array 1, {before last writable with
        ambient := {(before last writable).ambient with heap := [[.string priorText], [.string input]]}
        results := [(1, ⟨0, input⟩), (0, ⟨0, priorText⟩)]}) := by
  have computed := invokeRegExpExec_range (before last writable) 1 digitsRecord (matcher last writable) input [] last writable 48 57
    rfl rfl rfl safe rfl rfl
  have accepted : RangeRegExp.Accepted 48 57 input := by decide
  simpa [rangeExecValue, rangeExecState, accepted, before] using computed

theorem integer_bounds_and_other_flags_are_explicit_model_boundaries :
    numericToLength (.number (-7)) = .ok 0 ∧
    numericToLength (.number 9007199254740991) = .ok 9007199254740991 ∧
    numericToLength (.number 9007199254740992) = .error .unsupportedNumber ∧
    numericToLength (.number (-9007199254740992)) = .error .unsupportedNumber ∧
    invokeRegExpExec (.object 1) [.string input]
      {before with brands := [(1, {digitsRecord with originalFlags := [103]})]} = .error .unsupportedFlags := by cbv

/-- Public source is a separate property from the stored original source/code.
Spoofing it cannot replace the operational matcher used by the builtin. -/
theorem public_source_spoof_does_not_change_internal_pattern :
    let state := {before with ambient := {before.ambient with objects := (before.ambient.objects.set 1
      (newDataObject (matcher 17 false) sourceKey (.string [94, 120, 36])))}}
    (call "exec" [.string input] state).map Prod.fst = .ok (.array 1) := by cbv

/-- A parsed ordinary method mutates old match0's ACTUAL array via shift. Its
view keeps named index/input/groups, but observes new length0 and missing0. -/
theorem metadata_numeric_fields_follow_current_heap_after_ordinary_mutation :
    (parseMemberMethod "exec(input) { return input.shift() }" [] []).map (fun program =>
      (runRegExpCall 64 defaultSplitLimit methods functions ⟨3, [⟨program, [], []⟩, arrayMethod]⟩ builtins
        (.variable "matcher") "exec" [.variable "prior"] (withExec 3 before)).map
          (fun (returned, after) => (returned, after.ambient.heap, view after 0))) =
      some (.ok (.string priorText, [[]], [none, some (.data (.number 0) true false false),
        some (.data (.number 0) true true true), some (.data (.string priorText) true true true), some (.data .undefined true true true)])) := by cbv

private def declarationSource : String := "            const m = matcher.exec(restPathString)\n"
private def writerSource : String := "exec(input) { this.lastIndex = 17\nreturn null }"

/-- Separate real parsed activations: ordinary exec writes current lastIndex,
shared assignment restores the builtin identity, then source156 reads17. The
brand record has no lastIndex cache to accidentally reuse. -/
theorem restored_builtin_reads_lastIndex_written_by_ordinary_source_method :
    let outcome : Except RegExpCallError (Value × Except ObjectError Value × List (List Value) × List (Option PropertyDescriptor)) := do
      let program ← match parseMemberMethod writerSource [] [] with | some method => pure method | none => throw .representation
      let declaration ← match parseMemberDeclaration declarationSource ["matcher", "restPathString"] [] with
        | some declaration => pure declaration | none => throw .representation
      let actualMembers : MemberTable := ⟨3, [⟨program, [], []⟩, arrayMethod]⟩
      let changed ← executeRegExpDeclaration 64 defaultSplitLimit methods functions actualMembers builtins declaration (withExec 3 (before 0 true))
      let assignment ← match parseAssignment "matcher.exec = builtin" ["matcher", "builtin"] with
        | some assignment => pure assignment | none => throw .representation
      let (_, ambient) ← (executeAssignment 32 defaultSplitLimit assignment changed.ambient).mapError .evaluation
      let restored := {changed with ambient}
      let after ← executeRegExpDeclaration 64 defaultSplitLimit methods functions actualMembers builtins declaration restored
      let m ← (lookupVariable after.ambient "m").mapError .evaluation
      pure (m, getProperty propertyFuel after.ambient.objects 1 lastIndexKey, after.ambient.heap, view after 1)
    outcome = .ok (.array 1, .ok (.number 17), [[.string priorText], [.string input]],
      [some (.data (.string input) true true true), some (.data (.number 1) true false false),
       some (.data (.number 0) true true true), some (.data (.string input) true true true), some (.data .undefined true true true)]) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.invokeRegExpExec_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invokeRegExpExec_range
/-- info: 'HonoLean.Upstream.SourceSubset.runRegExpCall_builtin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runRegExpCall_builtin
/-- info: 'HonoLean.Upstream.SourceSubset.runRegExpCall_ordinary_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runRegExpCall_ordinary_reduction

end HonoLean.Upstream.SourceSubset.RegExpCallChecks
