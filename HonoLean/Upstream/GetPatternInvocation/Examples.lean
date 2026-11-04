import HonoLean.Upstream.GetPatternInvocation.Composition
import HonoLean.Upstream.LexicalArrow.Examples

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.GetPatternInvocation.Checks
open SourceSubset hiding pinnedSource
open GetPatternBody
open ECMA2025 LexicalArrow

private def context : PatternCacheContext := ⟨labelStandardContext⟩
private def root : OrdinaryObject := objectPrototypeProjection []
private def functionRoot : OrdinaryObject := ⟨[], some 0, true⟩
private def regexpRoot : OrdinaryObject := ⟨standardLabelRegExpOwn 9 5, some 0, true⟩

private theorem seed_setup : SetupInputs exampleSeed 7 root functionRoot :=
  ⟨rfl, rfl, by intro closure member; cases member⟩

private theorem seed_realm : LabelRealm exampleSeed.data labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [exampleSeed, cacheWithAmbient, labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < 8
  decide

theorem arbitrary_plain_initial_domain (name : JSString) (next : Option JSString) (extra : List Value)
    (validName : LabelRegExp.Name name) :
    InitialPlainInputs exampleSeed context 7 (.string (58 :: name) :: PatternCache.nextValue next :: extra)
      (58 :: name) name next root functionRoot none 1 :=
  ⟨seed_setup, explicit_arguments _ next extra, seed_realm, ⟨validName, rfl⟩,
    .absent rfl rfl rfl, by decide, Or.inl .absent, Or.inl rfl⟩

theorem arbitrary_plain_source_closure_witness (name : JSString) (next : Option JSString) (extra : List Value)
    (validName : LabelRegExp.Name name) :
    ∃ after,
      sourceSetup 7 exampleSeed = some (.ok (⟨0⟩, moduleWorld 7 exampleSeed)) ∧
      invokeBinding 257 defaultSplitLimit context 2 "getPattern" (.string (58 :: name) :: PatternCache.nextValue next :: extra)
        (moduleWorld 7 exampleSeed) = .returned (.array 2) after ∧
      SetupContract exampleSeed (moduleWorld 7 exampleSeed) 7 ⟨0⟩ ∧
      PlainContract (moduleWorld 7 exampleSeed) after context (58 :: name) name next 8 emptyLiteralObject (.array 2) :=
  source_setup_plain_satisfies 0 exampleSeed context 7 _ _ name next root functionRoot none 1
    (arbitrary_plain_initial_domain name next extra validName)

private def readySeed : Runtime := {exampleSeed with cells := [⟨.mutable, some (.function 6)⟩]}
private theorem ready_setup : SetupInputs readySeed 7 root functionRoot :=
  ⟨rfl, rfl, by intro closure member; cases member⟩

theorem arbitrary_terminal_initial_domain (name : JSString) (lower upper : UInt16) (next : Option JSString) (extra : List Value)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (terminal : PatternCacheTerminal.TerminalNext next) :
    InitialTerminalInputs readySeed context 7 (.string (LabelMatch.safeRangeLabel name lower upper) :: PatternCache.nextValue next :: extra)
      name lower upper next root functionRoot none 1 6 ⟨2⟩ regexpRoot := by
  refine ⟨ready_setup, explicit_arguments _ next extra, seed_realm, validName, safeLower, safeUpper, ordered, terminal,
    .absent rfl rfl rfl, by decide, Or.inl .absent, Or.inl rfl, ?_, by decide, rfl, rfl⟩
  exact ⟨0, .mutable, 0, .here rfl rfl, by decide, rfl⟩

theorem arbitrary_terminal_source_closure_and_reuse_witness (name : JSString) (lower upper : UInt16) (next : Option JSString) (extra : List Value)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (terminal : PatternCacheTerminal.TerminalNext next) :
    ∃ first second,
      sourceSetup 7 readySeed = some (.ok (⟨0⟩, moduleWorld 7 readySeed)) ∧
      invokeBinding 257 defaultSplitLimit context 2 "getPattern"
        (.string (LabelMatch.safeRangeLabel name lower upper) :: PatternCache.nextValue next :: extra)
        (moduleWorld 7 readySeed) = .returned (.array 2) first ∧
      invokeBinding 257 defaultSplitLimit context 2 "getPattern"
        (.string (LabelMatch.safeRangeLabel name lower upper) :: PatternCache.nextValue next :: extra) first = .returned (.array 2) second ∧
      SetupContract readySeed (moduleWorld 7 readySeed) 7 ⟨0⟩ ∧
      TerminalContract (moduleWorld 7 readySeed) first context name lower upper next 8 emptyLiteralObject 2 (.array 2) ∧
      WarmContract first second context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) 8 (.array 2) (.array 2) :=
  source_setup_terminal_warm_satisfies 0 0 readySeed context 7 _ name lower upper next root functionRoot none 1 6 ⟨2⟩ regexpRoot
    (arbitrary_terminal_initial_domain name lower upper next extra validName safeLower safeUpper ordered terminal)

/-- Observe two actual exported calls on the complete carried runtime. Failure
at setup, value resolution, binding, body execution or return produces none. -/
private def twoCalls (firstArguments secondArguments : List Value) : Option (Value × Value × Option (List Value) × Nat × Nat) :=
  match sourceSetup 7 exampleSeed with
  | some (.ok (_, created)) =>
    match invokeBinding 257 defaultSplitLimit context created.current "getPattern" firstArguments created with
    | .returned first afterFirst =>
      match invokeBinding 257 defaultSplitLimit context created.current "getPattern" secondArguments afterFirst with
      | .returned second afterSecond =>
        some (first, second, afterSecond.data.base.regexp.ambient.heap[2]?, afterSecond.closures.length, afterSecond.current)
      | _ => none
    | _ => none
  | _ => none

theorem source_closure_raw_separator_collision :
    twoCalls [.string (cacheAscii ":a#b"), .string (cacheAscii "c")]
      [.string (cacheAscii ":a"), .string (cacheAscii "b#c")] =
      some (.array 2, .array 2, some (PatternCache.plainValues (cacheAscii ":a#b") (cacheAscii "a#b")), 1, 2) := by
  unfold twoCalls
  rw [source_setup_runtime]
  cbv

theorem source_closure_raw_separator_collision_reverse :
    twoCalls [.string (cacheAscii ":a"), .string (cacheAscii "b#c")]
      [.string (cacheAscii ":a#b"), .string (cacheAscii "c")] =
      some (.array 2, .array 2, some (PatternCache.plainValues (cacheAscii ":a") (cacheAscii "a")), 1, 2) := by
  unfold twoCalls
  rw [source_setup_runtime]
  cbv

/-- Compatibility does not imply key injectivity: two distinct request pairs
have this same raw key. The histories above prove which first tuple survives. -/
theorem raw_cache_key_is_not_injective :
    (cacheAscii ":a#b", some (cacheAscii "c")) ≠ (cacheAscii ":a", some (cacheAscii "b#c")) ∧
    PatternCache.key (cacheAscii ":a#b") (some (cacheAscii "c")) =
      PatternCache.key (cacheAscii ":a") (some (cacheAscii "b#c")) := by decide

theorem source_closure_missing_and_string_undefined_collide :
    twoCalls [.string (cacheAscii ":id")]
      [.string (cacheAscii ":id"), .string (cacheAscii "undefined")] =
      some (.array 2, .array 2, some (PatternCache.plainValues (cacheAscii ":id") (cacheAscii "id")), 1, 2) := by
  unfold twoCalls
  rw [source_setup_runtime]
  cbv

private def isOutside : Outcome → Bool | .outsideModel _ => true | _ => false

/-- Source creation retains a reference to a TDZ global cell. Initializing that
same cell AFTER creation enables a cold terminal call; poisoning it AFTER the
first call leaves warm reuse successful and makes a different cold key outside
the admitted constructor model. No state after that error is asserted. -/
private def changedConstructorHistory : Option (Value × Value × Option (List Value) × Option (Option Nat) × Option Value × Bool) :=
  match sourceSetup 7 exampleSeed with
  | some (.ok (_, created)) =>
    match initializeCell created 0 (.function 6) with
    | .ok ready =>
      match invokeBinding 257 defaultSplitLimit context created.current "getPattern" [.string (cacheAscii ":id{[0-9]+}")] ready with
      | .returned first afterFirst =>
        match setBindingValue (afterFirst.environments.length + 1) afterFirst created.current "RegExp" (.number 17) with
        | .ok poisoned =>
          match invokeBinding 257 defaultSplitLimit context created.current "getPattern" [.string (cacheAscii ":id{[0-9]+}")] poisoned with
          | .returned second afterSecond =>
            some (first, second, afterSecond.data.base.regexp.ambient.heap[2]?,
              (afterSecond.data.base.regexp.ambient.objects[11]?).map OrdinaryObject.prototype,
              (afterSecond.cells[0]?).bind Cell.value,
              isOutside (invokeBinding 257 defaultSplitLimit context created.current "getPattern" [.string (cacheAscii ":other{[0-9]+}")] afterSecond))
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

theorem source_closure_reads_current_constructor_and_warm_skips_poison :
    changedConstructorHistory = some (.array 2, .array 2,
      some [.string (cacheAscii ":id{[0-9]+}"), .string (cacheAscii "id"), .object 11],
      some (some 2), some (.number 17), true) := by
  unfold changedConstructorHistory
  rw [source_setup_runtime]
  cbv

theorem exact_combined_source_retains_both_programs :
    (parseSetup pinnedSetup).map (fun parsed =>
      (parsed.initializer.name, parsed.arrow.name, parsed.arrow.parameters.map (·.name), parsed.arrow.body)) =
      some ("patternCache", "getPattern", ["label", "next"], GetPatternBody.program) := by
  rw [parses_setup]
  rfl

/-- A source fragment without its initializer cannot manufacture the cache
binding needed by the real declaration. Appending an unparsed statement is also
rejected instead of silently dropping source. -/
theorem setup_requires_initializer_and_whole_declaration :
    (parseSetup pinnedDeclaration).isNone = true ∧
    (parseSetup "const cache: { [key: string]: Pattern } = {}\nexport const f = (): Pattern | null => {return null}\nhidden()\n").isNone = true := by
  cbv <;> repeat' constructor

theorem any_typed_arguments_and_extra_values_are_admitted (input : JSString) (next : Option JSString) (extra : List Value) :
    Arguments (.string input :: PatternCache.nextValue next :: extra) input next :=
  explicit_arguments input next extra

theorem missing_next_has_undefined_value (input : JSString) :
    Arguments [.string input] input none ∧ argument [.string input] 1 = .undefined :=
  ⟨omitted_next input, rfl⟩

theorem erased_optional_parameter_still_counts_for_length :
    GetPatternBody.declaration.parameters.length = 2 := rfl

/-- info: 'HonoLean.Upstream.GetPatternInvocation.parses_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parses_setup

/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_refines
/-- info: 'HonoLean.Upstream.GetPatternInvocation.invoke_wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_wildcard_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.invoke_miss_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_miss_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.invoke_plain_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_plain_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.invoke_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_warm_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.invoke_terminal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_terminal_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_wildcard_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_miss_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_miss_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_plain_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_plain_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_terminal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_terminal_satisfies
/-- info: 'HonoLean.Upstream.GetPatternInvocation.source_setup_terminal_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_setup_terminal_warm_satisfies

end HonoLean.Upstream.GetPatternInvocation.Checks
