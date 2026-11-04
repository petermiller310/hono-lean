import HonoLean.Upstream.PatternCacheTerminal.Activation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.PatternCacheTerminal.Checks
open SourceSubset hiding pinnedSource
open ECMA2025 PatternCache

private def context : PatternCacheContext := ⟨labelStandardContext⟩
private def prototypeObject : OrdinaryObject := ⟨standardLabelRegExpOwn 9 5, some 0, true⟩
private def before50 (name : JSString) (lower upper : UInt16) (next : Option JSString) : LabelMatchState :=
  let before := labelStandardState (LabelMatch.safeRangeLabel name lower upper)
  cacheWithAmbient before {before.base.regexp.ambient with environment :=
    ("next", nextValue next) :: ("RegExp", .function 6) :: before.base.regexp.ambient.environment}
private def freshBefore (name : JSString) (lower upper : UInt16) (next : Option JSString) : LabelMatchState :=
  initializedPatternCacheState initProgram (before50 name lower upper next)
private def afterTerminal (name : JSString) (lower upper : UInt16) (next : Option JSString) : LabelMatchState :=
  resultState (freshBefore name lower upper next) context name lower upper next 7 emptyLiteralObject 2

private theorem before_realm (name : JSString) (lower upper : UInt16) (next : Option JSString) :
    LabelRealm (before50 name lower upper next) labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [before50, cacheWithAmbient, labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < 7
  decide

private theorem init_inputs (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    InitInputs (before50 name lower upper next) context name lower upper next (objectPrototypeProjection []) none 1 6 ⟨2⟩ prototypeObject := by
  exact ⟨⟨before_realm name lower upper next, rfl⟩, validName, safeLower, safeUpper, ordered, terminal,
    rfl, rfl, .absent rfl rfl rfl, (by decide), Or.inl .absent, Or.inl rfl, rfl, (by decide), rfl, rfl⟩
private theorem terminal_inputs (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    Inputs (freshBefore name lower upper next) context name lower upper next 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject :=
  initialized_inputs _ context name lower upper next _ none 1 6 ⟨2⟩ prototypeObject
    (init_inputs name lower upper next validName safeLower safeUpper ordered terminal)

/-- Inhabited initial domain: arbitrary valid rawUTF16 names and ordered safe
endpoints, all terminal next cases, actual source50 cache and current ctor6.
No supplied match array, compiled record, successful Set or future Get. -/
theorem arbitrary_terminal_domain_is_inhabited (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    Inputs (freshBefore name lower upper next) context name lower upper next 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject :=
  terminal_inputs name lower upper next validName safeLower safeUpper ordered terminal

private def Witness (name : JSString) (lower upper : UInt16) (next : Option JSString) : Prop :=
  sourceCall 256 context (freshBefore name lower upper next) = some (.ok (.array 2, afterTerminal name lower upper next)) ∧
  Contract (freshBefore name lower upper next) (afterTerminal name lower upper next) context name lower upper next 7 emptyLiteralObject 2 (.array 2)

/-- Actual533B cold source consumes its own source60 captures, constructs68,
strictly stores and rereads74; the independent contract specifies every layer. -/
theorem arbitrary_full_source_terminal_contract (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    Witness name lower upper next :=
  source_terminal_satisfies 0 _ context name lower upper next 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject
    (terminal_inputs name lower upper next validName safeLower safeUpper ordered terminal)

/-- Suffix is arbitrary UTF16, not a selected ASCII fixture. The actual next
condition admits absent, empty, colon-prefixed and star-prefixed values. -/
theorem all_four_next_variants_have_source_contracts (name suffix : JSString) (lower upper : UInt16)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    Witness name lower upper none ∧ Witness name lower upper (some []) ∧
    Witness name lower upper (some (58 :: suffix)) ∧ Witness name lower upper (some (42 :: suffix)) := by
  exact ⟨arbitrary_full_source_terminal_contract name lower upper none validName safeLower safeUpper ordered (Or.inl rfl),
    arbitrary_full_source_terminal_contract name lower upper (some []) validName safeLower safeUpper ordered (Or.inr (Or.inl rfl)),
    arbitrary_full_source_terminal_contract name lower upper (some (58 :: suffix)) validName safeLower safeUpper ordered (Or.inr (Or.inr (Or.inl ⟨suffix, rfl⟩))),
    arbitrary_full_source_terminal_contract name lower upper (some (42 :: suffix)) validName safeLower safeUpper ordered (Or.inr (Or.inr (Or.inr ⟨suffix, rfl⟩)))⟩

/-- Actual52B source50 initializes the SAME cache used by actual533B. Module
closure creation/caller activation remains a separate interpretation boundary. -/
theorem actual50_initialization_then_terminal_contract (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    sourceInit 2 context (before50 name lower upper next) = some (.ok (freshBefore name lower upper next)) ∧
    Witness name lower upper next := by
  have result := source_init_then_terminal_satisfies 0 0 _ context name lower upper next _ none 1 6 ⟨2⟩ prototypeObject
    (init_inputs name lower upper next validName safeLower safeUpper ordered terminal)
  exact ⟨result.1, result.2.1, result.2.2.2⟩

/-- Three source activations, one persistent state/cache. The second call
recomputes its capture array then reuses the first tuple and initialized regex. -/
theorem actual50_then_terminal_then_warm_same_heap (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (validName : LabelRegExp.Name name) (safeLower : RangeRegExp.SafeEndpoint lower)
    (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) (terminal : TerminalNext next) :
    sourceInit 2 context (before50 name lower upper next) = some (.ok (freshBefore name lower upper next)) ∧
    sourceCall 256 context (freshBefore name lower upper next) = some (.ok (.array 2, afterTerminal name lower upper next)) ∧
    sourceCall 256 context (afterTerminal name lower upper next) =
      some (.ok (.array 2, warmState (afterTerminal name lower upper next) context (LabelMatch.safeRangeLabel name lower upper))) ∧
    InitContract (before50 name lower upper next) (freshBefore name lower upper next) ∧
    Contract (freshBefore name lower upper next) (afterTerminal name lower upper next) context name lower upper next 7 emptyLiteralObject 2 (.array 2) ∧
    WarmContract (afterTerminal name lower upper next)
      (warmState (afterTerminal name lower upper next) context (LabelMatch.safeRangeLabel name lower upper)) context
      (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) 7 (.array 2) (.array 2) := by
  exact source_init_then_terminal_then_warm_satisfies 0 0 0 _ context name lower upper next _ none 1 6 ⟨2⟩ prototypeObject
    (init_inputs name lower upper next validName safeLower safeUpper ordered terminal)

/-- Explicit descriptor/prototype fixture variants below are not claimed to
be produced by source50 without subsequent ordinary caller mutation. -/
private def variant (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (object : OrdinaryObject) (extra : ObjectHeap := []) : LabelMatchState :=
  let before := freshBefore name lower upper next
  cacheWithAmbient before {before.base.regexp.ambient with objects := (labelStandardAmbient (LabelMatch.safeRangeLabel name lower upper)).objects ++ object :: extra}
private theorem variant_realm (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (object : OrdinaryObject) (extra : ObjectHeap) : LabelRealm (variant name lower upper next object extra) labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [variant, freshBefore, before50, initializedPatternCacheState, cacheWithAmbient,
    labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < ((labelStandardAmbient (LabelMatch.safeRangeLabel name lower upper)).objects ++ object :: extra).length
  simp only [List.length_append, List.length_cons]
  change 2 < 7 + (extra.length + 1)
  omega

private def idName : JSString := [105,100]
private def input : JSString := LabelMatch.safeRangeLabel idName 48 57
private theorem id_valid : LabelRegExp.Name idName := by simp [LabelRegExp.Name, idName]
private theorem digit_safe_lower : RangeRegExp.SafeEndpoint 48 := by decide
private theorem digit_safe_upper : RangeRegExp.SafeEndpoint 57 := by decide
private theorem digit_ordered : (48 : UInt16).toNat ≤ (57 : UInt16).toNat := by decide
private def inheritedObject : OrdinaryObject := ⟨[], some 8, true⟩
private def inheritedHolder : OrdinaryObject := ⟨[(key input none, .data (.number 0) true false false)], some 0, false⟩

/-- Inherited writable DATA is a real initial descriptor path. The cache has
no own slot; strict ordinary Set creates one without changing the holder. -/
theorem inherited_writable_data_terminal_domain_is_inhabited :
    Inputs (variant idName 48 57 none inheritedObject [inheritedHolder]) context idName 48 57 none 7 inheritedObject
      (some (.data (.number 0) true false false)) 2 6 ⟨2⟩ prototypeObject := by
  refine ⟨⟨⟨variant_realm _ _ _ _ _ _, rfl⟩,
    LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper, rfl, rfl, rfl,
    .parent rfl rfl rfl (.own rfl ?_), (by decide)⟩,
    Or.inl rfl, id_valid, digit_safe_lower, digit_safe_upper, digit_ordered,
    Or.inr ⟨.number 0, true, false, false, rfl, rfl⟩,
    ⟨Or.inr ⟨.number 0, false, false, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, rfl, (by decide), rfl, rfl⟩
  simp [inheritedHolder, input]

theorem inherited_writable_data_full_source_contract :
    sourceCall 256 context (variant idName 48 57 none inheritedObject [inheritedHolder]) =
      some (.ok (.array 2, resultState (variant idName 48 57 none inheritedObject [inheritedHolder]) context idName 48 57 none 7 inheritedObject 2)) ∧
    Contract (variant idName 48 57 none inheritedObject [inheritedHolder])
      (resultState (variant idName 48 57 none inheritedObject [inheritedHolder]) context idName 48 57 none 7 inheritedObject 2)
      context idName 48 57 none 7 inheritedObject 2 (.array 2) :=
  source_terminal_satisfies 0 _ context idName 48 57 none 7 inheritedObject _ 2 6 ⟨2⟩ prototypeObject inherited_writable_data_terminal_domain_is_inhabited

private def ownObject : OrdinaryObject := ⟨[(key input none, .data (.boolean false) true false false)], some 0, false⟩
private theorem own_inputs :
    Inputs (variant idName 48 57 none ownObject) context idName 48 57 none 7 ownObject
      (some (.data (.boolean false) true false false)) 1 6 ⟨2⟩ prototypeObject := by
  have own : ownObject.own.lookup (key input none) = some (.data (.boolean false) true false false) := by simp [ownObject]
  exact ⟨⟨⟨variant_realm _ _ _ _ _ [], rfl⟩,
    LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper, rfl, rfl, rfl, .own rfl own, (by decide)⟩,
    Or.inl rfl, id_valid, digit_safe_lower, digit_safe_upper, digit_ordered,
    Or.inr ⟨.boolean false, true, false, false, rfl, rfl⟩,
    ⟨Or.inr ⟨.boolean false, false, false, rfl⟩, Or.inr ⟨.boolean false, false, false, own⟩⟩, rfl, (by decide), rfl, rfl⟩

/-- Nonextensible is not readonly: an existing writable own slot succeeds,
retaining its false enumerable/configurable flags and actual cache identity. -/
theorem own_writable_nonextensible_full_source_contract :
    sourceCall 256 context (variant idName 48 57 none ownObject) =
      some (.ok (.array 2, resultState (variant idName 48 57 none ownObject) context idName 48 57 none 7 ownObject 2)) ∧
    Contract (variant idName 48 57 none ownObject) (resultState (variant idName 48 57 none ownObject) context idName 48 57 none 7 ownObject 2)
      context idName 48 57 none 7 ownObject 2 (.array 2) :=
  source_terminal_satisfies 0 _ context idName 48 57 none 7 ownObject _ 1 6 ⟨2⟩ prototypeObject own_inputs

theorem own_writable_slot_preserves_flags_and_caller_bindings :
    (resultState (variant idName 48 57 none ownObject) context idName 48 57 none 7 ownObject 2).base.regexp.ambient.objects[7]?.bind
      (fun object => object.own.lookup (key input none)) = some (.data (.array 2) true false false) ∧
    (resultState (variant idName 48 57 none ownObject) context idName 48 57 none 7 ownObject 2).base.regexp.ambient.environment =
      (variant idName 48 57 none ownObject).base.regexp.ambient.environment := by
  constructor
  · cbv <;> repeat' constructor
  · exact (terminal_contract _ context idName 48 57 none 7 ownObject _ 1 6 ⟨2⟩ prototypeObject own_inputs).frames.environment

/-- Old array0, caller object5 and private context are protected while the
cache object itself changes and its aliases observe the stored tuple. -/
theorem terminal_contract_protects_old_arrays_objects_and_private_context :
    (afterTerminal idName 48 57 none).base.regexp.ambient.heap[0]? = (freshBefore idName 48 57 none).base.regexp.ambient.heap[0]? ∧
    (afterTerminal idName 48 57 none).base.regexp.ambient.objects[5]? = (freshBefore idName 48 57 none).base.regexp.ambient.objects[5]? ∧
    (afterTerminal idName 48 57 none).base.regexp.ambient.privates = (freshBefore idName 48 57 none).base.regexp.ambient.privates := by
  have contract := (arbitrary_full_source_terminal_contract idName 48 57 none id_valid digit_safe_lower digit_safe_upper digit_ordered (Or.inl rfl)).2
  exact ⟨contract.oldArrays 0 (by change 0 < 1; decide),
    contract.otherObjects 5 (by decide) (by change 5 < 8; decide), contract.frames.privates⟩

/-- A non-ASCII/LT/lone-surrogate name reaches the same initialized digit
matcher. Name UTF16 has no accidental ASCII or line-terminator restriction. -/
theorem raw_utf16_name_terminal_source_domain_and_contract :
    Witness [0,55296,10,233] 48 57 none :=
  arbitrary_full_source_terminal_contract _ 48 57 none
    (by simp [LabelRegExp.Name]) digit_safe_lower digit_safe_upper digit_ordered (Or.inl rfl)

private def selectedCall (before : LabelMatchState) : Except PatternCacheError (Value × LabelMatchState) :=
  (sourceCall 256 context before).getD (.error .exhausted)
private def selectedInit (before : LabelMatchState) : Except PatternCacheError LabelMatchState :=
  (sourceInit 2 context before).getD (.error .exhausted)
private def terminalHistory := do
  let initialized ← selectedInit (before50 idName 48 57 none)
  let withOldAlias := cacheWithAmbient initialized {initialized.base.regexp.ambient with environment :=
    ("cacheAlias", .object 7) :: initialized.base.regexp.ambient.environment}
  let (first, middle) ← selectedCall withOldAlias
  let aliased := cacheWithAmbient middle {middle.base.regexp.ambient with environment :=
    ("tupleAlias", first) :: ("RegExp", .number 17) :: middle.base.regexp.ambient.environment}
  let (second, after) ← selectedCall aliased
  pure (first, second, after.base.regexp.ambient.environment.lookup "cacheAlias",
    after.base.regexp.ambient.environment.lookup "tupleAlias", after.base.regexp.ambient.heap.length,
    after.base.regexp.brands.lookup 9)

/-- A caller cache alias exists BEFORE the real terminal store. Then a warm
call tolerates current constructor replacement without reading NewExpression;
the old cache alias and returned-tuple alias both retain the actual identities. -/
theorem terminal_then_warm_reuses_first_tuple_despite_invalid_current_constructor :
    terminalHistory = .ok (.array 2, .array 2, some (.object 7), some (.array 2), 4, some digitsRecord) := by
  let fresh := freshBefore idName 48 57 none
  let firstBefore := callerEnvironment fresh (("cacheAlias", .object 7) :: fresh.base.regexp.ambient.environment)
  have firstInputs : Inputs firstBefore context idName 48 57 none 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject := by
    exact inputs_caller_environment fresh context idName 48 57 none 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject
      (terminal_inputs idName 48 57 none id_valid digit_safe_lower digit_safe_upper digit_ordered (Or.inl rfl))
      (("cacheAlias", .object 7) :: fresh.base.regexp.ambient.environment) rfl rfl rfl rfl
  let middle := resultState firstBefore context idName 48 57 none 7 emptyLiteralObject 2
  have firstFacts := source_terminal_satisfies 0 firstBefore context idName 48 57 none 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject firstInputs
  change sourceCall 256 context firstBefore = some (.ok (.array 2, middle)) ∧
    Contract firstBefore middle context idName 48 57 none 7 emptyLiteralObject 2 (.array 2) at firstFacts
  obtain ⟨updated, enumerable, configurable, ready⟩ := result_warm_inputs firstBefore context idName 48 57 none 7 emptyLiteralObject none 2 6 ⟨2⟩ prototypeObject firstInputs (by decide) (by decide)
  change WarmInputs middle context input idName (some (PatternConstruct.rawBody 48 57)) none 7 updated (.array 2) true enumerable configurable 1 at ready
  let secondEnvironment := ("tupleAlias", Value.array 2) :: ("RegExp", Value.number 17) :: middle.base.regexp.ambient.environment
  let secondBefore := callerEnvironment middle secondEnvironment
  have secondLabel : secondEnvironment.lookup "label" = some (.string input) := by
    change List.lookup "label" (("tupleAlias", _) :: ("RegExp", _) :: middle.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using ready.source.labelBinding
  have secondNext : secondEnvironment.lookup "next" = some (nextValue none) := by
    change List.lookup "next" (("tupleAlias", _) :: ("RegExp", _) :: middle.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using ready.nextBinding
  have secondCache : secondEnvironment.lookup "patternCache" = some (.object 7) := by
    change List.lookup "patternCache" (("tupleAlias", _) :: ("RegExp", _) :: middle.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using ready.cacheBinding
  have secondInputs := warm_caller_environment middle context input idName (some (PatternConstruct.rawBody 48 57)) none 7 updated (.array 2) true enumerable configurable 1 ready
    secondEnvironment secondLabel secondNext secondCache
  have secondFacts := source_warm_satisfies 0 secondBefore context input idName (some (PatternConstruct.rawBody 48 57)) none 7 updated (.array 2) true enumerable configurable 1 secondInputs
  let after := warmState secondBefore context input
  change sourceCall 256 context secondBefore = some (.ok (.array 2, after)) ∧
    WarmContract secondBefore after context input idName (some (PatternConstruct.rawBody 48 57)) 7 (.array 2) (.array 2) at secondFacts
  have finalCacheAlias : after.base.regexp.ambient.environment.lookup "cacheAlias" = some (.object 7) := by
    rw [secondFacts.2.frames.environment]
    change List.lookup "cacheAlias" secondEnvironment = _
    dsimp only [secondEnvironment]
    rw [firstFacts.2.frames.environment]
    rfl
  have finalTupleAlias : after.base.regexp.ambient.environment.lookup "tupleAlias" = some (.array 2) := by
    rw [secondFacts.2.frames.environment]
    rfl
  have finalLength : after.base.regexp.ambient.heap.length = 4 := by
    rw [secondFacts.2.captures]
    change (middle.base.regexp.ambient.heap ++ [LabelMatch.captures input idName (some (PatternConstruct.rawBody 48 57))]).length = 4
    rw [firstFacts.2.arrays]
    rfl
  have finalBrand : after.base.regexp.brands.lookup 9 = some digitsRecord := by
    rw [secondFacts.2.frames.rangeBrands]
    change middle.base.regexp.brands.lookup 9 = _
    rw [firstFacts.2.frames.rangeBrands]
    rfl
  have initRun : selectedInit (before50 idName 48 57 none) = .ok fresh := by
    unfold selectedInit
    rw [(source_init_satisfies 0 (before50 idName 48 57 none) context (objectPrototypeProjection []) rfl).1]
    rfl
  have firstRun : selectedCall firstBefore = .ok (.array 2, middle) := by
    unfold selectedCall
    rw [firstFacts.1]
    rfl
  have secondRun : selectedCall secondBefore = .ok (.array 2, after) := by
    unfold selectedCall
    rw [secondFacts.1]
    rfl
  have actualFirstRun : selectedCall (cacheWithAmbient fresh {fresh.base.regexp.ambient with environment :=
      ("cacheAlias", .object 7) :: fresh.base.regexp.ambient.environment}) = .ok (.array 2, middle) := firstRun
  have actualSecondRun : selectedCall (cacheWithAmbient middle {middle.base.regexp.ambient with environment :=
      ("tupleAlias", .array 2) :: ("RegExp", .number 17) :: middle.base.regexp.ambient.environment}) = .ok (.array 2, after) := secondRun
  unfold terminalHistory
  rw [initRun]
  simp only [bind]
  rw [Except.bind.eq_def]
  dsimp only []
  rw [actualFirstRun]
  rw [Except.bind.eq_def]
  dsimp only []
  rw [actualSecondRun]
  simp only [Except.bind, pure, Except.pure, finalCacheAlias, finalTupleAlias, finalLength, finalBrand]

private theorem selectedCall_after_match_error (before : LabelMatchState) (label name : JSString) (body : Option JSString)
    (error : PatternCacheError) (source : LabelMatch.Inputs before context.label label)
    (valid : LabelRegExp.Label label name body)
    (failed : executePatternCache 255 defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
      (matchedSnapshot before context label name body) = .error error) :
    selectedCall before = .error error := by
  have execution := execute_source_prefix 0 before context label source
  rewrite [matched_snapshot before context label name body valid] at execution
  have complete := execution.trans failed
  unfold selectedCall
  rewrite [sourceCall, parses_source]
  change runPatternCache 256 defaultSplitLimit context program before = .error error
  unfold runPatternCache
  rewrite [complete]
  rfl

private theorem project_failure (result : Except PatternCacheError (Value × LabelMatchState))
    (error : PatternCacheError) (failed : result = .error error) :
    result.map Prod.fst = .error error := by
  cases failed
  rfl

private theorem readonly_tail :
    executePatternCache 255 defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
      (matchedSnapshot (variant idName 48 57 none ⟨[(key input none, .data (.number 0) false true true)], some 0, true⟩)
        context input idName (some (PatternConstruct.rawBody 48 57))) = .error (.evaluation (.objectError .notWritable)) := by
  cbv <;> repeat' constructor

private theorem nonextensible_tail :
    executePatternCache 255 defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
      (matchedSnapshot (variant idName 48 57 none {emptyLiteralObject with extensible := false})
        context input idName (some (PatternConstruct.rawBody 48 57))) = .error (.evaluation (.objectError .notExtensible)) := by
  cbv <;> repeat' constructor

private theorem invalid_constructor_tail :
    executePatternCache 255 defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
      (matchedSnapshot (cacheWithAmbient (freshBefore idName 48 57 none)
        {(freshBefore idName 48 57 none).base.regexp.ambient with environment :=
          ("RegExp", .number 17) :: (freshBefore idName 48 57 none).base.regexp.ambient.environment})
        context input idName (some (PatternConstruct.rawBody 48 57))) = .error (.constructor .constructorDomain) := by
  cbv <;> repeat' constructor

private theorem lookahead_tail :
    executePatternCache 255 defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
      (matchedSnapshot (freshBefore idName 48 57 (some (cacheAscii "tail")))
        context input idName (some (PatternConstruct.rawBody 48 57))) = .error (.constructor .grammarDomain) := by
  cbv <;> repeat' constructor

/-- Error-only boundaries outside Inputs: strict Set rejects readonly DATA or
nonextensible missing slots; the model makes no failure-state/rollback claim. -/
theorem strict_data_rejection_controls :
    (selectedCall (variant idName 48 57 none ⟨[(key input none, .data (.number 0) false true true)], some 0, true⟩)).map Prod.fst =
      .error (.evaluation (.objectError .notWritable)) ∧
    (selectedCall (variant idName 48 57 none {emptyLiteralObject with extensible := false})).map Prod.fst =
      .error (.evaluation (.objectError .notExtensible)) := by
  constructor
  · have failed := selectedCall_after_match_error
      (variant idName 48 57 none ⟨[(key input none, .data (.number 0) false true true)], some 0, true⟩)
      input idName (some (PatternConstruct.rawBody 48 57)) (.evaluation (.objectError .notWritable))
      ⟨variant_realm _ _ _ _ _ [], rfl⟩
      (LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper) readonly_tail
    exact project_failure _ _ failed
  · have failed := selectedCall_after_match_error
      (variant idName 48 57 none {emptyLiteralObject with extensible := false})
      input idName (some (PatternConstruct.rawBody 48 57)) (.evaluation (.objectError .notExtensible))
      ⟨variant_realm _ _ _ _ _ [], rfl⟩
      (LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper) nonextensible_tail
    exact project_failure _ _ failed

/-- Current-constructor replacement and reached lookahead are explicit model
refusals, not a proof that arbitrary native constructors/lookaheads throw. -/
theorem invalid_constructor_and_reached_lookahead_controls :
    (selectedCall (cacheWithAmbient (freshBefore idName 48 57 none)
      {(freshBefore idName 48 57 none).base.regexp.ambient with environment :=
        ("RegExp", .number 17) :: (freshBefore idName 48 57 none).base.regexp.ambient.environment})).map Prod.fst =
      .error (.constructor .constructorDomain) ∧
    (selectedCall (freshBefore idName 48 57 (some (cacheAscii "tail")))).map Prod.fst =
      .error (.constructor .grammarDomain) := by
  constructor
  · let before := cacheWithAmbient (freshBefore idName 48 57 none)
      {(freshBefore idName 48 57 none).base.regexp.ambient with environment :=
        ("RegExp", .number 17) :: (freshBefore idName 48 57 none).base.regexp.ambient.environment}
    have source : LabelMatch.Inputs before context.label input := by
      exact ⟨realm_caller_environment (freshBefore idName 48 57 none) context.label _
        (terminal_inputs idName 48 57 none id_valid digit_safe_lower digit_safe_upper digit_ordered (Or.inl rfl)).source.toLabelRealm, rfl⟩
    have failed := selectedCall_after_match_error before input idName (some (PatternConstruct.rawBody 48 57)) (.constructor .constructorDomain)
      source (LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper) invalid_constructor_tail
    exact project_failure _ _ failed
  · have source : LabelMatch.Inputs (freshBefore idName 48 57 (some (cacheAscii "tail"))) context.label input :=
      initialized_label_inputs _ context input ⟨before_realm _ _ _ _, rfl⟩
    have failed := selectedCall_after_match_error (freshBefore idName 48 57 (some (cacheAscii "tail"))) input idName
      (some (PatternConstruct.rawBody 48 57)) (.constructor .grammarDomain) source
      (LabelMatch.safe_range_label idName 48 57 id_valid digit_safe_lower digit_safe_upper) lookahead_tail
    exact project_failure _ _ failed

/-- These are the existing actual533B post-wildcard bytes. The omitted earlier
wildcard guard, cold67 regex semantics and native/full-function adequacy stay open. -/
theorem selected_source_identity_and_terminal_domain_boundaries :
    parsePatternCacheBody pinnedSource bindings = some program ∧
    ¬ TerminalNext (some [116,97,105,108]) := by
  constructor
  · exact parses_source
  · simp [TerminalNext]

/-- info: 'HonoLean.Upstream.PatternCacheTerminal.source_terminal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_terminal_satisfies
/-- info: 'HonoLean.Upstream.PatternCacheTerminal.source_init_then_terminal_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_init_then_terminal_satisfies
/-- info: 'HonoLean.Upstream.PatternCacheTerminal.source_init_then_terminal_then_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_init_then_terminal_then_warm_satisfies
/-- info: 'HonoLean.Upstream.PatternCacheTerminal.eval_next_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_next_condition
/-- info: 'HonoLean.Upstream.PatternCacheTerminal.eval_terminal_tuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_terminal_tuple

end HonoLean.Upstream.PatternCacheTerminal.Checks
