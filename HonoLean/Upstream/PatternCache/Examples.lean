import HonoLean.Upstream.PatternCache.Composition

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.PatternCache.Checks
open SourceSubset ECMA2025

private def context : PatternCacheContext := ⟨labelStandardContext⟩
private def before50 (input : JSString) (next : Option JSString) : LabelMatchState :=
  let before := labelStandardState input
  cacheWithAmbient before {before.base.regexp.ambient with environment :=
    ("next", nextValue next) :: before.base.regexp.ambient.environment}
private def freshBefore (input : JSString) (next : Option JSString) : LabelMatchState :=
  initializedPatternCacheState initProgram (before50 input next)

/-- Ordinary DATA/prototype variants are explicit initial fixture inputs.
They are not claimed to be assignments performed by Hono's source50 initializer. -/
private def fixture (input : JSString) (next : Option JSString) (object : OrdinaryObject) (extra : ObjectHeap := []) : LabelMatchState :=
  let before := freshBefore input next
  cacheWithAmbient before {before.base.regexp.ambient with objects := (labelStandardAmbient input).objects ++ object :: extra}
private def dataObject (input : JSString) (next : Option JSString) (value : Value)
    (writable : Bool := false) (extensible : Bool := false) : OrdinaryObject :=
  ⟨[(key input next, .data value writable false false)], some 0, extensible⟩

private theorem fixture_realm (input : JSString) (next : Option JSString) (object : OrdinaryObject) (extra : ObjectHeap) :
    LabelRealm (fixture input next object extra) labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [fixture, freshBefore, before50, initializedPatternCacheState, cacheWithAmbient,
    labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < ((labelStandardAmbient input).objects ++ object :: extra).length
  simp only [List.length_append, List.length_cons]
  change 2 < 7 + (extra.length + 1)
  omega

private theorem fixture_inputs (input : JSString) (next : Option JSString) (object : OrdinaryObject) (extra : ObjectHeap) :
    LabelMatch.Inputs (fixture input next object extra) labelStandardContext input := ⟨fixture_realm input next object extra, rfl⟩

private theorem standard_realm (input : JSString) : LabelRealm (labelStandardState input) labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < 7
  decide

/-- Actual50 creates an allocated ordinary{} with the intrinsic ordinary
prototype. The function closure/module bootstrap remains an explicit boundary. -/
theorem actual_source50_allocates_the_persistent_cache (input : JSString) (next : Option JSString) :
    sourceInit 8 context (before50 input next) = some (.ok (freshBefore input next)) := by
  rw [sourceInit, parses_init]
  exact congrArg some (initializePatternCache_empty 6 defaultSplitLimit context initProgram (before50 input next)
    (objectPrototypeProjection []) rfl rfl)

private def blockOnly (input : JSString) (next : Option JSString) : LabelMatchState :=
  {base := {regexp := {ambient := {
    environment := [("label", .string input), ("next", nextValue next), ("patternCache", .object 0)]
    objects := [⟨[(key input next, .data (.boolean true) false false false)], none, false⟩]}}}}

/-- Whole440B warm entry needs neither match nor RegExp nor a producer realm.
Its initial truthy DATA skips every retained cold branch and returns unchanged. -/
theorem warm_block_needs_no_match_or_constructor_binding (input : JSString) (next : Option JSString) :
    sourceBlock 16 context (blockOnly input next) = some (.ok (.boolean true, blockOnly input next)) := by
  apply source_block_warm_satisfies 0 (blockOnly input next) context input next 0 _ (.boolean true) false false false 1
  refine ⟨rfl, rfl, rfl, rfl, .own rfl ?_, (by decide), rfl⟩
  simp

private theorem warm_inputs (input name : JSString) (body : Option JSString) (next : Option JSString) (value : Value)
    (valid : LabelRegExp.Label input name body) (truthy : SourceSubset.truthy value = true) :
    WarmInputs (fixture input next (dataObject input next value)) context input name body next 7
      (dataObject input next value) value false false false 1 := by
  refine ⟨⟨fixture_inputs input next _ [], valid, rfl, rfl, rfl, .own rfl ?_, (by decide)⟩, truthy⟩
  simp [dataObject]

/-- Inhabited full-source domain for arbitrary UTF16 labels/captures and any
truthy DATA value. No cold constructor/formatted tuple is a premise. -/
theorem arbitrary_warm_domain_is_inhabited (input name : JSString) (body : Option JSString) (next : Option JSString)
    (value : Value) (valid : LabelRegExp.Label input name body) (truthy : SourceSubset.truthy value = true) :
    WarmInputs (fixture input next (dataObject input next value)) context input name body next 7
      (dataObject input next value) value false false false 1 := warm_inputs input name body next value valid truthy

theorem arbitrary_truthy_data_full_source_contract (input name : JSString) (body : Option JSString) (next : Option JSString)
    (value : Value) (valid : LabelRegExp.Label input name body) (truthy : SourceSubset.truthy value = true) :
    sourceCall 256 context (fixture input next (dataObject input next value)) =
      some (.ok (value, warmState (fixture input next (dataObject input next value)) context input)) ∧
    WarmContract (fixture input next (dataObject input next value))
      (warmState (fixture input next (dataObject input next value)) context input) context input name body 7 value value :=
  source_warm_satisfies 0 _ context input name body next 7 _ value false false false 1
    (warm_inputs input name body next value valid truthy)

private def inheritedCache : OrdinaryObject := ⟨[], some 8, false⟩
private def inheritedHolder (input : JSString) (next : Option JSString) : OrdinaryObject :=
  ⟨[(key input next, .data (.object 5) false false false)], some 0, false⟩

/-- Initial descriptor traversal reaches an inherited readonly DATA value.
The cache is nonextensible, yet source63/74 only read; no write premise needed. -/
theorem inherited_readonly_nonextensible_warm_domain_and_source :
    sourceCall 256 context (fixture [58,105,100,123,40,125] none inheritedCache [inheritedHolder [58,105,100,123,40,125] none]) =
      some (.ok (.object 5, warmState (fixture [58,105,100,123,40,125] none inheritedCache [inheritedHolder [58,105,100,123,40,125] none]) context [58,105,100,123,40,125])) := by
  apply (source_warm_satisfies 0 _ context _ [105,100] (some [40]) none 7 inheritedCache (.object 5) false false false 2 ?_).1
  refine ⟨⟨fixture_inputs _ _ _ _, (by simp [LabelRegExp.Label, LabelRegExp.Name, LabelRegExp.Body]), rfl, rfl, rfl, .parent rfl rfl rfl (.own rfl ?_), (by decide)⟩, rfl⟩
  simp [inheritedHolder]

private theorem missing_path (name : JSString) (next : Option JSString) :
    NodeCaptureGuard.DescriptorPath (fixture (58 :: name) next emptyLiteralObject).base.regexp.ambient.objects
      (key (58 :: name) next) 7 none 2 := by
  refine .parent rfl rfl rfl (.absent rfl ?_ rfl)
  rfl

private theorem plain_inputs (name : JSString) (next : Option JSString) (validName : LabelRegExp.Name name) :
    PlainInputs (fixture (58 :: name) next emptyLiteralObject) context (58 :: name) name next 7 emptyLiteralObject none 2 := by
  refine ⟨⟨fixture_inputs _ _ _ [], ⟨validName, rfl⟩, rfl, rfl, rfl, missing_path name next, (by decide)⟩,
    Or.inl .absent, ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Plain source60→70 inputs are derived solely from the raw input name and
initial ordinary empty cache. There is no supplied capture array/tuple or Set. -/
theorem arbitrary_plain_domain_is_inhabited (name : JSString) (next : Option JSString) (validName : LabelRegExp.Name name) :
    PlainInputs (fixture (58 :: name) next emptyLiteralObject) context (58 :: name) name next 7 emptyLiteralObject none 2 :=
  plain_inputs name next validName

/-- Minimal miss world lacks both next and cache bindings. -/
theorem noncolon_source_miss_needs_no_next_or_cache (head : UInt16) (tail : JSString) (notColon : head ≠ 58) :
    sourceCall 256 context (labelStandardState (head :: tail)) =
      some (.ok (.null, warmState (labelStandardState (head :: tail)) context (head :: tail))) ∧
    MissContract (labelStandardState (head :: tail)) (warmState (labelStandardState (head :: tail)) context (head :: tail)) context (head :: tail) .null := by
  apply source_miss_satisfies 0 _ context _ ⟨standard_realm _, rfl⟩
  rintro ⟨name, body, valid⟩
  have colon := LabelRegExp.label_input (head :: tail) name body valid
  exact notColon (List.cons.inj colon).1

/-- Arbitrary rawUTF16 nonbrace names start BEFORE the producer; the theorem
computes captures then reserves the tuple and performs the actual ordinary Set. -/
theorem arbitrary_cold_plain_full_source_contract (name : JSString) (next : Option JSString) (validName : LabelRegExp.Name name) :
    sourceCall 256 context (fixture (58 :: name) next emptyLiteralObject) =
      some (.ok (.array 2, plainState (fixture (58 :: name) next emptyLiteralObject) context (58 :: name) name next 7 emptyLiteralObject)) ∧
    PlainContract (fixture (58 :: name) next emptyLiteralObject)
      (plainState (fixture (58 :: name) next emptyLiteralObject) context (58 :: name) name next 7 emptyLiteralObject)
      context (58 :: name) name next 7 emptyLiteralObject (.array 2) :=
  source_plain_satisfies 0 _ context _ name next 7 _ none 2 (plain_inputs name next validName)

private def idInput : JSString := [58,105,100]
private def idName : JSString := [105,100]
private theorem id_valid : LabelRegExp.Name idName := by simp [LabelRegExp.Name, idName]

/-- A nonextensible cache can still update an existing writable DATA entry;
its nonenumerable/nonconfigurable flags are preserved, not normalized to WEC. -/
theorem existing_writable_data_plain_domain_and_source :
    sourceCall 256 context (fixture idInput none (dataObject idInput none (.number 0) true false)) =
      some (.ok (.array 2, plainState (fixture idInput none (dataObject idInput none (.number 0) true false))
        context idInput idName none 7 (dataObject idInput none (.number 0) true false))) ∧
    PlainContract (fixture idInput none (dataObject idInput none (.number 0) true false))
      (plainState (fixture idInput none (dataObject idInput none (.number 0) true false)) context idInput idName none 7 (dataObject idInput none (.number 0) true false))
      context idInput idName none 7 (dataObject idInput none (.number 0) true false) (.array 2) := by
  apply source_plain_satisfies 0 _ context idInput idName none 7 _ (some (.data (.number 0) true false false)) 1
  have own : (dataObject idInput none (.number 0) true false).own.lookup (key idInput none) = some (.data (.number 0) true false false) := by
    simp [dataObject]
  refine ⟨⟨fixture_inputs _ _ _ [], ⟨id_valid, rfl⟩, rfl, rfl, rfl, .own rfl own, (by decide)⟩,
    Or.inr ⟨.number 0, true, false, false, rfl, rfl⟩,
    ⟨Or.inr ⟨.number 0, false, false, rfl⟩, Or.inr ⟨.number 0, false, false, own⟩⟩⟩

private def activate (input : JSString) (next : Option JSString) (before : LabelMatchState) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with environment :=
    ("label", .string input) :: ("next", nextValue next) :: before.base.regexp.ambient.environment}
private def selectedCall (before : LabelMatchState) : Except PatternCacheError (Value × LabelMatchState) :=
  (sourceCall 256 context before).getD (.error .exhausted)
private def selectedInit (before : LabelMatchState) : Except PatternCacheError LabelMatchState :=
  (sourceInit 8 context before).getD (.error .exhausted)

/-- Only fixture parameter activation is external. All three source executions
are actual50→actual533B→actual533B, retaining the full first post-state. -/
private def history (firstInput : JSString) (firstNext : Option JSString) (secondInput : JSString) (secondNext : Option JSString) := do
  let initialized ← selectedInit (before50 firstInput firstNext)
  let (first, middle) ← selectedCall initialized
  let aliased := cacheWithAmbient middle {middle.base.regexp.ambient with environment :=
    ("cacheAlias", .object 7) :: ("tupleAlias", first) :: middle.base.regexp.ambient.environment}
  let (second, after) ← selectedCall (activate secondInput secondNext aliased)
  pure (first, second, after.base.regexp.ambient.heap[2]?, after.base.regexp.ambient.heap.length,
    after.base.regexp.ambient.environment.lookup "cacheAlias", after.base.regexp.ambient.environment.lookup "tupleAlias")

/-- Both raw# collision orders keep the FIRST actual tuple identity and name,
although the second real producer derives a different requested name. -/
theorem source50_two_calls_raw_separator_collision_both_orders :
    history (cacheAscii ":a#b") (some (cacheAscii "c")) (cacheAscii ":a") (some (cacheAscii "b#c")) =
      .ok (.array 2, .array 2, some [.string (cacheAscii ":a#b"), .string (cacheAscii "a#b"), .boolean true], 4,
        some (.object 7), some (.array 2)) ∧
    history (cacheAscii ":a") (some (cacheAscii "b#c")) (cacheAscii ":a#b") (some (cacheAscii "c")) =
      .ok (.array 2, .array 2, some [.string (cacheAscii ":a"), .string (cacheAscii "a"), .boolean true], 4,
        some (.object 7), some (.array 2)) := by
  simp only [history, selectedInit, selectedCall, sourceInit, sourceCall, parses_init, parses_source]
  cbv <;> repeat' constructor

/-- Undefined and the primitive stringundefined collide in both source-call
orders. The second call allocates its capture array, but never a second tuple. -/
theorem source50_two_calls_undefined_collision_both_orders :
    history idInput none idInput (some (cacheAscii "undefined")) =
      .ok (.array 2, .array 2, some [.string idInput, .string idName, .boolean true], 4,
        some (.object 7), some (.array 2)) ∧
    history idInput (some (cacheAscii "undefined")) idInput none =
      .ok (.array 2, .array 2, some [.string idInput, .string idName, .boolean true], 4,
        some (.object 7), some (.array 2)) := by
  simp only [history, selectedInit, selectedCall, sourceInit, sourceCall, parses_init, parses_source]
  cbv <;> repeat' constructor

/-- Cache/tuple aliases are retained by the actual plain contract's old-array
and environment frames; the current caller state is not reconstructed. -/
theorem source_plain_frames_preserve_initial_caller_aliases :
    let before := fixture idInput none emptyLiteralObject
    let aliased := cacheWithAmbient before {before.base.regexp.ambient with environment :=
      ("cacheAlias", .object 7) :: before.base.regexp.ambient.environment}
    Frames aliased (plainState aliased context idInput idName none 7 emptyLiteralObject) context idInput ∧
    (plainState aliased context idInput idName none 7 emptyLiteralObject).base.regexp.ambient.environment.lookup "cacheAlias" = some (.object 7) := by
  intro before aliased
  have realm : LabelRealm aliased labelStandardContext := by
    have original := fixture_realm idInput none emptyLiteralObject []
    cases original
    constructor <;> assumption
  have aliasInputs : PlainInputs aliased context idInput idName none 7 emptyLiteralObject none 2 := by
    exact ⟨⟨⟨realm, rfl⟩, ⟨id_valid, rfl⟩, rfl, rfl, rfl, missing_path idName none, (by decide)⟩,
      Or.inl .absent, ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  exact ⟨(source_plain_satisfies 0 aliased context idInput idName none 7 emptyLiteralObject none 2 aliasInputs).2.frames, rfl⟩

/-- Warm actual source skips a malformed future body'(' after a REAL first
plain store. This minimal warm/plain fixture deliberately lacks standard constructor
readiness; no cold construction fact is supplied to obtain this hit. -/
theorem first_plain_store_skips_invalid_future_body_cold_readiness :
    history idInput (some (cacheAscii "{(}#undefined")) (cacheAscii ":id#{(}") none =
      .ok (.array 2, .array 2, some [.string idInput, .string idName, .boolean true], 4,
        some (.object 7), some (.array 2)) := by
  simp only [history, selectedInit, selectedCall, sourceInit, sourceCall, parses_init, parses_source]
  cbv <;> repeat' constructor

/-- Error-only projection outside PlainInputs. Readonly/nonextensible DATA
are ordinary strict rejections; ARRAY RHS to the legacy prototype setter is a
model frontier (native may succeed/reprototype), not a native rejection theorem.
No post-error heap/rollback is claimed. -/
theorem cold_descriptor_rejections_and_array_setter_frontier :
    (selectedCall (fixture idInput none (dataObject idInput none (.number 0) false false))).map Prod.fst =
      .error (.evaluation (.objectError .notWritable)) ∧
    (selectedCall (fixture idInput none {emptyLiteralObject with extensible := false})).map Prod.fst =
      .error (.evaluation (.objectError .notExtensible)) ∧
    (selectedCall (fixture idInput none ⟨[(key idInput none, .accessor .missing .prototype false true)], some 0, true⟩)).map Prod.fst =
      .error (.evaluation (.objectError .unsupported)) := by
  simp only [selectedCall, sourceCall, parses_source]
  cbv <;> repeat' constructor


/-- The root descriptor absence is proved BEFORE actual50. Fresh ordinary own
storage alone is not used as an inherited lookup assumption. -/
theorem actual_source50_then_arbitrary_plain_source (name : JSString) (next : Option JSString) (validName : LabelRegExp.Name name) :
    sourceInit 8 context (before50 (58 :: name) next) = some (.ok (freshBefore (58 :: name) next)) ∧
    sourceCall 256 context (freshBefore (58 :: name) next) =
      some (.ok (.array 2, plainState (freshBefore (58 :: name) next) context (58 :: name) name next 7 emptyLiteralObject)) ∧
    InitContract (before50 (58 :: name) next) (freshBefore (58 :: name) next) ∧
    PlainContract (freshBefore (58 :: name) next)
      (plainState (freshBefore (58 :: name) next) context (58 :: name) name next 7 emptyLiteralObject)
      context (58 :: name) name next 7 emptyLiteralObject (.array 2) := by
  apply source_init_then_plain_satisfies 6 0 (before50 (58 :: name) next) context (58 :: name) name next (objectPrototypeProjection []) none 1
  have realm : LabelRealm (before50 (58 :: name) next) labelStandardContext := by
    have original := standard_realm (58 :: name)
    cases original
    constructor <;> assumption
  exact ⟨⟨realm, rfl⟩, ⟨validName, rfl⟩, rfl, rfl, .absent rfl rfl rfl, by decide, Or.inl .absent, Or.inl rfl⟩

/-- Bounded actual68 execution witness through the full selected533B AST.
It is not a universal cold-regex/cache theorem or a proof of source67 lookahead. -/
theorem cold_terminal68_executes_real_constructor_profile :
    (do
      let before := before50 (cacheAscii ":id{[0-9]+}") none
      let before := cacheWithAmbient before {before.base.regexp.ambient with environment := ("RegExp", .function 6) :: before.base.regexp.ambient.environment}
      let initialized ← selectedInit before
      let (value, after) ← selectedCall initialized
      pure (value, after.base.regexp.ambient.heap[1]?, after.base.regexp.ambient.heap[2]?, after.base.regexp.brands.lookup 9)) =
      .ok (.array 2, some [.string (cacheAscii ":id{[0-9]+}"), .string idName, .string (cacheAscii "[0-9]+")],
        some [.string (cacheAscii ":id{[0-9]+}"), .string idName, .object 9], some digitsRecord) := by
  simp only [selectedInit, selectedCall, sourceInit, sourceCall, parses_init, parses_source]
  cbv <;> repeat' constructor

/-- The caller alias points at the SAME old cache object and sees its mutation;
only unrelated old object cells are covered by the old-object frame. -/
theorem caller_alias_observes_actual_cache_object_write :
    (let before := fixture idInput none emptyLiteralObject
     let aliased := cacheWithAmbient before {before.base.regexp.ambient with environment := ("cacheAlias", .object 7) :: before.base.regexp.ambient.environment}
     (selectedCall aliased).map (fun (_, after) => (after.base.regexp.ambient.environment.lookup "cacheAlias",
       getProperty propertyFuel after.base.regexp.ambient.objects 7 (key idInput none),
       after.base.regexp.ambient.objects[7]?.bind (fun object => object.own.lookup (key idInput none))))) =
      .ok (some (.object 7), .ok (.array 2), some (.data (.array 2) true true true)) := by
  simp only [selectedCall, sourceCall, parses_source]
  cbv <;> repeat' constructor

/-- info: 'HonoLean.Upstream.PatternCache.source_block_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_block_warm_satisfies
/-- info: 'HonoLean.Upstream.PatternCache.source_warm_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_warm_satisfies
/-- info: 'HonoLean.Upstream.PatternCache.source_plain_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_plain_satisfies
/-- info: 'HonoLean.Upstream.PatternCache.source_miss_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_miss_satisfies

/-- info: 'HonoLean.Upstream.PatternCache.source_init_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_init_satisfies
/-- info: 'HonoLean.Upstream.PatternCache.source_init_then_plain_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_init_then_plain_satisfies

end HonoLean.Upstream.PatternCache.Checks
