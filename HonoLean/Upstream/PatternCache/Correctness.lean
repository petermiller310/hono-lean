import HonoLean.Upstream.PatternCache.Contract

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.PatternCache
open SourceSubset ECMA2025

theorem next_stringification (next : Option JSString) : cachePrimitiveToString (nextValue next) = .ok (nextText next) := by
  cases next <;> rfl

theorem raw_key (input : JSString) (next : Option JSString) : patternCacheKey input (nextValue next) = .ok (key input next) := by
  rw [patternCacheKey, next_stringification]
  rfl

def keyedState (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) (next : Option JSString) : LabelMatchState :=
  let matched := matchedState before context input
  cacheWithAmbient matched {matched.base.regexp.ambient with environment :=
    ("cacheKey", .string (key input next)) :: matched.base.regexp.ambient.environment}

def warmState (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) : LabelMatchState :=
  resetCaller before (matchedState before context input)

def plainState (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) : LabelMatchState :=
  let array := plainArray before context input name
  resetCaller before (cacheWithAmbient array {array.base.regexp.ambient with
    objects := array.base.regexp.ambient.objects.set cache (updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1)))})

theorem set_from_data_path (heap : ObjectHeap) (key : JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth : Nat) (value : Value)
    (found : heap[cache]? = some object) (path : NodeCaptureGuard.DescriptorPath heap key cache descriptor depth)
    (bound : depth ≤ propertyFuel) (writable : WritableData object key descriptor) :
    setProperty propertyFuel heap cache key value = .ok (heap.set cache (updatedObject object key value)) := by
  have resolved := NodeCaptureGuard.descriptor_path_lookup heap key cache descriptor depth propertyFuel path bound
  obtain ⟨inherited, own⟩ := writable
  rcases inherited with rfl | ⟨previous, enumerable, configurable, rfl⟩
  · rcases own with ⟨absent, extensible⟩ | ⟨old, oldEnumerable, oldConfigurable, present⟩
    · simp [setProperty, resolved, writeOwnData, found, absent, extensible, updatedObject, bind, Except.bind]
    · simp [setProperty, resolved, writeOwnData, found, present, updatedObject, bind, Except.bind]
  · rcases own with ⟨absent, extensible⟩ | ⟨old, oldEnumerable, oldConfigurable, present⟩
    · simp [setProperty, resolved, writeOwnData, found, absent, extensible, updatedObject, bind, Except.bind]
    · simp [setProperty, resolved, writeOwnData, found, present, updatedObject, bind, Except.bind]

theorem updated_own (object : OrdinaryObject) (key : JSString) (descriptor : Option PropertyDescriptor) (value : Value)
    (writable : WritableData object key descriptor) :
    ∃ enumerable configurable, (updatedObject object key value).own.lookup key = some (.data value true enumerable configurable) ∧
      (updatedObject object key value).prototype = object.prototype ∧ (updatedObject object key value).extensible = object.extensible := by
  rcases writable.2 with ⟨absent, _⟩ | ⟨old, enumerable, configurable, present⟩
  · refine ⟨true, true, ?_, ?_, ?_⟩ <;> simp [updatedObject, absent, newDataObject, putOwn]
  · refine ⟨enumerable, configurable, ?_, ?_, ?_⟩ <;> simp [updatedObject, present, putOwn]

private theorem lookup_filter_other (entries : List (JSString × PropertyDescriptor)) (key other : JSString) (different : other ≠ key) :
    (entries.filter (fun entry => entry.1 != key)).lookup other = entries.lookup other := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨head, descriptor⟩ := entry
    by_cases removed : head = key
    · subst head
      have unequal : (other == key) = false := beq_eq_false_iff_ne.mpr different
      simp [List.lookup, unequal, ih]
    · have retained : (head == key) = false := beq_eq_false_iff_ne.mpr removed
      simp only [bne] at ih
      simp [List.filter, bne, retained, List.lookup, ih]

theorem updated_other (object : OrdinaryObject) (key other : JSString) (value : Value) (different : other ≠ key) :
    (updatedObject object key value).own.lookup other = object.own.lookup other := by
  unfold updatedObject
  cases own : object.own.lookup key with
  | none => simp [newDataObject, putOwn, List.lookup, beq_eq_false_iff_ne.mpr different, lookup_filter_other _ key other different]
  | some descriptor =>
    cases descriptor with
    | accessor getter setter enumerable configurable =>
      simp [newDataObject, putOwn, List.lookup, beq_eq_false_iff_ne.mpr different, lookup_filter_other _ key other different]
    | data previous writable enumerable configurable =>
      cases writable <;> simp [newDataObject, putOwn, List.lookup, beq_eq_false_iff_ne.mpr different, lookup_filter_other _ key other different]

/-- Current cache descriptor after actual source60. Its path and owner bounds
are derived from BEFORE source60, whose only object effect is fresh literal allocation. -/
theorem matched_path (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before context input name body next cache object descriptor depth) :
    NodeCaptureGuard.DescriptorPath (matchedState before context input).base.regexp.ambient.objects (key input next) cache descriptor depth ∧
    (matchedState before context input).base.regexp.ambient.objects[cache]? = some object := by
  have contract := LabelMatch.result_contract before context.label input
  constructor
  · change NodeCaptureGuard.DescriptorPath (LabelMatch.resultState before context.label input).base.regexp.ambient.objects _ _ _ _
    rw [contract.objects]
    exact NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ inputs.path
  · exact (contract.oldObjects cache (List.getElem?_eq_some_iff.mp inputs.cacheFound).1).trans inputs.cacheFound

def blockKeyState (before : LabelMatchState) (input : JSString) (next : Option JSString) : LabelMatchState :=
  cacheWithAmbient before {before.base.regexp.ambient with environment := ("cacheKey", .string (key input next)) :: before.base.regexp.ambient.environment}

theorem eval_cache_data (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (cache : Nat) (property : JSString) (value : Value)
    (cacheFound : before.base.regexp.ambient.environment.lookup "patternCache" = some (.object cache))
    (keyFound : before.base.regexp.ambient.environment.lookup "cacheKey" = some (.string property))
    (read : getProperty propertyFuel before.base.regexp.ambient.objects cache property = .ok value) :
    evalPatternCacheExpr (extra + 3) defaultSplitLimit context cacheExpr before = .ok (value, before) := by
  have base := evalPatternCache_variable extra defaultSplitLimit context before "patternCache" (.object cache) cacheFound
  have field := evalPatternCache_variable extra defaultSplitLimit context before "cacheKey" (.string property) keyFound
  have evaluated := evalPatternCache_index (extra + 2) defaultSplitLimit context _ _ before before before (.object cache) (.string property) base field
  simpa [cacheExpr, keyExpr, cacheReadProperty, readProperty, read, Except.mapError, Except.map] using evaluated

theorem execute_warm_block (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : BlockWarmInputs before input next cache object value writable enumerable configurable depth) :
    executePatternCache (extra + 16) defaultSplitLimit context block before =
      .ok (.returned value (blockKeyState before input next)) := by
  have keyEval := evalPatternCache_key (extra + 11) defaultSplitLimit context before input (nextValue next) inputs.labelBinding inputs.nextBinding
  rw [raw_key] at keyEval
  have budgetKey : extra + 11 + 4 = extra + 15 := by omega
  rw [budgetKey] at keyEval
  dsimp only [Except.map] at keyEval
  change evalPatternCacheExpr (extra + 15) defaultSplitLimit context keyTemplate before = .ok (.string (key input next), before) at keyEval
  have resolved := NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ _ inputs.path inputs.pathBound
  have read := iterator_get_of_lookup propertyFuel _ _ _ _ value resolved (.data value writable enumerable configurable)
  have cacheBinding : (blockKeyState before input next).base.regexp.ambient.environment.lookup "patternCache" = some (.object cache) := by
    change List.lookup "patternCache" (("cacheKey", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.cacheBinding
  have keyBinding : (blockKeyState before input next).base.regexp.ambient.environment.lookup "cacheKey" = some (.string (key input next)) := by rfl
  have lookup := eval_cache_data (extra + 10) (blockKeyState before input next) context cache (key input next) value cacheBinding keyBinding read
  have budgetRead : extra + 10 + 3 = extra + 13 := by omega
  rw [budgetRead] at lookup
  have test : evalPatternCacheExpr (extra + 14) defaultSplitLimit context (.logicalNot cacheExpr) (blockKeyState before input next) =
      .ok (.boolean false, blockKeyState before input next) := by
    rw [evalPatternCacheExpr, lookup]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [inputs.truthy]
    rfl
  change executePatternCache (extra + 16) defaultSplitLimit context
    [.declare "cacheKey" keyTemplate, .branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] before = _
  rw [executePatternCache, keyEval]
  dsimp only [bind, Except.bind]
  change executePatternCache (extra + 15) defaultSplitLimit context [.branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] (blockKeyState before input next) = _
  rw [executePatternCache, test]
  simp only [truthy, Bool.false_eq_true, ↓reduceIte, executePatternCache, cacheRestoreEnvironment, bind, Except.bind]
  change (do
    let (returned, after) ← evalPatternCacheExpr (extra + 13) defaultSplitLimit context cacheExpr (blockKeyState before input next)
    pure (PatternCacheCompletion.returned returned after)) = _
  rw [lookup]
  rfl

/-- Two actual Get occurrences in full source440B; all cold code is retained
but not entered. This minimal theorem has no match/constructor facts. -/
theorem source_block_warm_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : BlockWarmInputs before input next cache object value writable enumerable configurable depth) :
    sourceBlock (extra + 16) context before = some (.ok (value, before)) := by
  rw [sourceBlock, parses_block]
  dsimp only [Option.map]
  rw [runPatternCache_restores_caller _ _ _ _ _ _ _
    (execute_warm_block extra before context input next cache object value writable enumerable configurable depth inputs)]
  rfl


theorem label_declaration (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) :
    executeLabelMatch (extra + 128) defaultSplitLimit context.label ⟨"match", .variable "label", "match", labelActualLiteral⟩ before =
      .ok (matchedState before context input) := by
  have executed := LabelMatch.execute_source extra before context.label input inputs
  rw [LabelMatch.sourceMatch, LabelMatch.parses_source] at executed
  exact Option.some.inj executed

theorem execute_source_prefix (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) :
    executePatternCache (extra + 256) defaultSplitLimit context program before =
      executePatternCache (extra + 255) defaultSplitLimit context [.branch matchExpr block [], .ret (.ordinary .null)]
        (matchedState before context input) := by
  have declared := label_declaration (extra + 126) before context input inputs
  have budget : extra + 126 + 128 = extra + 254 := by omega
  rw [budget] at declared
  change executePatternCache ((extra + 254) + 2) defaultSplitLimit context
    (.declare "match" (.labelMatch (.variable "label") "match" labelActualLiteral) :: _) before = _
  rw [executePatternCache_declare_label, declared]
  rfl

theorem matched_value (before : LabelMatchState) (input name : JSString) (body : Option JSString)
    (valid : LabelRegExp.Label input name body) : labelEngineValue before input = .array before.base.regexp.ambient.heap.length := by
  rw [labelEngineValue, LabelRegExp.execute_label_hit input name body valid]

theorem matched_block_inputs (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context input name body next cache object value writable enumerable configurable depth) :
    BlockWarmInputs (matchedState before context input) input next cache object value writable enumerable configurable depth := by
  obtain ⟨path, found⟩ := matched_path before context input name body next cache object _ depth inputs.toHeaderInputs
  refine ⟨?_, ?_, ?_, found, path, inputs.pathBound, inputs.truthy⟩
  · change List.lookup "label" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.source.labelBinding
  · change List.lookup "next" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  · change List.lookup "patternCache" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.cacheBinding

theorem execute_source_warm (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context input name body next cache object value writable enumerable configurable depth) :
    executePatternCache (extra + 256) defaultSplitLimit context program before =
      .ok (.returned value (matchedState before context input)) := by
  have binding : (matchedState before context input).base.regexp.ambient.environment.lookup "match" =
      some (.array before.base.regexp.ambient.heap.length) := by
    change some (labelEngineValue before input) = _
    rw [matched_value before input name body inputs.label]
  have condition := evalPatternCache_variable (extra + 252) defaultSplitLimit context (matchedState before context input) "match" _ binding
  have budget : extra + 252 + 2 = extra + 254 := by omega
  rw [budget] at condition
  change evalPatternCacheExpr (extra + 254) defaultSplitLimit context matchExpr (matchedState before context input) = .ok (_, matchedState before context input) at condition
  have blocked := execute_warm_block (extra + 238) (matchedState before context input) context input next cache object value writable enumerable configurable depth
    (matched_block_inputs before context input name body next cache object value writable enumerable configurable depth inputs)
  have budgetBlock : extra + 238 + 16 = extra + 254 := by omega
  rw [budgetBlock] at blocked
  rw [execute_source_prefix extra before context input inputs.source]
  rw [executePatternCache, condition]
  simp only [bind, Except.bind, truthy, ↓reduceIte]
  rw [blocked]
  rfl

theorem label_frames (before : LabelMatchState) (context : PatternCacheContext) (input : JSString) :
    Frames before (warmState before context input) context input := by
  constructor
  case labelResults =>
    constructor
    · rintro ⟨name, body, valid⟩
      have hit := LabelRegExp.execute_label_hit input name body valid
      have bounds := LabelRegExp.label_capture_bounds input name body valid
      simp [warmState, resetCaller, matchedState, LabelMatch.resultState, labelEngineState, labelFreshState, cacheWithAmbient, hit, bounds.1]
    · intro absent
      have miss := (LabelRegExp.execute_label_miss_iff input).mpr absent
      simp [warmState, resetCaller, matchedState, LabelMatch.resultState, labelEngineState, labelFreshState, cacheWithAmbient, miss]
  all_goals cases outcome : LabelRegExp.execute LabelRegExp.labelCode input <;>
    simp [warmState, resetCaller, matchedState, LabelMatch.resultState, labelEngineState, labelFreshState, cacheWithAmbient, outcome]

theorem warm_contract (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value)
    (found : before.base.regexp.ambient.objects[cache]? = some object) (valid : LabelRegExp.Label input name body) :
    WarmContract before (warmState before context input) context input name body cache value value := by
  have contract := LabelMatch.result_contract before context.label input
  refine ⟨rfl, ?_, (contract.success name body valid).2.1, contract.objects, contract.oldArrays, label_frames before context input⟩
  exact contract.oldObjects cache (List.getElem?_eq_some_iff.mp found).1

/-- Full actual533B warm path. The stored truthy DATA may be ANY Value, including
malformed/non-tuple values and invalid future regex bodies. No cold readiness. -/
theorem source_warm_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat)
    (inputs : WarmInputs before context input name body next cache object value writable enumerable configurable depth) :
    sourceCall (extra + 256) context before = some (.ok (value, warmState before context input)) ∧
    WarmContract before (warmState before context input) context input name body cache value value := by
  constructor
  · rw [sourceCall, parses_source]
    dsimp only [Option.map]
    rw [runPatternCache_restores_caller _ _ _ _ _ _ _ (execute_source_warm extra before context input name body next cache object value writable enumerable configurable depth inputs)]
    rfl
  · exact warm_contract before context input name body cache object value inputs.cacheFound inputs.label

theorem execute_source_miss (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) (absent : ¬ ∃ name body, LabelRegExp.Label input name body) :
    executePatternCache (extra + 256) defaultSplitLimit context program before =
      .ok (.returned .null (matchedState before context input)) := by
  have miss := (LabelRegExp.execute_label_miss_iff input).mpr absent
  have binding : (matchedState before context input).base.regexp.ambient.environment.lookup "match" = some .null := by
    change some (labelEngineValue before input) = _
    simp [labelEngineValue, miss]
  have condition := evalPatternCache_variable (extra + 252) defaultSplitLimit context (matchedState before context input) "match" .null binding
  have budget : extra + 252 + 2 = extra + 254 := by omega
  rw [budget] at condition
  change evalPatternCacheExpr (extra + 254) defaultSplitLimit context matchExpr (matchedState before context input) = .ok (.null, matchedState before context input) at condition
  rw [execute_source_prefix extra before context input inputs]
  rw [executePatternCache, condition]
  simp [truthy, executePatternCache, evalPatternCacheExpr, evalExpression, cacheRestoreEnvironment, cacheWithAmbient, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A computed miss never evaluates next, patternCache, cacheKey or construction.
Those bindings and cache/writable facts are deliberately absent from the domain. -/
theorem source_miss_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before context.label input) (absent : ¬ ∃ name body, LabelRegExp.Label input name body) :
    sourceCall (extra + 256) context before = some (.ok (.null, warmState before context input)) ∧
    MissContract before (warmState before context input) context input .null := by
  constructor
  · rw [sourceCall, parses_source]
    dsimp only [Option.map]
    rw [runPatternCache_restores_caller _ _ _ _ _ _ _ (execute_source_miss extra before context input inputs absent)]
    rfl
  · have contract := LabelMatch.result_contract before context.label input
    exact ⟨rfl, (contract.failure absent).2.1, contract.objects, label_frames before context input⟩


theorem eval_number (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (value : Nat) :
    evalPatternCacheExpr (extra + 2) defaultSplitLimit context (.ordinary (.number value)) before = .ok (.number value, before) := by
  simp [evalPatternCacheExpr, evalExpression, cacheWithAmbient, Except.map, Except.mapError] <;> rfl

theorem eval_true (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) :
    evalPatternCacheExpr (extra + 2) defaultSplitLimit context (.ordinary (.boolean true)) before = .ok (.boolean true, before) := by
  simp [evalPatternCacheExpr, evalExpression, cacheWithAmbient, Except.map, Except.mapError] <;> rfl

theorem eval_match_index (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (matched index : Nat) (values : List Value)
    (binding : before.base.regexp.ambient.environment.lookup "match" = some (.array matched))
    (found : before.base.regexp.ambient.heap[matched]? = some values) :
    evalPatternCacheExpr (extra + 3) defaultSplitLimit context (.index matchExpr (.ordinary (.number index))) before =
      .ok (values[index]?.getD .undefined, before) := by
  have base := evalPatternCache_variable extra defaultSplitLimit context before "match" (.array matched) binding
  have evaluated := evalPatternCache_index (extra + 2) defaultSplitLimit context _ _ before before before (.array matched) (.number index)
    base (eval_number extra before context index)
  simpa [matchExpr, cacheReadProperty, readProperty, found, Except.map, Except.mapError] using evaluated

theorem eval_plain_tuple (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext)
    (input name : JSString) (matched : Nat) (values : List Value)
    (labelBinding : before.base.regexp.ambient.environment.lookup "label" = some (.string input))
    (matchBinding : before.base.regexp.ambient.environment.lookup "match" = some (.array matched))
    (matchFound : before.base.regexp.ambient.heap[matched]? = some values)
    (nameFound : values[1]? = some (.string name)) :
    evalPatternCacheExpr (extra + 8) defaultSplitLimit context plainTuple before =
      .ok (.array before.base.regexp.ambient.heap.length, cacheArrayCellState before (plainValues input name)) := by
  have bound := (List.getElem?_eq_some_iff.mp matchFound).1
  have label := evalPatternCache_variable (extra + 4) defaultSplitLimit context (cacheArrayCellState before []) "label" (.string input) labelBinding
  have foundAfter : (cacheArrayCellState before [.string input]).base.regexp.ambient.heap[matched]? = some values :=
    (List.getElem?_append_left bound).trans matchFound
  have indexed := eval_match_index (extra + 2) (cacheArrayCellState before [.string input]) context matched 1 values matchBinding foundAfter
  rw [nameFound] at indexed
  dsimp only [Option.getD] at indexed
  have third := eval_true (extra + 2) (cacheArrayCellState before [.string input, .string name]) context
  change evalPatternCacheExpr ((extra + 3) + 5) defaultSplitLimit context (.arrayLiteral [labelExpr, nameExpr, .ordinary (.boolean true)]) before = _
  rw [evalPatternCache_array3]
  change evalPatternCacheExpr (extra + 6) defaultSplitLimit context labelExpr (cacheEmptyArray before) = _ at label
  rw [label]
  dsimp only [bind, Except.bind]
  rw [cacheAppendElement_fresh]
  dsimp only [bind, Except.bind, List.nil_append]
  change evalPatternCacheExpr (extra + 5) defaultSplitLimit context nameExpr (cacheArrayCellState before [.string input]) = _ at indexed
  rw [indexed]
  dsimp only [bind, Except.bind]
  rw [cacheAppendElement_fresh]
  dsimp only [bind, Except.bind, List.cons_append, List.nil_append]
  rw [third]
  dsimp only [bind, Except.bind]
  rw [cacheAppendElement_fresh]
  rfl

def plainStoredState (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) : LabelMatchState :=
  let rhs := cacheArrayCellState (keyedState before context input next) (plainValues input name)
  cacheWithAmbient rhs {rhs.base.regexp.ambient with
    objects := rhs.base.regexp.ambient.objects.set cache (updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1)))}

theorem keyed_bindings (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before context input name none next cache object descriptor depth) :
    (keyedState before context input next).base.regexp.ambient.environment.lookup "label" = some (.string input) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "match" = some (.array before.base.regexp.ambient.heap.length) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "patternCache" = some (.object cache) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "cacheKey" = some (.string (key input next)) := by
  have produced := matched_value before input name none inputs.label
  change List.lookup "label" (("cacheKey", _) :: ("match", _) :: before.base.regexp.ambient.environment) = _ ∧
    List.lookup "match" (("cacheKey", _) :: ("match", labelEngineValue before input) :: before.base.regexp.ambient.environment) = _ ∧
    List.lookup "patternCache" (("cacheKey", _) :: ("match", _) :: before.base.regexp.ambient.environment) = _ ∧ _
  simp only [List.lookup_cons, String.reduceBEq, produced]
  exact ⟨inputs.source.labelBinding, trivial, inputs.cacheBinding, rfl⟩

theorem keyed_captures (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (valid : LabelRegExp.Label input name none) :
    (keyedState before context input next).base.regexp.ambient.heap = before.base.regexp.ambient.heap ++ [LabelMatch.captures input name none] ∧
    (keyedState before context input next).base.regexp.ambient.heap[before.base.regexp.ambient.heap.length]? = some (LabelMatch.captures input name none) ∧
    (keyedState before context input next).base.regexp.ambient.heap.length = before.base.regexp.ambient.heap.length + 1 := by
  have heap := (LabelMatch.result_contract before context.label input).success name none valid |>.2.1
  change (LabelMatch.resultState before context.label input).base.regexp.ambient.heap = _ at heap
  constructor
  · exact heap
  · change (LabelMatch.resultState before context.label input).base.regexp.ambient.heap[_]? = _ ∧
      (LabelMatch.resultState before context.label input).base.regexp.ambient.heap.length = _
    rw [heap]
    simp

theorem plain_first_read (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    ∃ value, getProperty propertyFuel (keyedState before context input next).base.regexp.ambient.objects cache (key input next) = .ok value ∧ truthy value = false := by
  have path := (matched_path before context input name none next cache object descriptor depth inputs.toHeaderInputs).1
  have resolved := NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ _ path inputs.pathBound
  rcases inputs.falsy with read | ⟨value, writable, enumerable, configurable, equal, falsy⟩
  · exact ⟨.undefined, iterator_get_of_lookup _ _ _ _ _ _ resolved read, rfl⟩
  · subst descriptor
    exact ⟨value, iterator_get_of_lookup _ _ _ _ _ _ resolved (.data value writable enumerable configurable), falsy⟩

theorem execute_plain_assignment (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    executePatternCacheAssignment (extra + 250) defaultSplitLimit context cacheExpr plainTuple (keyedState before context input next) =
      .ok (plainStoredState before context input name next cache object) := by
  obtain ⟨labelBinding, matchBinding, cacheBinding, keyBinding⟩ := keyed_bindings before context input name next cache object descriptor depth inputs.toHeaderInputs
  obtain ⟨heap, captured, length⟩ := keyed_captures before context input name next inputs.label
  have rhs := eval_plain_tuple (extra + 242) (keyedState before context input next) context input name before.base.regexp.ambient.heap.length
    (LabelMatch.captures input name none) labelBinding matchBinding captured rfl
  have budgetRhs : extra + 242 + 8 = extra + 250 := by omega
  rw [budgetRhs, length] at rhs
  have base := evalPatternCache_variable (extra + 248) defaultSplitLimit context (keyedState before context input next) "patternCache" (.object cache) cacheBinding
  have property := evalPatternCache_variable (extra + 248) defaultSplitLimit context (keyedState before context input next) "cacheKey" (.string (key input next)) keyBinding
  have budgetVar : extra + 248 + 2 = extra + 250 := by omega
  rw [budgetVar] at base property
  have assigned := executePatternCacheAssignment_reference (extra + 250) defaultSplitLimit context _ _ _ _ _ _ _ cache (key input next)
    (.array (before.base.regexp.ambient.heap.length + 1)) base property rhs
  change executePatternCacheAssignment (extra + 250) defaultSplitLimit context cacheExpr plainTuple (keyedState before context input next) = _ at assigned
  obtain ⟨path, found⟩ := matched_path before context input name none next cache object descriptor depth inputs.toHeaderInputs
  have set := set_from_data_path (cacheArrayCellState (keyedState before context input next) (plainValues input name)).base.regexp.ambient.objects
    (key input next) cache object descriptor depth (.array (before.base.regexp.ambient.heap.length + 1)) found path inputs.pathBound inputs.writable
  rw [assigned, set]
  rfl

theorem plain_return_read (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    evalPatternCacheExpr (extra + 251) defaultSplitLimit context cacheExpr (plainStoredState before context input name next cache object) =
      .ok (.array (before.base.regexp.ambient.heap.length + 1), plainStoredState before context input name next cache object) := by
  obtain ⟨_, _, cacheBinding, keyBinding⟩ := keyed_bindings before context input name next cache object descriptor depth inputs.toHeaderInputs
  have objects := (LabelMatch.result_contract before context.label input).objects
  have old := (List.getElem?_eq_some_iff.mp inputs.cacheFound).1
  have bound : cache < (keyedState before context input next).base.regexp.ambient.objects.length := by
    change cache < (LabelMatch.resultState before context.label input).base.regexp.ambient.objects.length
    rw [objects]
    simp only [List.length_append, List.length_singleton]
    omega
  have found : (plainStoredState before context input name next cache object).base.regexp.ambient.objects[cache]? =
      some (updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1))) := List.getElem?_set_self bound
  obtain ⟨enumerable, configurable, own, _, _⟩ := updated_own object (key input next) descriptor (.array (before.base.regexp.ambient.heap.length + 1)) inputs.writable
  have read := getProperty_data _ cache (propertyFuel - 1) (key input next) _ _ true enumerable configurable found own
  change getProperty propertyFuel _ _ _ = _ at read
  have run := eval_cache_data (extra + 248) (plainStoredState before context input name next cache object) context cache (key input next)
    (.array (before.base.regexp.ambient.heap.length + 1)) cacheBinding keyBinding read
  simpa only [Nat.add_assoc, Nat.reduceAdd] using run


theorem execute_cold_plain (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    executePatternCache (extra + 252) defaultSplitLimit context coldProgram (keyedState before context input next) =
      .ok (.normal (plainStoredState before context input name next cache object)) := by
  obtain ⟨_, binding, _, _⟩ := keyed_bindings before context input name next cache object descriptor depth inputs.toHeaderInputs
  have captured := (keyed_captures before context input name next inputs.label).2.1
  have body := eval_match_index (extra + 248) (keyedState before context input next) context before.base.regexp.ambient.heap.length 2
    (LabelMatch.captures input name none) binding captured
  have budgetBody : extra + 248 + 3 = extra + 251 := by omega
  rw [budgetBody] at body
  change evalPatternCacheExpr (extra + 251) defaultSplitLimit context bodyExpr (keyedState before context input next) =
    .ok (.undefined, keyedState before context input next) at body
  have assigned : executePatternCache (extra + 251) defaultSplitLimit context [.assign cacheExpr plainTuple] (keyedState before context input next) =
      .ok (.normal (plainStoredState before context input name next cache object)) := by
    rw [executePatternCache, execute_plain_assignment extra before context input name next cache object descriptor depth inputs]
    rfl
  change executePatternCache (extra + 252) defaultSplitLimit context
    [.branch bodyExpr [.assign cacheExpr regexTuple] [.assign cacheExpr plainTuple]] (keyedState before context input next) = _
  rw [executePatternCache, body]
  simp only [bind, Except.bind, truthy, Bool.false_eq_true, ↓reduceIte]
  rw [assigned]
  rfl

theorem execute_plain_block (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    executePatternCache (extra + 254) defaultSplitLimit context block (matchedState before context input) =
      .ok (.returned (.array (before.base.regexp.ambient.heap.length + 1)) (plainStoredState before context input name next cache object)) := by
  have labelBinding : (matchedState before context input).base.regexp.ambient.environment.lookup "label" = some (.string input) := by
    change List.lookup "label" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.source.labelBinding
  have nextBinding : (matchedState before context input).base.regexp.ambient.environment.lookup "next" = some (nextValue next) := by
    change List.lookup "next" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  have keyEval := evalPatternCache_key (extra + 249) defaultSplitLimit context (matchedState before context input) input (nextValue next) labelBinding nextBinding
  rw [raw_key] at keyEval
  dsimp only [Except.map] at keyEval
  change evalPatternCacheExpr (extra + 253) defaultSplitLimit context keyTemplate (matchedState before context input) =
    .ok (.string (key input next), matchedState before context input) at keyEval
  obtain ⟨_, _, cacheBinding, keyBinding⟩ := keyed_bindings before context input name next cache object descriptor depth inputs.toHeaderInputs
  obtain ⟨previous, read, falsy⟩ := plain_first_read before context input name next cache object descriptor depth inputs
  have first := eval_cache_data (extra + 248) (keyedState before context input next) context cache (key input next) previous cacheBinding keyBinding read
  have budgetRead : extra + 248 + 3 = extra + 251 := by omega
  rw [budgetRead] at first
  have test : evalPatternCacheExpr (extra + 252) defaultSplitLimit context (.logicalNot cacheExpr) (keyedState before context input next) =
      .ok (.boolean true, keyedState before context input next) := by
    rw [evalPatternCacheExpr, first]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [falsy]
    rfl
  change executePatternCache (extra + 254) defaultSplitLimit context
    [.declare "cacheKey" keyTemplate, .branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] (matchedState before context input) = _
  rw [executePatternCache, keyEval]
  dsimp only [bind, Except.bind]
  change executePatternCache (extra + 253) defaultSplitLimit context [.branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] (keyedState before context input next) = _
  rw [executePatternCache, test]
  simp only [bind, Except.bind, truthy, ↓reduceIte]
  rw [execute_cold_plain extra before context input name next cache object descriptor depth inputs]
  dsimp only [bind, Except.bind, cacheRestoreEnvironment]
  change executePatternCache (extra + 252) defaultSplitLimit context [.ret cacheExpr] (plainStoredState before context input name next cache object) = _
  rw [executePatternCache, plain_return_read extra before context input name next cache object descriptor depth inputs]
  rfl

theorem execute_source_plain (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    executePatternCache (extra + 256) defaultSplitLimit context program before =
      .ok (.returned (.array (before.base.regexp.ambient.heap.length + 1))
        (cacheWithAmbient (plainStoredState before context input name next cache object)
          {(plainStoredState before context input name next cache object).base.regexp.ambient with environment :=
            (matchedState before context input).base.regexp.ambient.environment})) := by
  have binding : (matchedState before context input).base.regexp.ambient.environment.lookup "match" = some (.array before.base.regexp.ambient.heap.length) := by
    change some (labelEngineValue before input) = _
    rw [matched_value before input name none inputs.label]
  have condition := evalPatternCache_variable (extra + 252) defaultSplitLimit context (matchedState before context input) "match" _ binding
  change evalPatternCacheExpr (extra + 254) defaultSplitLimit context matchExpr (matchedState before context input) = _ at condition
  rw [execute_source_prefix extra before context input inputs.source]
  rw [executePatternCache, condition]
  simp only [bind, Except.bind, truthy, ↓reduceIte]
  rw [execute_plain_block extra before context input name next cache object descriptor depth inputs]
  rfl

theorem plain_frames (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString) (cache : Nat) (object : OrdinaryObject) :
    Frames before (plainState before context input name next cache object) context input := by
  have frames := label_frames before context input
  cases frames
  constructor <;> assumption

theorem plain_contract (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    PlainContract before (plainState before context input name next cache object) context input name next cache object
      (.array (before.base.regexp.ambient.heap.length + 1)) := by
  have contract := LabelMatch.result_contract before context.label input
  have heap := (contract.success name none inputs.label).2.1
  have objectBound := (List.getElem?_eq_some_iff.mp inputs.cacheFound).1
  have objects := contract.objects
  change (matchedState before context input).base.regexp.ambient.heap = _ at heap
  change (matchedState before context input).base.regexp.ambient.objects = _ at objects
  constructor
  case returned => rfl
  case captures =>
    change (matchedState before context input).base.regexp.ambient.heap ++ [plainValues input name] = _
    rw [heap]
    simp [List.append_assoc]
  case objects =>
    change ((matchedState before context input).base.regexp.ambient.objects.set cache _) = _
    rw [objects]
  case cacheOwn =>
    have bound : cache < (matchedState before context input).base.regexp.ambient.objects.length := by
      rw [objects]
      simp only [List.length_append, List.length_singleton]
      omega
    exact ⟨updatedObject object (key input next) (.array (before.base.regexp.ambient.heap.length + 1)), List.getElem?_set_self bound,
      updated_own object (key input next) descriptor (.array (before.base.regexp.ambient.heap.length + 1)) inputs.writable⟩
  case otherObjects =>
    intro reference different old
    change ((matchedState before context input).base.regexp.ambient.objects.set cache _)[reference]? = _
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact contract.oldObjects reference old
  case oldArrays =>
    intro reference old
    change ((matchedState before context input).base.regexp.ambient.heap ++ [plainValues input name])[reference]? = _
    have bound : reference < (matchedState before context input).base.regexp.ambient.heap.length := by
      rw [heap]
      simp only [List.length_append, List.length_singleton]
      omega
    exact (List.getElem?_append_left bound).trans (contract.oldArrays reference old)
  case frames => exact plain_frames before context input name next cache object

/-- Source60 computes m/name/undefined optional capture, source70 creates its
fresh array, ordinary Set stores it, and source74 performs a NEW current Get. -/
theorem source_plain_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : PlainInputs before context input name next cache object descriptor depth) :
    sourceCall (extra + 256) context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1), plainState before context input name next cache object)) ∧
    PlainContract before (plainState before context input name next cache object) context input name next cache object
      (.array (before.base.regexp.ambient.heap.length + 1)) := by
  constructor
  · rw [sourceCall, parses_source]
    dsimp only [Option.map]
    rw [runPatternCache_restores_caller _ _ _ _ _ _ _ (execute_source_plain extra before context input name next cache object descriptor depth inputs)]
    rfl
  · exact plain_contract before context input name next cache object descriptor depth inputs


end HonoLean.Upstream.PatternCache
