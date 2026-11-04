import HonoLean.Upstream.PatternCacheTerminal.Rules

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.PatternCacheTerminal
open SourceSubset ECMA2025 PatternCache

theorem keyed_bindings (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : HeaderInputs before context input name body next cache object descriptor depth) :
    (keyedState before context input next).base.regexp.ambient.environment.lookup "label" = some (.string input) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "match" = some (.array before.base.regexp.ambient.heap.length) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "patternCache" = some (.object cache) ∧
    (keyedState before context input next).base.regexp.ambient.environment.lookup "cacheKey" = some (.string (key input next)) := by
  have produced := matched_value before input name body inputs.label
  change List.lookup "label" (("cacheKey", _) :: ("match", _) :: before.base.regexp.ambient.environment) = _ ∧
    List.lookup "match" (("cacheKey", _) :: ("match", labelEngineValue before input) :: before.base.regexp.ambient.environment) = _ ∧
    List.lookup "patternCache" (("cacheKey", _) :: ("match", _) :: before.base.regexp.ambient.environment) = _ ∧ _
  simp only [List.lookup_cons, String.reduceBEq, produced]
  exact ⟨inputs.source.labelBinding, trivial, inputs.cacheBinding, rfl⟩

theorem keyed_captures (before : LabelMatchState) (context : PatternCacheContext) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (valid : LabelRegExp.Label input name body) :
    (keyedState before context input next).base.regexp.ambient.heap = before.base.regexp.ambient.heap ++ [LabelMatch.captures input name body] ∧
    (keyedState before context input next).base.regexp.ambient.heap[before.base.regexp.ambient.heap.length]? = some (LabelMatch.captures input name body) ∧
    (keyedState before context input next).base.regexp.ambient.heap.length = before.base.regexp.ambient.heap.length + 1 := by
  have heap := (LabelMatch.result_contract before context.label input).success name body valid |>.2.1
  change (LabelMatch.resultState before context.label input).base.regexp.ambient.heap = _ at heap
  constructor
  · exact heap
  · change (LabelMatch.resultState before context.label input).base.regexp.ambient.heap[_]? = _ ∧
      (LabelMatch.resultState before context.label input).base.regexp.ambient.heap.length = _
    rw [heap]
    simp


theorem constructor_inputs (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    PatternConstruct.Inputs (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.regexp
      context.label.iterators.constructors (LabelMatch.safeRangeLabel name lower upper) name before.base.regexp.ambient.heap.length handle
      (LabelMatch.captures (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) lower upper constructor prototypeObject := by
  let realm := inputs.source.toLabelRealm
  have noArg := realm.oldNoArg
  have methods := realm.oldMethods
  have functions := realm.oldFunctions
  have members := realm.oldMembers
  have regexp := realm.oldRegExp
  have initial : LabelMatch.ConstructorInputs before context.label name lower upper handle constructor prototypeObject := by
    refine ⟨inputs.source, inputs.validName, inputs.lowerSafe, inputs.upperSafe, inputs.ordered,
      inputs.constructorBinding, ?_, ?_, ?_, ?_, regexp, inputs.handleBound, inputs.identity, inputs.prototypeFound⟩
    all_goals omega
  have produced := LabelMatch.produced_constructor_inputs before context.label name lower upper handle constructor prototypeObject initial
  constructor
  case labelBinding =>
    change List.lookup "label" (("cacheKey", _) :: (matchedState before context _).base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, matchedState] using produced.labelBinding
  case matchBinding =>
    change List.lookup "match" (("cacheKey", _) :: (matchedState before context _).base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, matchedState] using produced.matchBinding
  case constructorBinding =>
    change List.lookup "RegExp" (("cacheKey", _) :: (matchedState before context _).base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, matchedState] using produced.constructorBinding
  all_goals cases produced <;> assumption

theorem first_read (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    ∃ value, getProperty propertyFuel (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.regexp.ambient.objects
      cache (key (LabelMatch.safeRangeLabel name lower upper) next) = .ok value ∧ truthy value = false := by
  have path := (matched_path before context _ name _ next cache object descriptor depth inputs.toHeaderInputs).1
  have resolved := NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ _ path inputs.pathBound
  rcases inputs.falsy with read | ⟨value, writable, enumerable, configurable, equal, falsy⟩
  · exact ⟨.undefined, iterator_get_of_lookup _ _ _ _ _ _ resolved read, rfl⟩
  · subst descriptor
    exact ⟨value, iterator_get_of_lookup _ _ _ _ _ _ resolved (.data value writable enumerable configurable), falsy⟩

theorem eval_regex_tuple (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    evalPatternCacheExpr (extra + 250) defaultSplitLimit context regexTuple
      (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
      .ok (.array (before.base.regexp.ambient.heap.length + 1),
        tupleState (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) constructor.prototype lower upper (LabelMatch.safeRangeLabel name lower upper) name) := by
  have binding : (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.regexp.ambient.environment.lookup "next" = some (nextValue next) := by
    change List.lookup "next" (("cacheKey", _) :: ("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  obtain ⟨value, condition, falsy⟩ := eval_next_condition (extra + 239) _ context next binding inputs.terminal
  have budget : extra + 239 + 10 = extra + 249 := by omega
  rw [budget] at condition
  have evaluated := eval_terminal_tuple (extra + 237) _ context (LabelMatch.safeRangeLabel name lower upper) name before.base.regexp.ambient.heap.length handle
    _ lower upper constructor prototypeObject (constructor_inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs)
  have length := (keyed_captures before context _ name _ next inputs.label).2.2
  change evalPatternCacheExpr ((extra + 249) + 1) defaultSplitLimit context (.conditional nextCondition lookaheadTuple terminalTuple) _ = _
  rw [evalPatternCache_conditional (extra + 249) _ _ _ _ _ _ _ value condition, falsy]
  simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_assoc, Nat.reduceAdd, length] using evaluated

theorem execute_terminal_assignment (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    executePatternCacheAssignment (extra + 250) defaultSplitLimit context cacheExpr regexTuple
      (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
      .ok (storedState before context name lower upper next cache object constructor.prototype) := by
  obtain ⟨_, _, cacheBinding, keyBinding⟩ := keyed_bindings before context _ name _ next cache object descriptor depth inputs.toHeaderInputs
  have rhs := eval_regex_tuple extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs
  have base := evalPatternCache_variable (extra + 248) defaultSplitLimit context _ "patternCache" (.object cache) cacheBinding
  have property := evalPatternCache_variable (extra + 248) defaultSplitLimit context _ "cacheKey" (.string (key (LabelMatch.safeRangeLabel name lower upper) next)) keyBinding
  have budget : extra + 248 + 2 = extra + 250 := by omega
  rw [budget] at base property
  have assigned := executePatternCacheAssignment_reference (extra + 250) defaultSplitLimit context _ _ _ _ _ _ _ cache _
    (.array (before.base.regexp.ambient.heap.length + 1)) base property rhs
  obtain ⟨path, found⟩ := matched_path before context _ name _ next cache object descriptor depth inputs.toHeaderInputs
  have appended := NodeCaptureGuard.descriptor_path_append _ [initializedRegExpObject constructor.prototype] _ _ _ _ path
  have foundAfter : ((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype])[cache]? = some object :=
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  have set := set_from_data_path _ _ cache object descriptor depth (.array (before.base.regexp.ambient.heap.length + 1)) foundAfter appended inputs.pathBound inputs.writable
  change executePatternCacheAssignment (extra + 250) defaultSplitLimit context cacheExpr regexTuple _ = _ at assigned
  rw [assigned]
  change ((setProperty propertyFuel
    ((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]) cache
    (key (LabelMatch.safeRangeLabel name lower upper) next) (.array (before.base.regexp.ambient.heap.length + 1))).mapError _).map _ = _
  rw [set]
  rfl

theorem terminal_return_read (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    evalPatternCacheExpr (extra + 251) defaultSplitLimit context cacheExpr (storedState before context name lower upper next cache object constructor.prototype) =
      .ok (.array (before.base.regexp.ambient.heap.length + 1), storedState before context name lower upper next cache object constructor.prototype) := by
  obtain ⟨_, _, cacheBinding, keyBinding⟩ := keyed_bindings before context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) next cache object descriptor depth inputs.toHeaderInputs
  have objects := (LabelMatch.result_contract before context.label (LabelMatch.safeRangeLabel name lower upper)).objects
  have old := (List.getElem?_eq_some_iff.mp inputs.cacheFound).1
  have bound : cache < ((keyedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]).length := by
    change cache < ((LabelMatch.resultState before context.label (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]).length
    rw [objects]
    simp only [List.length_append, List.length_singleton]
    omega
  have found : (storedState before context name lower upper next cache object constructor.prototype).base.regexp.ambient.objects[cache]? =
      some (updatedObject object (key (LabelMatch.safeRangeLabel name lower upper) next) (.array (before.base.regexp.ambient.heap.length + 1))) := List.getElem?_set_self bound
  obtain ⟨enumerable, configurable, own, _, _⟩ := updated_own object (key (LabelMatch.safeRangeLabel name lower upper) next) descriptor (.array (before.base.regexp.ambient.heap.length + 1)) inputs.writable
  have read := getProperty_data _ cache (propertyFuel - 1) (key (LabelMatch.safeRangeLabel name lower upper) next) _ _ true enumerable configurable found own
  change getProperty propertyFuel _ _ _ = _ at read
  have run := eval_cache_data (extra + 248) (storedState before context name lower upper next cache object constructor.prototype) context cache (key (LabelMatch.safeRangeLabel name lower upper) next)
    (.array (before.base.regexp.ambient.heap.length + 1)) cacheBinding keyBinding read
  simpa only [Nat.add_assoc, Nat.reduceAdd] using run


theorem execute_cold_terminal (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    executePatternCache (extra + 252) defaultSplitLimit context coldProgram (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
      .ok (.normal (storedState before context name lower upper next cache object constructor.prototype)) := by
  obtain ⟨_, binding, _, _⟩ := keyed_bindings before context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) next cache object descriptor depth inputs.toHeaderInputs
  have captured := (keyed_captures before context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) next inputs.label).2.1
  have body := eval_match_index (extra + 248) (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) context before.base.regexp.ambient.heap.length 2
    (LabelMatch.captures (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) binding captured
  have budgetBody : extra + 248 + 3 = extra + 251 := by omega
  rw [budgetBody] at body
  change evalPatternCacheExpr (extra + 251) defaultSplitLimit context bodyExpr (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
    .ok (.string (PatternConstruct.rawBody lower upper), keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) at body
  have assigned : executePatternCache (extra + 251) defaultSplitLimit context [.assign cacheExpr regexTuple] (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
      .ok (.normal (storedState before context name lower upper next cache object constructor.prototype)) := by
    rw [executePatternCache, execute_terminal_assignment extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs]
    rfl
  change executePatternCache (extra + 252) defaultSplitLimit context
    [.branch bodyExpr [.assign cacheExpr regexTuple] [.assign cacheExpr plainTuple]] (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) = _
  rw [executePatternCache, body]
  simp only [bind, Except.bind, truthy, PatternConstruct.rawBody, List.isEmpty_cons, Bool.not_false, ↓reduceIte]
  rw [assigned]
  rfl

theorem execute_terminal_block (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    executePatternCache (extra + 254) defaultSplitLimit context block (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) =
      .ok (.returned (.array (before.base.regexp.ambient.heap.length + 1)) (storedState before context name lower upper next cache object constructor.prototype)) := by
  have labelBinding : (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.environment.lookup "label" = some (.string (LabelMatch.safeRangeLabel name lower upper)) := by
    change List.lookup "label" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.source.labelBinding
  have nextBinding : (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.environment.lookup "next" = some (nextValue next) := by
    change List.lookup "next" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.nextBinding
  have keyEval := evalPatternCache_key (extra + 249) defaultSplitLimit context (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) (LabelMatch.safeRangeLabel name lower upper) (nextValue next) labelBinding nextBinding
  rw [raw_key] at keyEval
  dsimp only [Except.map] at keyEval
  change evalPatternCacheExpr (extra + 253) defaultSplitLimit context keyTemplate (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) =
    .ok (.string (key (LabelMatch.safeRangeLabel name lower upper) next), matchedState before context (LabelMatch.safeRangeLabel name lower upper)) at keyEval
  obtain ⟨_, _, cacheBinding, keyBinding⟩ := keyed_bindings before context (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) next cache object descriptor depth inputs.toHeaderInputs
  obtain ⟨previous, read, falsy⟩ := first_read before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs
  have first := eval_cache_data (extra + 248) (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) context cache (key (LabelMatch.safeRangeLabel name lower upper) next) previous cacheBinding keyBinding read
  have budgetRead : extra + 248 + 3 = extra + 251 := by omega
  rw [budgetRead] at first
  have test : evalPatternCacheExpr (extra + 252) defaultSplitLimit context (.logicalNot cacheExpr) (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
      .ok (.boolean true, keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) := by
    rw [evalPatternCacheExpr, first]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [falsy]
    rfl
  change executePatternCache (extra + 254) defaultSplitLimit context
    [.declare "cacheKey" keyTemplate, .branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) = _
  rw [executePatternCache, keyEval]
  dsimp only [bind, Except.bind]
  change executePatternCache (extra + 253) defaultSplitLimit context [.branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr] (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) = _
  rw [executePatternCache, test]
  simp only [bind, Except.bind, truthy, ↓reduceIte]
  rw [execute_cold_terminal extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs]
  dsimp only [bind, Except.bind, cacheRestoreEnvironment]
  change executePatternCache (extra + 252) defaultSplitLimit context [.ret cacheExpr] (storedState before context name lower upper next cache object constructor.prototype) = _
  rw [executePatternCache, terminal_return_read extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs]
  rfl

theorem execute_source_terminal (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    executePatternCache (extra + 256) defaultSplitLimit context program before =
      .ok (.returned (.array (before.base.regexp.ambient.heap.length + 1))
        (cacheWithAmbient (storedState before context name lower upper next cache object constructor.prototype)
          {(storedState before context name lower upper next cache object constructor.prototype).base.regexp.ambient with environment :=
            (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.environment})) := by
  have binding : (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.environment.lookup "match" = some (.array before.base.regexp.ambient.heap.length) := by
    change some (labelEngineValue before (LabelMatch.safeRangeLabel name lower upper)) = _
    rw [matched_value before (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) inputs.label]
  have condition := evalPatternCache_variable (extra + 252) defaultSplitLimit context (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) "match" _ binding
  change evalPatternCacheExpr (extra + 254) defaultSplitLimit context matchExpr (matchedState before context (LabelMatch.safeRangeLabel name lower upper)) = _ at condition
  rw [execute_source_prefix extra before context (LabelMatch.safeRangeLabel name lower upper) inputs.source]
  rw [executePatternCache, condition]
  simp only [bind, Except.bind, truthy, ↓reduceIte]
  rw [execute_terminal_block extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs]
  rfl


theorem terminal_frames (before : LabelMatchState) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat)
    (valid : LabelRegExp.Label (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) :
    Frames before (resultState before context name lower upper next cache object prototype) context (LabelMatch.safeRangeLabel name lower upper) lower upper := by
  have frames := label_frames before context (LabelMatch.safeRangeLabel name lower upper)
  have objects := (LabelMatch.result_contract before context.label (LabelMatch.safeRangeLabel name lower upper)).objects
  constructor
  case rangeBrands =>
    change ((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects.length, constructedRangeRecord lower upper) ::
      (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.brands = _
    change (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects = _ at objects
    rw [objects]
    simpa only [List.length_append, List.length_singleton, warmState, resetCaller, cacheWithAmbient] using congrArg (fun brands =>
      (before.base.regexp.ambient.objects.length + 1, constructedRangeRecord lower upper) :: brands) frames.rangeBrands
  case labelResults => exact frames.labelResults.1 ⟨name, some (PatternConstruct.rawBody lower upper), valid⟩
  all_goals cases frames <;> assumption

theorem terminal_contract (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    Contract before (resultState before context name lower upper next cache object constructor.prototype) context name lower upper next cache object constructor.prototype
      (.array (before.base.regexp.ambient.heap.length + 1)) := by
  have produced := LabelMatch.result_contract before context.label (LabelMatch.safeRangeLabel name lower upper)
  have heap := (produced.success name (some (PatternConstruct.rawBody lower upper)) inputs.label).2.1
  have objects := produced.objects
  change (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.heap = _ at heap
  change (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects = _ at objects
  have cacheBound := (List.getElem?_eq_some_iff.mp inputs.cacheFound).1
  have labelCount : (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects.length = before.base.regexp.ambient.objects.length + 1 := by
    rw [objects]
    simp
  constructor
  case resultValue => rfl
  case arrays =>
    change (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.heap ++
      [tupleValues (keyedState before context (LabelMatch.safeRangeLabel name lower upper) next) _ name] = _
    rw [heap]
    simp only [tupleValues, keyedState, cacheWithAmbient, labelCount, List.append_assoc, List.singleton_append]
  case objects =>
    change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++
      [initializedRegExpObject constructor.prototype]).set cache _) = _
    rw [objects]
    simp only [List.append_assoc, List.singleton_append]
  case cacheOwn =>
    have bound : cache < ((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]).length := by
      simp only [List.length_append, List.length_singleton, labelCount]
      omega
    obtain ⟨enumerable, configurable, own, proto, ext⟩ := updated_own object (key (LabelMatch.safeRangeLabel name lower upper) next) descriptor
      (.array (before.base.regexp.ambient.heap.length + 1)) inputs.writable
    exact ⟨updatedObject object _ _, enumerable, configurable, List.getElem?_set_self bound, own, proto, ext⟩
  case regexFound =>
    change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]).set cache _)[before.base.regexp.ambient.objects.length + 1]? = _
    rw [List.getElem?_set_ne (by omega), ← labelCount]
    simp
  case lastIndex => rfl
  case internal =>
    change List.lookup (before.base.regexp.ambient.objects.length + 1)
      (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects.length, _) :: _) = _
    rw [labelCount]
    simp only [List.lookup_cons, beq_self_eq_true]
  case source => rfl
  case flags => rfl
  case compiled => rfl
  case language => intro input; exact RangeRegExp.execute_anchoredPlus lower upper input
  case otherObjects =>
    intro reference different old
    change (((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects ++ [initializedRegExpObject constructor.prototype]).set cache _)[reference]? = _
    rw [List.getElem?_set_ne (Ne.symm different)]
    have bound : reference < (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.objects.length := by omega
    exact (List.getElem?_append_left bound).trans (produced.oldObjects reference old)
  case oldArrays =>
    intro reference old
    change ((matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.heap ++ [_])[reference]? = _
    have bound : reference < (matchedState before context (LabelMatch.safeRangeLabel name lower upper)).base.regexp.ambient.heap.length := by
      rw [heap]
      simp only [List.length_append, List.length_singleton]
      omega
    exact (List.getElem?_append_left bound).trans (produced.oldArrays reference old)
  case frames => exact terminal_frames before context name lower upper next cache object constructor.prototype inputs.label

/-- Actual full533B source: computed captures select source68, real constructor
initializes the regex, strict ordinary Set updates the saved cache reference,
then source74 performs its independent CURRENT Get. Source67 stays unentered. -/
theorem source_terminal_satisfies (extra : Nat) (before : LabelMatchState) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : Option JSString) (cache : Nat) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next cache object descriptor depth handle constructor prototypeObject) :
    sourceCall (extra + 256) context before = some (.ok (.array (before.base.regexp.ambient.heap.length + 1),
      resultState before context name lower upper next cache object constructor.prototype)) ∧
    Contract before (resultState before context name lower upper next cache object constructor.prototype) context name lower upper next cache object constructor.prototype
      (.array (before.base.regexp.ambient.heap.length + 1)) := by
  constructor
  · rw [sourceCall, parses_source]
    dsimp only [Option.map]
    rw [runPatternCache_restores_caller _ _ _ _ _ _ _ (execute_source_terminal extra before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs)]
    rfl
  · exact terminal_contract before context name lower upper next cache object descriptor depth handle constructor prototypeObject inputs

end HonoLean.Upstream.PatternCacheTerminal
