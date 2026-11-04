import HonoLean.Upstream.SourceSubset.LabelMatchRealm
import HonoLean.Upstream.ECMA2025.LabelRegExpRules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

def labelLiteralRecord : LabelRegExpRecord :=
  ⟨LabelRegExp.labelLiteral.drop 1 |>.take (LabelRegExp.labelLiteral.length - 2), [], LabelRegExp.labelCode⟩
def labelActualLiteral : LabelRegExpLiteral := ⟨labelLiteralRecord.source, []⟩

theorem initialize_actual_label : initializeLabelRecord labelActualLiteral = some labelLiteralRecord := by rfl

def labelFreshState (before : LabelMatchState) (context : LabelMatchContext) (record : LabelRegExpRecord) (events : List LabelEvent) : LabelMatchState :=
  {before with
    base := {before.base with regexp := {before.base.regexp with ambient := {before.base.regexp.ambient with
      objects := before.base.regexp.ambient.objects ++ [initializedRegExpObject context.regexpPrototype]}}}
    brands := (before.base.regexp.ambient.objects.length, record) :: before.brands
    trace := events}

theorem labelFresh_trace (before : LabelMatchState) (context : LabelMatchContext) (record : LabelRegExpRecord) (events : List LabelEvent) :
    (labelFreshState before context record events).trace = events := rfl

theorem labelFreshState_trace (before : LabelMatchState) (context : LabelMatchContext) (record : LabelRegExpRecord) (events next : List LabelEvent) :
    {labelFreshState before context record events with trace := next} = labelFreshState before context record next := rfl

theorem labelFreshState_before_trace (before : LabelMatchState) (context : LabelMatchContext) (record : LabelRegExpRecord) (old events : List LabelEvent) :
    labelFreshState {before with trace := old} context record events = labelFreshState before context record events := rfl

theorem label_realm_separated (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context) :
    labelTablesSeparated context before.base.regexp.ambient = true := by
  simp [labelTablesSeparated, realm.noArgBefore, realm.methodsBefore, realm.functionsBefore,
    realm.membersBefore, realm.regexpBefore, realm.constructorsBefore, realm.iteratorsBefore]

theorem label_builtin_offset (context : LabelMatchContext) (entries : context.builtins.entries = standardLabelBuiltins) (index : Nat) :
    labelBuiltinAt context.builtins (.function (context.builtins.base + index)) = standardLabelBuiltins[index]? := by
  simp [labelBuiltinAt, entries, Nat.le_add_right]

theorem label_symbol_fresh (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context) :
    before.symbols.lookup before.base.regexp.ambient.objects.length = none := by
  apply List.lookup_eq_none_iff.mpr
  intro entry member
  have bound := realm.symbolOwners entry member
  have different : before.base.regexp.ambient.objects.length ≠ entry.1 := by omega
  have unequal : (before.base.regexp.ambient.objects.length == entry.1) = false := beq_eq_false_iff_ne.mpr different
  simp [bne, unequal]

theorem label_allocate_actual (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context) :
    allocateLabelLiteral context labelActualLiteral before =
      .ok (.object before.base.regexp.ambient.objects.length,
        labelFreshState before context labelLiteralRecord
          (before.trace ++ [.literalAllocated before.base.regexp.ambient.objects.length,
            .initialized before.base.regexp.ambient.objects.length labelActualLiteral.source []])) := by
  obtain ⟨object, found, _⟩ := realm.regexpFound
  have fresh : (before.base.regexp.ambient.objects ++ [uninitializedRegExpObject context.regexpPrototype])[before.base.regexp.ambient.objects.length]? =
      some (uninitializedRegExpObject context.regexpPrototype) := by simp
  have assigned := writable_data_preserves_attributes (before.base.regexp.ambient.objects ++ [uninitializedRegExpObject context.regexpPrototype])
    before.base.regexp.ambient.objects.length (propertyFuel - 1) lastIndexKey (uninitializedRegExpObject context.regexpPrototype)
    .undefined (.number 0) false false fresh rfl
  have changed : {uninitializedRegExpObject context.regexpPrototype with
      own := putOwn lastIndexKey (.data (.number 0) true false false) (uninitializedRegExpObject context.regexpPrototype).own} =
      initializedRegExpObject context.regexpPrototype := rfl
  rw [changed] at assigned
  have replaced : (before.base.regexp.ambient.objects ++ [uninitializedRegExpObject context.regexpPrototype]).set before.base.regexp.ambient.objects.length
      (initializedRegExpObject context.regexpPrototype) = before.base.regexp.ambient.objects ++ [initializedRegExpObject context.regexpPrototype] := by simp
  rw [replaced] at assigned
  have budget : propertyFuel - 1 + 1 = propertyFuel := by decide
  rw [budget] at assigned
  simp only [allocateLabelLiteral, found, initialize_actual_label, bind, Except.bind, labelLiteralAllocated]
  rw [assigned]
  simp [Except.mapError, pure, Except.pure, labelFreshState, labelActualLiteral, List.append_assoc]

theorem label_fresh_resolve_string (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (record : LabelRegExpRecord) (events : List LabelEvent) (key : JSString) (descriptor : PropertyDescriptor)
    (notOwn : (initializedRegExpObject context.regexpPrototype).own.lookup key = none)
    (protoOwn : (standardLabelRegExpOwn context.builtins.base context.iterators.constructors.builtins.base).lookup key = some descriptor) :
    resolveLabelProperty propertyFuel (labelFreshState before context record events) before.base.regexp.ambient.objects.length (.string key) =
      .ok (some (context.regexpPrototype, descriptor)) := by
  obtain ⟨object, found, own⟩ := realm.regexpFound
  have old := (List.getElem?_eq_some_iff.mp found).1
  have appended : (labelFreshState before context record events).base.regexp.ambient.objects[context.regexpPrototype]? = some object :=
    (List.getElem?_append_left old).trans found
  have fresh : (labelFreshState before context record events).base.regexp.ambient.objects[before.base.regexp.ambient.objects.length]? =
      some (initializedRegExpObject context.regexpPrototype) := by simp [labelFreshState]
  change resolveLabelProperty (31 + 1) _ _ _ = _
  rw [resolveLabelProperty, fresh]
  dsimp only [bind, Except.bind, labelOwn]
  rw [notOwn]
  change resolveLabelProperty (30 + 1) _ _ _ = _
  rw [resolveLabelProperty, appended]
  dsimp only [bind, Except.bind, labelOwn]
  rw [own, protoOwn]
  rfl

theorem label_fresh_resolve_lastIndex (before : LabelMatchState) (context : LabelMatchContext)
    (record : LabelRegExpRecord) (events : List LabelEvent) :
    resolveLabelProperty propertyFuel (labelFreshState before context record events) before.base.regexp.ambient.objects.length (.string lastIndexKey) =
      .ok (some (before.base.regexp.ambient.objects.length, .data (.number 0) true false false)) := by
  have fresh : (labelFreshState before context record events).base.regexp.ambient.objects[before.base.regexp.ambient.objects.length]? =
      some (initializedRegExpObject context.regexpPrototype) := by simp [labelFreshState]
  change resolveLabelProperty (31 + 1) _ _ _ = _
  simp [resolveLabelProperty, fresh, labelOwn, initializedRegExpObject, bind, Except.bind, pure, Except.pure]

theorem label_fresh_resolve_symbol (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (record : LabelRegExpRecord) (events : List LabelEvent) :
    resolveLabelProperty propertyFuel (labelFreshState before context record events) before.base.regexp.ambient.objects.length (.symbol .match) =
      .ok (some (context.regexpPrototype, .data (.function (context.builtins.base + 1)) true false true)) := by
  obtain ⟨object, found, _⟩ := realm.regexpFound
  have old := (List.getElem?_eq_some_iff.mp found).1
  have appended : (labelFreshState before context record events).base.regexp.ambient.objects[context.regexpPrototype]? = some object :=
    (List.getElem?_append_left old).trans found
  have fresh : (labelFreshState before context record events).base.regexp.ambient.objects[before.base.regexp.ambient.objects.length]? =
      some (initializedRegExpObject context.regexpPrototype) := by simp [labelFreshState]
  have ownFresh : labelOwn (labelFreshState before context record events) before.base.regexp.ambient.objects.length
      (initializedRegExpObject context.regexpPrototype) (.symbol .match) = none := by
    change (before.symbols.lookup before.base.regexp.ambient.objects.length).bind _ = none
    rw [label_symbol_fresh before context realm]
    rfl
  have ownProto : labelOwn (labelFreshState before context record events) context.regexpPrototype object (.symbol .match) =
      some (.data (.function (context.builtins.base + 1)) true false true) := realm.symbol
  change resolveLabelProperty (31 + 1) _ _ _ = _
  rw [resolveLabelProperty, fresh]
  dsimp only [bind, Except.bind]
  rw [ownFresh]
  change resolveLabelProperty (30 + 1) _ _ _ = _
  rw [resolveLabelProperty, appended]
  dsimp only [bind, Except.bind]
  rw [ownProto]
  rfl

theorem label_get_string_method (fuel : Nat) (before : LabelMatchState) (context : LabelMatchContext)
    (realm : LabelRealm before context) (input : JSString) :
    getLabelProperty (fuel + 1) context (.string input) context.stringPrototype (.string labelMatchKey) before =
      .ok (.function context.builtins.base, {before with trace := before.trace ++
        [LabelEvent.get (.string input) (.string labelMatchKey) context.stringPrototype (.function context.builtins.base)]}) := by
  obtain ⟨object, found, own⟩ := realm.stringFound
  simp [getLabelProperty, resolveLabelProperty, propertyFuel, found, labelOwn, own, bind, Except.bind, pure, Except.pure]

def labelFlagEvents (context : LabelMatchContext) (reference : Nat) (flags : List LabelFlag) : List LabelEvent :=
  flags.flatMap (fun flag => [LabelEvent.getter (.function (context.builtins.base + 3 + labelFlagIndex flag)) (.object reference),
    LabelEvent.get (.object reference) (.string (labelFlagKey flag)) context.regexpPrototype (.boolean false)])

theorem label_fresh_flag (fuel : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (events : List LabelEvent) (flag : LabelFlag) :
    getLabelProperty (fuel + 3) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.string (labelFlagKey flag))
      (labelFreshState before context labelLiteralRecord events) =
      .ok (.boolean false, labelFreshState before context labelLiteralRecord
        (events ++ labelFlagEvents context before.base.regexp.ambient.objects.length [flag])) := by
  have resolved := label_fresh_resolve_string before context realm labelLiteralRecord events (labelFlagKey flag)
    (.accessor .unsupported .missing false true) (by cases flag <;> rfl) (by cases flag <;> rfl)
  have separated : labelTablesSeparated context (labelFreshState before context labelLiteralRecord events).base.regexp.ambient = true :=
    label_realm_separated before context realm
  have identity : labelBuiltinAt context.builtins (.function (context.builtins.base + 3 + labelFlagIndex flag)) = some (.flagGetter flag) := by
    have offset := label_builtin_offset context realm.builtinEntries (3 + labelFlagIndex flag)
    cases flag <;> simpa [labelFlagIndex, Nat.add_assoc, standardLabelBuiltins] using offset
  have accessor : labelAccessorAt (labelFreshState before context labelLiteralRecord events) context.regexpPrototype (.string (labelFlagKey flag)) =
      some (.function (context.builtins.base + 3 + labelFlagIndex flag)) := by
    cases flag <;> simp [labelAccessorAt, labelFreshState, realm.accessors, standardLabelAccessors, labelFlags,
      labelFlagKey, labelFlagsKey, labelFlagIndex]
  simp only [getLabelProperty, resolved, bind, Except.bind]
  rw [accessor]
  simp only [invokeLabelGetter, separated, Bool.not_true, identity, bind, Except.bind]
  simp [labelFreshState, labelLiteralRecord, labelFlagEvents, List.append_assoc, pure, Except.pure]

theorem label_fresh_flags (fuel : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (events : List LabelEvent) (flags : List LabelFlag) (enough : flags.length + 3 ≤ fuel) :
    getLabelFlags fuel context before.base.regexp.ambient.objects.length flags (labelFreshState before context labelLiteralRecord events) =
      .ok ([], labelFreshState before context labelLiteralRecord (events ++ labelFlagEvents context before.base.regexp.ambient.objects.length flags)) := by
  induction flags generalizing fuel events with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [getLabelFlags, labelFlagEvents]
  | cons flag flags ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bound : 3 ≤ fuel := by simp only [List.length_cons] at enough; omega
      have read := label_fresh_flag (fuel - 3) before context realm events flag
      have budget : fuel - 3 + 3 = fuel := by omega
      rw [budget] at read
      rw [getLabelFlags, read]
      dsimp only [bind, Except.bind]
      rw [ih fuel _ (by simp only [List.length_cons] at enough; omega)]
      simp [truthy, labelFlagEvents, List.append_assoc, pure, Except.pure]

def labelFlagsEvents (context : LabelMatchContext) (reference : Nat) : List LabelEvent :=
  [LabelEvent.getter (.function (context.builtins.base + 2)) (.object reference)] ++ labelFlagEvents context reference labelFlags ++
    [LabelEvent.get (.object reference) (.string labelFlagsKey) context.regexpPrototype (.string [])]

theorem label_fresh_get_flags (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (events : List LabelEvent) :
    getLabelProperty (extra + 16) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.string labelFlagsKey)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (.string [], labelFreshState before context labelLiteralRecord
        (events ++ labelFlagsEvents context before.base.regexp.ambient.objects.length)) := by
  have resolved := label_fresh_resolve_string before context realm labelLiteralRecord events labelFlagsKey
    (.accessor .unsupported .missing false true) (by rfl) (by rfl)
  have separated : labelTablesSeparated context (labelFreshState before context labelLiteralRecord events).base.regexp.ambient = true :=
    label_realm_separated before context realm
  have identity : labelBuiltinAt context.builtins (.function (context.builtins.base + 2)) = some .flagsGetter := by
    simpa [standardLabelBuiltins] using label_builtin_offset context realm.builtinEntries 2
  have accessor : labelAccessorAt (labelFreshState before context labelLiteralRecord events) context.regexpPrototype (.string labelFlagsKey) =
      some (.function (context.builtins.base + 2)) := by
    simp [labelAccessorAt, labelFreshState, realm.accessors, standardLabelAccessors]
  simp only [getLabelProperty, resolved, bind, Except.bind]
  rw [accessor]
  simp only [invokeLabelGetter, separated, Bool.not_true, identity, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  simp only [labelFreshState_trace, labelFresh_trace]
  rw [label_fresh_flags (extra + 14) before context realm _ labelFlags (by change 8 + 3 ≤ extra + 14; omega)]
  simp [labelFlagsEvents, labelFreshState, List.append_assoc, pure, Except.pure]

theorem label_fresh_get_exec (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (events : List LabelEvent) :
    getLabelProperty (extra + 1) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.string labelExecKey)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (.function (context.iterators.constructors.builtins.base), labelFreshState before context labelLiteralRecord
        (events ++ [LabelEvent.get (.object before.base.regexp.ambient.objects.length) (.string labelExecKey) context.regexpPrototype (.function (context.iterators.constructors.builtins.base))])) := by
  have resolved := label_fresh_resolve_string before context realm labelLiteralRecord events labelExecKey
    (.data (.function (context.iterators.constructors.builtins.base)) true false true) (by rfl) (by rfl)
  rw [getLabelProperty, resolved]
  rfl

theorem label_fresh_get_symbol (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (events : List LabelEvent) :
    getLabelProperty (extra + 1) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.symbol .match)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (.function (context.builtins.base + 1), labelFreshState before context labelLiteralRecord
        (events ++ [LabelEvent.get (.object before.base.regexp.ambient.objects.length) (.symbol .match) context.regexpPrototype (.function (context.builtins.base + 1))])) := by
  have resolved := label_fresh_resolve_symbol before context realm labelLiteralRecord events
  rw [getLabelProperty, resolved]
  rfl

theorem label_fresh_get_lastIndex (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (events : List LabelEvent) :
    getLabelProperty (extra + 1) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.string lastIndexKey)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (.number 0, labelFreshState before context labelLiteralRecord
        (events ++ [LabelEvent.get (.object before.base.regexp.ambient.objects.length) (.string lastIndexKey) before.base.regexp.ambient.objects.length (.number 0)])) := by
  rw [getLabelProperty, label_fresh_resolve_lastIndex]
  rfl

def labelEngineValue (before : LabelMatchState) (input : JSString) : Value :=
  match LabelRegExp.execute LabelRegExp.labelCode input with
  | .matched _ => .array before.base.regexp.ambient.heap.length
  | _ => .null

def labelEngineState (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) (events : List LabelEvent) : LabelMatchState :=
  let fresh := labelFreshState before context labelLiteralRecord events
  match LabelRegExp.execute LabelRegExp.labelCode input with
  | .matched matched => {fresh with
      base := {fresh.base with regexp := {fresh.base.regexp with ambient := {fresh.base.regexp.ambient with
        heap := before.base.regexp.ambient.heap ++ [labelMatchValues input matched]}}}
      results := (before.base.regexp.ambient.heap.length, ⟨matched.start, input⟩) :: before.results}
  | _ => fresh

def labelExecEvents (before : LabelMatchState) (input : JSString) : List LabelEvent :=
  [LabelEvent.toString (.string input), LabelEvent.get (.object before.base.regexp.ambient.objects.length) (.string lastIndexKey) before.base.regexp.ambient.objects.length (.number 0),
   LabelEvent.lastIndex (.number 0) 0, LabelEvent.executed before.base.regexp.ambient.objects.length]

theorem label_exec_fresh (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) (events : List LabelEvent) :
    invokeLabelExec (extra + 1) context (.object before.base.regexp.ambient.objects.length) (.string input)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (labelEngineValue before input, labelEngineState before context input (events ++ labelExecEvents before input)) := by
  have brand : (labelFreshState before context labelLiteralRecord events).brands.lookup before.base.regexp.ambient.objects.length = some labelLiteralRecord := by
    simp [labelFreshState]
  unfold invokeLabelExec
  dsimp only [bind, Except.bind]
  rw [brand]
  dsimp only [bind, Except.bind]
  rw [labelFreshState_trace]
  rw [label_fresh_get_lastIndex extra]
  dsimp only [bind, Except.bind]
  cases outcome : LabelRegExp.execute LabelRegExp.labelCode input with
  | exhausted => exact False.elim (LabelRegExp.execute_ne_exhausted _ _ outcome)
  | noMatch => simp [labelLiteralRecord, numericToLength, labelEngineValue, labelEngineState, outcome, labelExecEvents, labelFreshState, List.append_assoc, pure, Except.pure, Except.mapError]
  | matched matched => simp [labelLiteralRecord, numericToLength, labelEngineValue, labelEngineState, outcome, labelExecEvents, labelFreshState, List.append_assoc, pure, Except.pure, Except.mapError]

def labelRegExpMatchEvents (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) : List LabelEvent :=
  let receiver := Value.object before.base.regexp.ambient.objects.length
  [LabelEvent.toString (.string input)] ++ labelFlagsEvents context before.base.regexp.ambient.objects.length ++
    [LabelEvent.toString (.string []), LabelEvent.get receiver (.string labelExecKey) context.regexpPrototype (.function (context.iterators.constructors.builtins.base)),
      LabelEvent.call (.function (context.iterators.constructors.builtins.base)) receiver] ++ labelExecEvents before input

theorem label_regexp_match_fresh (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (input : JSString) (events : List LabelEvent) :
    invokeLabelRegExpMatch (extra + 128) context (.object before.base.regexp.ambient.objects.length) (.string input)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (labelEngineValue before input, labelEngineState before context input (events ++ labelRegExpMatchEvents before context input)) := by
  have flags := label_fresh_get_flags (extra + 112) before context realm (events ++ [LabelEvent.toString (.string input)])
  have budget : extra + 112 + 16 = extra + 128 := by omega
  rw [budget] at flags
  have identity : builtinAt context.iterators.constructors.builtins (.function context.iterators.constructors.builtins.base) = some .regexpExec := by
    simp [builtinAt, realm.regexpIdentity]
  unfold invokeLabelRegExpMatch
  dsimp only [bind, Except.bind]
  rw [labelFreshState_trace]
  simp only [labelFresh_trace]
  rw [flags]
  dsimp only [bind, Except.bind]
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  rw [labelFreshState_trace]
  simp only [labelFresh_trace]
  rw [label_fresh_get_exec (extra + 127) before context realm]
  dsimp only [bind, Except.bind]
  rw [identity]
  try dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [labelFreshState_trace]
  simp only [labelFresh_trace]
  rw [label_exec_fresh (extra + 127)]
  simp [labelRegExpMatchEvents, List.append_assoc]

def labelStringMatchEvents (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) : List LabelEvent :=
  let receiver := Value.object before.base.regexp.ambient.objects.length
  [LabelEvent.call (.function context.builtins.base) (.string input),
    LabelEvent.get receiver (.symbol .match) context.regexpPrototype (.function (context.builtins.base + 1)),
    LabelEvent.call (.function (context.builtins.base + 1)) receiver] ++ labelRegExpMatchEvents before context input

theorem label_string_match_fresh (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (realm : LabelRealm before context)
    (input : JSString) (events : List LabelEvent) :
    invokeLabelStringMatch (extra + 128) context (.function context.builtins.base) (.string input) (.object before.base.regexp.ambient.objects.length)
      (labelFreshState before context labelLiteralRecord events) =
      .ok (labelEngineValue before input, labelEngineState before context input (events ++ labelStringMatchEvents before context input)) := by
  have separated : labelTablesSeparated context (labelFreshState before context labelLiteralRecord events).base.regexp.ambient = true :=
    label_realm_separated before context realm
  have identity : labelBuiltinAt context.builtins (.function context.builtins.base) = some .stringMatch := by
    simpa [standardLabelBuiltins] using label_builtin_offset context realm.builtinEntries 0
  have matchIdentity : labelBuiltinAt context.builtins (.function (context.builtins.base + 1)) = some LabelBuiltin.regexpMatch := by
    simpa [standardLabelBuiltins] using label_builtin_offset context realm.builtinEntries 1
  unfold invokeLabelStringMatch
  simp only [separated, Bool.not_true, identity, bne_self_eq_false, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  rw [labelFreshState_trace]
  change (do
    let (method, after) ← getLabelProperty (extra + 128) context (.object before.base.regexp.ambient.objects.length) before.base.regexp.ambient.objects.length (.symbol .match)
      (labelFreshState before context labelLiteralRecord (events ++ [LabelEvent.call (.function context.builtins.base) (.string input)]))
    if labelBuiltinAt context.builtins method != some LabelBuiltin.regexpMatch then Except.error LabelMatchError.methodDomain else
      invokeLabelRegExpMatch (extra + 128) context (.object before.base.regexp.ambient.objects.length) (.string input)
        {after with trace := after.trace ++ [LabelEvent.call method (.object before.base.regexp.ambient.objects.length)]}) = _
  rw [label_fresh_get_symbol (extra + 127) before context realm]
  dsimp only [bind, Except.bind]
  rw [matchIdentity]
  try dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [labelFreshState_trace]
  simp only [labelFresh_trace]
  rw [label_regexp_match_fresh extra before context realm]
  simp [labelStringMatchEvents, List.append_assoc]

end HonoLean.Upstream.SourceSubset
