import HonoLean.Upstream.NodeRegExpExec.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeRegExpExec
open SourceSubset ECMA2025

theorem initialized_record (record : RangeRegExpRecord) (initialized : initializeRangeRecord digitsPattern [] = some record) : record = digitsRecord :=
  (Option.some.inj (initialize_digits.symm.trans initialized)).symm

theorem tables_separated (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable) :
    regExpTablesSeparated methods functions members builtins before.ambient = true := by
  have memberBound : members.base ≤ builtins.base := by have := inputs.membersBeforeBuiltin; omega
  have noArg : before.ambient.functions.length ≤ builtins.base := Nat.le_trans inputs.noArgBeforeMember memberBound
  have privateRange : methods.base + methods.entries.length ≤ builtins.base := Nat.le_trans inputs.privateBeforeMember memberBound
  have functionRange : functions.base + functions.entries.length ≤ builtins.base := Nat.le_trans inputs.functionsBeforeMember memberBound
  simp [regExpTablesSeparated, memberTableSeparated, inputs.noArgBeforeMember, inputs.privateBeforeMember, inputs.functionsBeforeMember,
    noArg, privateRange, functionRange, inputs.membersBeforeBuiltin]

theorem current_builtin (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable) :
    prepareMethod (.object matcher) "exec" before.ambient = .ok (.member (.object matcher) (.function handle)) := by
  obtain ⟨write, enumerable, configurable, depth, path, bound⟩ := inputs.current
  have resolved := NodeCaptureGuard.descriptor_path_lookup before.ambient.objects NodeExecCall.execKey matcher _ depth propertyFuel path bound
  change ((getProperty propertyFuel before.ambient.objects matcher NodeExecCall.execKey).mapError EvalError.objectError).map (PreparedMethod.member (.object matcher)) = _
  unfold getProperty
  rw [resolved]
  rfl

theorem builtin_computes (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable) :
    invokeRegExpExec (.object matcher) [.string input] before = .ok (returnedValue before input, callState before input) := by
  exact invokeRegExpExec_range before matcher record object input [] last writable 48 57 inputs.brand inputs.objectFound inputs.lastIndex inputs.numericBound
    (by rw [initialized_record record inputs.initialized]; rfl) (by rw [initialized_record record inputs.initialized]; rfl)

theorem result_contract (extra : Nat) (before : RegExpCallState) (matcher handle : Nat) (input : JSString)
    (object : OrdinaryObject) (last : Int) (writable : Bool) (phases : CallPhases (extra + 20) before matcher handle input)
    (found : before.ambient.objects[matcher]? = some object) (lastIndex : object.own.lookup lastIndexKey = some (.data (.number last) writable false false)) :
    Contract (extra + 20) before (resultState before input) matcher handle input object last writable := by
  have language : DigitsLanguage input ↔ RangeRegExp.Accepted 48 57 input := Iff.rfl
  refine ⟨phases, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases accepted : DigitsLanguage input <;> simp [returnedValue, rangeExecValue, ← language, accepted]
  · intro accepted
    have admitted := language.mp accepted
    simp [resultState, callState, rangeExecState, admitted, observeRegExpResult, observeRegExpMatch]
  · intro rejected
    have absent : ¬ RangeRegExp.Accepted 48 57 input := fun accepted => rejected (language.mpr accepted)
    simp [returnedValue, rangeExecValue, resultState, callState, rangeExecState, absent]
  · intro reference inside
    by_cases accepted : RangeRegExp.Accepted 48 57 input <;> simp [resultState, callState, rangeExecState, accepted, List.getElem?_append_left inside]
  all_goals first
    | exact ⟨by simpa [resultState, callState, rangeExecState] using found, lastIndex⟩
    | (by_cases accepted : RangeRegExp.Accepted 48 57 input <;> simp [resultState, callState, rangeExecState, accepted])
  all_goals exact ⟨found, lastIndex⟩

/-- Exact source156 now executes the genuine parsed/compiled builtin branch.
The input contains no m/match result, desired VM output or future success. -/
theorem source_exec_satisfies (extra : Nat) (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool)
    (inputs : Inputs before methods functions members builtins matcher handle input record object last writable) :
    sourceExec (extra + 20) methods functions members builtins before = some (.ok (resultState before input)) ∧
      Contract (extra + 20) before (resultState before input) matcher handle input object last writable := by
  have receiverEval : evalExpression (extra + 20) defaultSplitLimit NodeExecCall.receiver before.ambient = .ok (.object matcher, before.ambient) := by
    simp [NodeExecCall.receiver, evalExpression, lookupVariable, inputs.matcherBinding]
    rfl
  have argumentEval : evalArguments (extra + 20) defaultSplitLimit NodeExecCall.arguments before.ambient = .ok ([.string input], before.ambient) := by
    simp [NodeExecCall.arguments, evalArguments, evalExpression, lookupVariable, inputs.inputBinding, bind, Except.bind, pure, Except.pure]
  have prepared := current_builtin before methods functions members builtins matcher handle input record object last writable inputs
  have builtin : builtinAt builtins (.function handle) = some .regexpExec := by
    simp [builtinAt, inputs.handleBound, inputs.identity]
  have called := runRegExpCall_builtin (extra + 20) defaultSplitLimit methods functions members builtins NodeExecCall.receiver "exec" NodeExecCall.arguments
    before before.ambient before.ambient (.object matcher) (.function handle) [.string input] receiverEval prepared argumentEval
    (tables_separated before methods functions members builtins matcher handle input record object last writable inputs) builtin
  have computed := builtin_computes before methods functions members builtins matcher handle input record object last writable inputs
  have unchanged : {before with ambient := before.ambient} = before := rfl
  rw [unchanged, computed] at called
  have executed := executeRegExpDeclaration_call (extra + 20) defaultSplitLimit methods functions members builtins "m" "exec" NodeExecCall.receiver (.variable "restPathString")
    before (callState before input) (returnedValue before input) called
  have environment : (callState before input).ambient.environment = before.ambient.environment := by
    by_cases accepted : RangeRegExp.Accepted 48 57 input <;> simp [callState, rangeExecState, accepted]
  refine ⟨?_, result_contract extra before matcher handle input object last writable ⟨receiverEval, prepared, argumentEval, computed⟩ inputs.objectFound inputs.lastIndex⟩
  simpa [sourceExec, parses_source, program, NodeExecCall.program, NodeExecCall.arguments, resultState, environment] using congrArg some executed

theorem produced_guard_test (extra : Nat) (before : RegExpCallState) (input : JSString) :
    evalExpression (extra + 1) defaultSplitLimit guardCondition (resultState before input).ambient =
      .ok (returnedValue before input, (resultState before input).ambient) ∧
    (truthy (returnedValue before input) = true ↔ DigitsLanguage input) := by
  constructor
  · simp [guardCondition, NodeExecCall.guardCondition, evalExpression, lookupVariable, resultState]
    rfl
  · change (truthy (if DigitsLanguage input then .array before.ambient.heap.length else .null) = true ↔ DigitsLanguage input)
    by_cases accepted : DigitsLanguage input <;> simp [accepted]

/-- info: 'HonoLean.Upstream.NodeRegExpExec.source_exec_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_exec_satisfies
/-- info: 'HonoLean.Upstream.NodeRegExpExec.builtin_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms builtin_computes
/-- info: 'HonoLean.Upstream.NodeRegExpExec.produced_guard_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms produced_guard_test

end HonoLean.Upstream.NodeRegExpExec
