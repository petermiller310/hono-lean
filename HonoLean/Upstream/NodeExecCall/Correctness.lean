import HonoLean.Upstream.NodeExecCall.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeExecCall
open SourceSubset ECMA2025

theorem current_exec (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString)
    (inputs : Inputs before methods functions members closure matcher handle input) :
    prepareMethod (.object matcher) "exec" before = .ok (.member (.object matcher) (.function handle)) := by
  obtain ⟨writable, enumerable, configurable, depth, path, bound⟩ := inputs.current
  have resolved := NodeCaptureGuard.descriptor_path_lookup before.objects execKey matcher _ depth propertyFuel path bound
  change ((getProperty propertyFuel before.objects matcher execKey).mapError EvalError.objectError).map (PreparedMethod.member (.object matcher)) = _
  unfold getProperty
  rw [resolved]
  rfl

theorem tables_separated (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString)
    (inputs : Inputs before methods functions members closure matcher handle input) :
    memberTableSeparated methods functions members before = true := by
  simp [memberTableSeparated, inputs.noArgBefore, inputs.privateBefore, inputs.functionsBefore]

theorem body_admitted (closure : MemberClosure) (shape : BodyShape)
    (program : closure.program.body = shapeBody shape closure.program.parameter) : memberBodyAdmitted closure = true := by
  unfold memberBodyAdmitted
  rw [program]
  cases shape <;> rfl

/-- The source-defined body is executed on the original receiver and actual
argument. In particular singleton does real array allocation and element
creation, and normal fallthrough produces undefined rather than a fake match. -/
theorem invoke_shape (extra : Nat) (before : State) (closure : MemberClosure) (matcher : Nat) (input : JSString) (shape : BodyShape)
    (program : closure.program.body = shapeBody shape closure.program.parameter) :
    invokeMemberClosure (extra + 20) defaultSplitLimit closure (.object matcher) [.string input] before =
      .ok (returnedValue shape before matcher input, callState shape before input) := by
  have admitted := body_admitted closure shape program
  unfold invokeMemberClosure
  rw [admitted]
  simp only [Bool.not_true]
  cases shape <;>
    simp [runBlock, program, shapeBody, declaredNames, execute, evalExpression, evalLiteralElements, appendLiteralElements,
      memberActivation, restoreMemberCaller, restoreCompletion, lookupVariable, withoutBindings, returnedValue, returnedHeap,
      callState, List.set_append_right, bind, Except.bind, pure, Except.pure]

theorem result_contract (extra : Nat) (before : State) (closure : MemberClosure) (matcher handle : Nat) (input : JSString) (shape : BodyShape)
    (program : closure.program.body = shapeBody shape closure.program.parameter)
    (receiverEval : evalExpression (extra + 20) defaultSplitLimit receiver before = .ok (.object matcher, before))
    (callee : prepareMethod (.object matcher) "exec" before = .ok (.member (.object matcher) (.function handle)))
    (argumentEval : evalArguments (extra + 20) defaultSplitLimit arguments before = .ok ([.string input], before)) :
    Contract (extra + 20) before (resultState shape before matcher input) closure matcher handle input shape := by
  have invoked := invoke_shape extra before closure matcher input shape program
  refine ⟨program, ⟨receiverEval, callee, argumentEval, (invokeMemberClosure_iff _ _ _ _ _ _ _ _).mp invoked⟩,
    rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro reference inside
  cases shape <;> simp [resultState, callState, returnedHeap, List.getElem?_append_left inside]

/-- Exact51B source156 executes the CURRENT data callee's actual source body.
No match value, future m binding, successful invocation or body run is an input.
These source-defined examples do not yet implement builtin RegExp execution. -/
theorem source_exec_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString) (shape : BodyShape)
    (inputs : Inputs before methods functions members closure matcher handle input)
    (programBody : closure.program.body = shapeBody shape closure.program.parameter) :
    sourceExec (extra + 20) methods functions members before = some (.ok (resultState shape before matcher input)) ∧
      Contract (extra + 20) before (resultState shape before matcher input) closure matcher handle input shape := by
  have receiverEval : evalExpression (extra + 20) defaultSplitLimit receiver before = .ok (.object matcher, before) := by
    simp [receiver, evalExpression, lookupVariable, inputs.matcherBinding]
    rfl
  have argumentEval : evalArguments (extra + 20) defaultSplitLimit arguments before = .ok ([.string input], before) := by
    simp [arguments, evalArguments, evalExpression, lookupVariable, inputs.inputBinding, bind, Except.bind, pure, Except.pure]
  have callee := current_exec before methods functions members closure matcher handle input inputs
  have resolved := runMemberCall_resolved (extra + 20) defaultSplitLimit methods functions members receiver "exec" arguments before before before
    (.object matcher) handle [.string input] closure receiverEval callee argumentEval (tables_separated before methods functions members closure matcher handle input inputs)
    inputs.handleBound inputs.closureFound
  have invoked := invoke_shape extra before closure matcher input shape programBody
  rw [invoked] at resolved
  have executed := executeMemberDeclaration_call (extra + 20) defaultSplitLimit methods functions members "m" "exec" receiver (.variable "restPathString") before
    (callState shape before input) (returnedValue shape before matcher input) resolved
  exact ⟨by simpa [sourceExec, parses_source, program, resultState, arguments, callState] using congrArg some executed,
    result_contract extra before closure matcher handle input shape programBody receiverEval callee argumentEval⟩

theorem produced_guard_test (extra : Nat) (before : State) (matcher : Nat) (input : JSString) (shape : BodyShape) :
    evalExpression (extra + 1) defaultSplitLimit guardCondition (resultState shape before matcher input) =
      .ok (returnedValue shape before matcher input, resultState shape before matcher input) ∧
    truthy (returnedValue shape before matcher input) = resultTruthy shape input := by
  constructor
  · simp [guardCondition, evalExpression, lookupVariable, resultState]
    rfl
  · cases shape <;> rfl

/-- info: 'HonoLean.Upstream.NodeExecCall.source_exec_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_exec_satisfies
/-- info: 'HonoLean.Upstream.NodeExecCall.invoke_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invoke_shape
/-- info: 'HonoLean.Upstream.NodeExecCall.produced_guard_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms produced_guard_test

end HonoLean.Upstream.NodeExecCall
