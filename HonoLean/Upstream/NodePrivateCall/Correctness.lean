import HonoLean.Upstream.NodePrivateCall.Contract

namespace HonoLean.Upstream.NodePrivateCall

open SourceSubset ECMA2025

theorem four_activation (before : State) (closure : PrivateMethodClosure) (receiver : Value)
    (collector target : Nat) (method : JSString) (nodeParams : Nat)
    (source : closure.program = methodProgram) :
    (methodActivation closure receiver (fourValues collector target method nodeParams) before).state =
      bodyState before closure receiver collector target method nodeParams .undefined := by
  simp [methodActivation, parameterBindings, source, methodProgram, fourValues, bodyState]

theorem five_activation (before : State) (closure : PrivateMethodClosure) (receiver : Value)
    (collector target : Nat) (method : JSString) (nodeParams : Nat) (parameterReceiver : Value)
    (source : closure.program = methodProgram) :
    (methodActivation closure receiver (fiveValues collector target method nodeParams parameterReceiver) before).state =
      bodyState before closure receiver collector target method nodeParams parameterReceiver := by
  simp [methodActivation, parameterBindings, source, methodProgram, fiveValues, bodyState]

theorem body_inputs (before : State) (closure : PrivateMethodClosure) (receiver : Value)
    (target stamp methods collector : Nat) (rows : List Value) (method : JSString)
    (nodeParams : Nat) (parameterReceiver : Value)
    (storage : Storage before closure target stamp methods collector rows) :
    MethodsLoop.Inputs (bodyState before closure receiver collector target method nodeParams parameterReceiver)
      target stamp methods collector rows method := by
  exact ⟨rfl, rfl, storage.targetFound, storage.privateName, storage.privateSlot,
    storage.methodsFound, storage.separate, storage.legalLength⟩

theorem eval_four_arguments (extra : Nat) (before : State) (collector target : Nat)
    (method : JSString) (nodeParams : Nat) (reads : FourReads before collector target method nodeParams) :
    evalArguments (extra + 8) defaultSplitLimit fourCall.arguments before =
      .ok (fourValues collector target method nodeParams, before) := by
  obtain ⟨callerNode, bound, read⟩ := reads.callerNode
  simp [fourCall, fourValues, evalArguments, evalExpression, lookupVariable,
    reads.collectorBinding, reads.targetBinding, reads.methodBinding, bound, read,
    bind, Except.bind, pure, Except.pure]

theorem eval_five_arguments (extra : Nat) (before : State) (collector target : Nat)
    (method : JSString) (nodeParams : Nat) (parameterReceiver : Value)
    (reads : FiveReads before collector target method nodeParams parameterReceiver) :
    evalArguments (extra + 8) defaultSplitLimit fiveCall.arguments before =
      .ok (fiveValues collector target method nodeParams parameterReceiver, before) := by
  obtain ⟨callerNode, bound, read⟩ := reads.callerNode
  simp [fiveCall, fiveValues, evalArguments, evalExpression, lookupVariable,
    reads.collectorBinding, reads.targetBinding, reads.methodBinding, reads.parameterBinding, bound, read,
    bind, Except.bind, pure, Except.pure]

/-- The initial protected layout supplies structural reads and frames, never a
completed loop or future successful execution. Parameter bindings have already
been derived from the source declaration and argument expressions. -/
theorem body_satisfies (before : State) (closure : PrivateMethodClosure) (receiver : Value)
    (target stamp methods collector keyBound : Nat) (rows : List Value) (method : JSString)
    (nodeParams : Nat) (parameterReceiver : Value) (records : List MethodsLoopInitial.Record)
    (initial : List Value)
    (storage : Storage before closure target stamp methods collector rows)
    (layout : MethodsLoopInitial.Layout
      (bodyState before closure receiver collector target method nodeParams parameterReceiver)
      rows method collector keyBound records parameterReceiver nodeParams initial) :
    ∃ after,
      runBlock (rows.length + keyBound + 103) MethodsLoop.program
        (bodyState before closure receiver collector target method nodeParams parameterReceiver) = .ok (.normal after) ∧
      MethodsLoop.LoopContract (bodyState before closure receiver collector target method nodeParams parameterReceiver)
        after rows method collector := by
  obtain ⟨after, run, contract⟩ := MethodsLoopInitial.parsed_initial_satisfies target stamp methods
    (body_inputs before closure receiver target stamp methods collector rows method nodeParams parameterReceiver storage) layout
  rw [MethodsLoop.parses_source] at run
  exact ⟨after, Option.some.inj run, contract⟩

theorem parsed_closure_source (closure : PrivateMethodClosure)
    (source : closure.program = methodProgram) :
    parsePrivateMethod pinnedMethodSource lexicalBindings classPrivateNames = some closure.program := by
  rw [source, parses_method]

/-- Actual four-argument call: the omitted fifth formal is derived as undefined.
The receiver/brand and captured closure are explicit initial reads; the initial
layout contains no completed body execution, selected result or future Entry. -/
theorem parsed_four_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle target stamp methods collector keyBound : Nat) (rows : List Value)
    (method : JSString) (nodeParams : Nat) (records : List MethodsLoopInitial.Record) (initial : List Value)
    (callable : Callable before table closure receiver handle)
    (reads : FourReads before collector target method nodeParams)
    (storage : Storage before closure target stamp methods collector rows)
    (layout : MethodsLoopInitial.Layout (bodyState before closure (.object receiver) collector target method nodeParams .undefined)
      rows method collector keyBound records .undefined nodeParams initial) :
    parsePrivateMethod pinnedMethodSource lexicalBindings classPrivateNames = some closure.program ∧
    ∃ after,
      (parsePrivateMethodCall pinnedFourSource fourBindings classPrivateNames).map
        (fun call => runPrivateMethodCall (rows.length + keyBound + 103) defaultSplitLimit table
          ⟨.object receiver⟩ call before) = some (.ok (.undefined, after)) ∧
      CallContract before (bodyState before closure (.object receiver) collector target method nodeParams .undefined)
        rows method collector .undefined after := by
  refine ⟨parsed_closure_source closure callable.sourceProgram, ?_⟩
  obtain ⟨bodyAfter, bodyRun, contract⟩ := body_satisfies before closure (.object receiver) target stamp methods collector keyBound
    rows method nodeParams .undefined records initial storage layout
  have arguments : evalArguments (rows.length + keyBound + 103) defaultSplitLimit fourCall.arguments before =
      .ok (fourValues collector target method nodeParams, before) := by
    simpa [Nat.add_assoc] using eval_four_arguments (rows.length + keyBound + 95) before collector target method nodeParams reads
  have call := runPrivateMethodCall_this (rows.length + keyBound + 103) defaultSplitLimit table
    (.object receiver) "pushHandlerSets" fourCall.arguments before before
    (fourValues collector target method nodeParams) handle closure callable.tableSeparate
    callable.privateRead arguments callable.handleBound callable.closureFound
  have normal : runBlock (rows.length + keyBound + 103) closure.program.body
      (methodActivation closure (.object receiver) (fourValues collector target method nodeParams) before).state =
        .ok (.normal bodyAfter) := by
    rw [four_activation before closure (.object receiver) collector target method nodeParams callable.sourceProgram,
      callable.sourceProgram]
    exact bodyRun
  rw [invokePrivateClosure_normal _ _ _ _ _ _ _ normal] at call
  refine ⟨restoreMethodCaller before bodyAfter, ?_, rfl, bodyAfter, contract, rfl⟩
  rw [parses_four, Option.map_some]
  exact congrArg some call

/-- Actual parameter-branch call reverses the two parameter sources: source
`params` binds nodeParams, while source `node.#params` binds the fifth formal.
This theorem follows that positional behavior rather than renaming it away. -/
theorem parsed_five_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle target stamp methods collector keyBound : Nat) (rows : List Value)
    (method : JSString) (nodeParams : Nat) (parameterReceiver : Value)
    (records : List MethodsLoopInitial.Record) (initial : List Value)
    (callable : Callable before table closure receiver handle)
    (reads : FiveReads before collector target method nodeParams parameterReceiver)
    (storage : Storage before closure target stamp methods collector rows)
    (layout : MethodsLoopInitial.Layout (bodyState before closure (.object receiver) collector target method nodeParams parameterReceiver)
      rows method collector keyBound records parameterReceiver nodeParams initial) :
    parsePrivateMethod pinnedMethodSource lexicalBindings classPrivateNames = some closure.program ∧
    ∃ after,
      (parsePrivateMethodCall pinnedFiveSource fiveBindings classPrivateNames).map
        (fun call => runPrivateMethodCall (rows.length + keyBound + 103) defaultSplitLimit table
          ⟨.object receiver⟩ call before) = some (.ok (.undefined, after)) ∧
      CallContract before (bodyState before closure (.object receiver) collector target method nodeParams parameterReceiver)
        rows method collector .undefined after := by
  refine ⟨parsed_closure_source closure callable.sourceProgram, ?_⟩
  obtain ⟨bodyAfter, bodyRun, contract⟩ := body_satisfies before closure (.object receiver) target stamp methods collector keyBound
    rows method nodeParams parameterReceiver records initial storage layout
  have arguments : evalArguments (rows.length + keyBound + 103) defaultSplitLimit fiveCall.arguments before =
      .ok (fiveValues collector target method nodeParams parameterReceiver, before) := by
    simpa [Nat.add_assoc] using eval_five_arguments (rows.length + keyBound + 95) before collector target method nodeParams parameterReceiver reads
  have call := runPrivateMethodCall_this (rows.length + keyBound + 103) defaultSplitLimit table
    (.object receiver) "pushHandlerSets" fiveCall.arguments before before
    (fiveValues collector target method nodeParams parameterReceiver) handle closure callable.tableSeparate
    callable.privateRead arguments callable.handleBound callable.closureFound
  have normal : runBlock (rows.length + keyBound + 103) closure.program.body
      (methodActivation closure (.object receiver) (fiveValues collector target method nodeParams parameterReceiver) before).state =
        .ok (.normal bodyAfter) := by
    rw [five_activation before closure (.object receiver) collector target method nodeParams parameterReceiver callable.sourceProgram,
      callable.sourceProgram]
    exact bodyRun
  rw [invokePrivateClosure_normal _ _ _ _ _ _ _ normal] at call
  refine ⟨restoreMethodCaller before bodyAfter, ?_, rfl, bodyAfter, contract, rfl⟩
  rw [parses_five, Option.map_some]
  exact congrArg some call

/-- info: 'HonoLean.Upstream.NodePrivateCall.parsed_four_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_four_satisfies

/-- info: 'HonoLean.Upstream.NodePrivateCall.parsed_five_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_five_satisfies

end HonoLean.Upstream.NodePrivateCall
