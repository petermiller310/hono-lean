import HonoLean.Upstream.NodeLiteralBranch.Frames

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025

theorem eval_next (extra limit : Nat) (before : State) (parent children : Nat)
    (part : JSString) (next : Value) (reads : Lookup before parent children part next) :
    evalExpression (extra + 8) limit nextLookup before = .ok (next, before) := by
  simp [nextLookup, evalExpression, lookupVariable, reads.parentBinding, reads.partBinding,
    reads.childrenRead, readProperty, reads.nextRead, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_wildcard (extra limit : Nat) (before : State) (target children : Nat) (value : Value)
    (binding : before.environment.lookup "nextNode" = some (.object target))
    (childrenRead : privateGet (.object target) "children" before = .ok (.object children))
    (read : getProperty propertyFuel before.objects children [42] = .ok value) :
    evalExpression (extra + 8) limit wildcardLookup before = .ok (value, before) := by
  simp [wildcardLookup, evalExpression, lookupVariable, binding, childrenRead, readProperty, read, Except.mapError,
    bind, Except.bind, pure, Except.pure]

theorem execute_declaration (extra limit : Nat) (before : State) (parent children : Nat)
    (part : JSString) (next : Value) (reads : Lookup before parent children part next) :
    execute (extra + 10) limit [.declare "nextNode" nextLookup] before =
      .ok (.normal (declaredState before next)) := by
  have evaluated := eval_next (extra + 1) limit before parent children part next reads
  rw [show extra + 10 = (extra + 9) + 1 by omega, execute, evaluated]
  simp [execute, declaredState, bind, Except.bind]

theorem writable_declared (before : State) (target identity : Nat) (old next : Value)
    (writable : NodePrivateWrite.Writable before target identity old) :
    NodePrivateWrite.Writable (declaredState before next) target identity old :=
  ⟨writable.scope, writable.allocated, writable.data⟩

def writtenState (before : State) (target stamp nodeParams : Nat) : State :=
  writePrivateDataState (declaredState before (.object target)) target (stamp + 4) (.object nodeParams)

theorem execute_propagation (extra limit : Nat) (before : State)
    (parent children target receiver stamp collector temp nodeParams : Nat)
    (part query : JSString) (last old : Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old) :
    execute (extra + 34) limit [.assign NodePrivateWrite.propagation] (declaredState before (.object target)) =
      .ok (.normal (writtenState before target stamp nodeParams)) := by
  have writable := writable_declared before target (stamp + 4) old (.object target) entry.writable
  have setter := NodePrivateWrite.setter (declaredState before (.object target)) target (stamp + 4) old (.object nodeParams) writable
  have targetBinding : (declaredState before (.object target)).environment.lookup "nextNode" = some (.object target) := by simp [declaredState]
  have parentBinding : (declaredState before (.object target)).environment.lookup "node" = some (.object parent) := by
    simpa [declaredState, List.lookup] using entry.lookup.parentBinding
  have parentRead : privateGet (.object parent) "params" (declaredState before (.object target)) = .ok (.object nodeParams) := entry.parentRead
  have assignment : executeAssignment (extra + 33) limit NodePrivateWrite.propagation (declaredState before (.object target)) =
      .ok (.object nodeParams, writtenState before target stamp nodeParams) := by
    simp [executeAssignment, NodePrivateWrite.propagation, evalAssignmentReference, evalExpression,
      lookupVariable, targetBinding, writable.scope, parentBinding, parentRead,
      putAssignmentReference, setter, writtenState, bind, Except.bind, pure, Except.pure]
  rw [show extra + 34 = (extra + 33) + 1 by omega, execute, assignment]
  simp [execute, bind, Except.bind]

theorem propagation_contract (before : State)
    (parent children target receiver stamp collector temp nodeParams : Nat)
    (part query : JSString) (last old : Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old) :
    NodePrivateWrite.WriteContract (declaredState before (.object target))
      (writtenState before target stamp nodeParams) target (stamp + 4) old (.object nodeParams) (.object nodeParams) :=
  NodePrivateWrite.write_contract _ target (stamp + 4) old (.object nodeParams)
    (writable_declared before target (stamp + 4) old (.object target) entry.writable)

theorem storage_after_propagation (before : State) (closure : PrivateMethodClosure)
    (target other stamp methods collector nodeParams : Nat) (rows : List Value) (old : Value)
    (writable : NodePrivateWrite.Writable before target (stamp + 4) old)
    (storage : NodePrivateCall.Storage before closure other stamp methods collector rows) :
    NodePrivateCall.Storage (writtenState before target stamp nodeParams) closure other stamp methods collector rows := by
  by_cases same : other = target
  · subst other
    exact NodePrivateWrite.storage_after_params (declaredState before (.object target)) closure target stamp methods collector rows old
      (.object nodeParams) (writable_declared before target (stamp + 4) old (.object target) writable)
      ⟨storage.targetFound, storage.privateName, storage.privateSlot, storage.methodsFound, storage.separate, storage.legalLength⟩
  · obtain ⟨fields, brand, field⟩ := storage.privateSlot
    refine ⟨storage.targetFound, storage.privateName, ⟨fields, ?_, field⟩, storage.methodsFound, storage.separate, storage.legalLength⟩
    rw [writtenState, writePrivateDataState_other_owner _ target (stamp + 4) other (.object nodeParams) same]
    exact brand

theorem children_after_propagation (before : State) (target stamp children nodeParams : Nat) (old : Value)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before target (stamp + 4) old)
    (read : privateGet (.object target) "children" before = .ok (.object children)) :
    privateGet (.object target) "children" (writtenState before target stamp nodeParams) = .ok (.object children) := by
  obtain ⟨raw, brand, _⟩ := writable.data
  rw [writtenState, privateGet_write_other_identity (declaredState before (.object target)) target (stamp + 4) (stamp + 1) (.object nodeParams)
    "children" raw ?_ brand (by omega)]
  · exact read
  · simp [declaredState, scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]

theorem parent_after_propagation (before : State) (parent target stamp nodeParams : Nat) (old : Value)
    (writable : NodePrivateWrite.Writable before target (stamp + 4) old)
    (read : privateGet (.object parent) "params" before = .ok (.object nodeParams)) :
    privateGet (.object parent) "params" (writtenState before target stamp nodeParams) = .ok (.object nodeParams) :=
  NodePrivateWrite.parent_read_after_propagation (declaredState before (.object target)) target parent (stamp + 4)
    old (.object nodeParams) (writable_declared before target (stamp + 4) old (.object target) writable) read

theorem callable_after_propagation (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target receiver stamp handle nodeParams : Nat) (old : Value)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before target (stamp + 4) old)
    (callable : NodePrivateCall.Callable before table closure receiver handle) :
    NodePrivateCall.Callable (writtenState before target stamp nodeParams) table closure receiver handle :=
  NodePrivateWrite.callable_after_params (declaredState before (.object target)) table closure target receiver stamp handle
    old (.object nodeParams) scope (writable_declared before target (stamp + 4) old (.object target) writable)
    ⟨callable.sourceProgram, callable.tableSeparate, callable.handleBound, callable.closureFound, callable.privateRead⟩

theorem eval_wildcard_arguments (extra : Nat) (before : State) (parent target children collector : Nat)
    (query : JSString) (nodeParams wildcardTarget : Nat)
    (collectorBinding : before.environment.lookup "handlerSets" = some (.array collector))
    (targetBinding : before.environment.lookup "nextNode" = some (.object target))
    (methodBinding : before.environment.lookup "method" = some (.string query))
    (parentBinding : before.environment.lookup "node" = some (.object parent))
    (childrenRead : privateGet (.object target) "children" before = .ok (.object children))
    (wildcardRead : getProperty propertyFuel before.objects children [42] = .ok (.object wildcardTarget))
    (parentRead : privateGet (.object parent) "params" before = .ok (.object nodeParams)) :
    evalArguments (extra + 12) defaultSplitLimit wildcardCall.arguments before =
      .ok (NodePrivateCall.fourValues collector wildcardTarget query nodeParams, before) := by
  simp [wildcardCall, wildcardLookup, NodePrivateCall.fourValues, evalArguments, evalExpression, lookupVariable,
    collectorBinding, targetBinding, methodBinding, parentBinding, childrenRead, readProperty, wildcardRead, parentRead, Except.mapError,
    bind, Except.bind, pure, Except.pure]

theorem actual_call_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle target stamp methods collector keyBound : Nat) (rows : List Value)
    (query : JSString) (nodeParams : Nat) (records : List MethodsLoopInitial.Record) (initial : List Value)
    (arguments : List Expr)
    (callable : NodePrivateCall.Callable before table closure receiver handle)
    (evaluated : evalArguments (rows.length + keyBound + 103) defaultSplitLimit arguments before =
      .ok (NodePrivateCall.fourValues collector target query nodeParams, before))
    (storage : NodePrivateCall.Storage before closure target stamp methods collector rows)
    (layout : MethodsLoopInitial.Layout (NodePrivateCall.bodyState before closure (.object receiver)
      collector target query nodeParams .undefined) rows query collector keyBound records .undefined nodeParams initial) :
    ∃ after,
      runPrivateMethodCall (rows.length + keyBound + 103) defaultSplitLimit table ⟨.object receiver⟩
        ⟨.this, "pushHandlerSets", arguments⟩ before = .ok (.undefined, after) ∧
      NodePrivateCall.CallContract before
        (NodePrivateCall.bodyState before closure (.object receiver) collector target query nodeParams .undefined)
        rows query collector .undefined after := by
  obtain ⟨bodyAfter, bodyRun, contract⟩ := NodePrivateCall.body_satisfies before closure (.object receiver) target stamp methods collector
    keyBound rows query nodeParams .undefined records initial storage layout
  have call := runPrivateMethodCall_this (rows.length + keyBound + 103) defaultSplitLimit table (.object receiver)
    "pushHandlerSets" arguments before before (NodePrivateCall.fourValues collector target query nodeParams)
    handle closure callable.tableSeparate callable.privateRead evaluated callable.handleBound callable.closureFound
  have normal : runBlock (rows.length + keyBound + 103) closure.program.body
      (methodActivation closure (.object receiver) (NodePrivateCall.fourValues collector target query nodeParams) before).state =
        .ok (.normal bodyAfter) := by
    rw [NodePrivateCall.four_activation before closure (.object receiver) collector target query nodeParams callable.sourceProgram,
      callable.sourceProgram]
    exact bodyRun
  rw [invokePrivateClosure_normal _ _ _ _ _ _ _ normal] at call
  exact ⟨restoreMethodCaller before bodyAfter, call, rfl, bodyAfter, contract, rfl⟩

end HonoLean.Upstream.NodeLiteralBranch
