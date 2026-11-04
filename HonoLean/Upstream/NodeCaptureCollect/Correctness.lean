import HonoLean.Upstream.NodeCaptureCollect.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeCaptureCollect
open SourceSubset ECMA2025 MethodsLoopInitial

theorem installed_callable (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure) (receiver handle : Nat)
    (installed : Installed before table closure receiver handle) : NodePrivateCall.Callable before table closure receiver handle := by
  obtain ⟨object, found⟩ := installed.receiverFound
  obtain ⟨fields, brand, method⟩ := installed.method
  refine ⟨installed.source, installed.separate, installed.handleBound, installed.closureFound, ?_⟩
  apply privateGet_field before receiver installed.identity "pushHandlerSets" object _ (.function handle) installed.scope found
  · rw [PrivateStore.slots_lookup, brand]
    rfl
  · rw [lookup_map_values, method]
    rfl

theorem actual_storage (before : State) (closure : PrivateMethodClosure) (child slot methods collector : Nat) (rows : List Value)
    (stored : Storage before closure child slot methods collector rows) : NodePrivateCall.Storage before closure child slot methods collector rows := by
  obtain ⟨fields, brand, field⟩ := stored.data
  refine ⟨stored.childFound, stored.scope, ⟨fields.map (fun (key, value) => (key, value.value)), ?_, ?_⟩,
    stored.rowsFound, stored.separate, stored.legal⟩
  · rw [PrivateStore.slots_lookup, brand]
    rfl
  · rw [lookup_map_values, field]
    rfl

theorem eval_arguments (extra : Nat) (before : State) (receiver node parentIdentity child collector parent q : Nat) (query : JSString)
    (reads : CallReads before receiver node parentIdentity child collector parent q query) :
    evalArguments (extra + 8) defaultSplitLimit call.arguments before = .ok (NodePrivateCall.fiveValues collector child query parent (.object q), before) := by
  have parentRead := NodeParamsInit.writable_read before node parentIdentity parent reads.parentData
  simp [call, NodePrivateCall.fiveValues, evalArguments, evalExpression, lookupVariable, reads.collectorBinding, reads.childBinding,
    reads.methodBinding, reads.nodeBinding, reads.paramsBinding, parentRead, bind, Except.bind, pure, Except.pure]

theorem contract_of_call (before after : State) (closure : PrivateMethodClosure) (receiver child slot methods collector parent q : Nat)
    (rows initial : List Value) (query : JSString)
    (stored : NodePrivateCall.Storage before closure child slot methods collector rows)
    (collectorFound : before.heap[collector]? = some initial)
    (called : NodePrivateCall.CallContract before (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q)) rows query collector .undefined after) :
    Contract before after closure receiver child slot methods collector parent q rows initial query := by
  have frames := NodeLiteralBranch.call_frames called rfl rfl rfl rfl rfl
  refine ⟨stored, called, frames.1, frames.2.1, frames.2.2.1, frames.2.2.2.1, frames.2.2.2.2.1, frames.2.2.2.2.2.1, frames.2.2.2.2.2.2, ?_⟩
  obtain ⟨_, bodyAfter, ⟨completed, selected, trace, rfl⟩, rfl⟩ := called
  have found : (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q)).heap[collector]? = some initial := collectorFound
  have output := MethodsLoop.processed_collector found trace
  exact ⟨selected, output⟩

/-- Exact161, with parent fourth and local q fifth. Current structural facts
introduce the body Layout in the conclusion, never as a future input premise. -/
theorem source_call_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent q keyBound : Nat)
    (rows initial : List Value) (query : JSString) (records : List Record)
    (installed : Installed before table closure receiver handle)
    (reads : CallReads before receiver node parentIdentity child collector parent q query)
    (stored : Storage before closure child slot methods collector rows)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial) :
    ∃ after, sourceCall (rows.length + keyBound + 103) table before = some (.ok (.undefined, after)) ∧
      Contract before after closure receiver child slot methods collector parent q rows initial query := by
  have callable := installed_callable before table closure receiver handle installed
  have storage := actual_storage before closure child slot methods collector rows stored
  have layout := body_layout_from_twoSource before closure.environment rows query collector keyBound records parent (.object q) initial closure (.object receiver) child facts rfl
  obtain ⟨bodyAfter, bodyRun, bodyContract⟩ := NodePrivateCall.body_satisfies before closure (.object receiver) child slot methods collector keyBound rows query parent (.object q) records initial storage layout
  have arguments := eval_arguments (rows.length + keyBound + 95) before receiver node parentIdentity child collector parent q query reads
  have invoked := runPrivateMethodCall_this (rows.length + keyBound + 103) defaultSplitLimit table (.object receiver) "pushHandlerSets" call.arguments before before
    (NodePrivateCall.fiveValues collector child query parent (.object q)) handle closure callable.tableSeparate callable.privateRead arguments callable.handleBound callable.closureFound
  have normal : runBlock (rows.length + keyBound + 103) closure.program.body
      (methodActivation closure (.object receiver) (NodePrivateCall.fiveValues collector child query parent (.object q)) before).state = .ok (.normal bodyAfter) := by
    rw [NodePrivateCall.five_activation before closure (.object receiver) collector child query parent (.object q) callable.sourceProgram, callable.sourceProgram]
    exact bodyRun
  rw [invokePrivateClosure_normal _ _ _ _ _ _ _ normal] at invoked
  have actual : runPrivateMethodCall (rows.length + keyBound + 103) defaultSplitLimit table ⟨before.thisValue⟩ call before =
      .ok (.undefined, restoreMethodCaller before bodyAfter) := by simpa [call, reads.thisValue] using invoked
  have contract : NodePrivateCall.CallContract before (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q))
      rows query collector .undefined (restoreMethodCaller before bodyAfter) := ⟨rfl, bodyAfter, bodyContract, rfl⟩
  refine ⟨_, ?_, contract_of_call before _ closure receiver child slot methods collector parent q rows initial query storage facts.frame.collectorFound contract⟩
  simpa [sourceCall, parses_call] using congrArg some actual

/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_call_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_call_satisfies
end HonoLean.Upstream.NodeCaptureCollect
