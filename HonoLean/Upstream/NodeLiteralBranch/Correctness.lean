import HonoLean.Upstream.NodeLiteralBranch.SecondCall
import HonoLean.Upstream.NodeLiteralBranch.Control

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025 MethodsLoopInitial

theorem missing_satisfies (extra : Nat) (before : State) (table : PrivateMethodTable)
    (closure : PrivateMethodClosure) (parent children receiver collector temp stamp nodeParams : Nat)
    (part query : JSString) (next : Value)
    (reads : Lookup before parent children part next) (falsy : truthy next = false) :
    (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
      (fun source => executePrivateControl (extra + 200) defaultSplitLimit table source before) =
        some (.ok (.normal (declaredState before next))) ∧
    BranchContract before closure next receiver collector temp stamp query nodeParams (declaredState before next) := by
  refine ⟨?_, .missing falsy⟩
  rw [parses_source, Option.map_some]
  apply congrArg some
  have declared := execute_declaration (extra + 188) defaultSplitLimit before parent children part next reads
  simp only [program, executePrivateControl, executePrivateControlStmt]
  rw [declared]
  simp only [bind, Except.bind]
  have nextEval : evalExpression (extra + 197) defaultSplitLimit (.variable "nextNode") (declaredState before next) =
      .ok (next, declaredState before next) := by
    simp [evalExpression, lookupVariable, declaredState, bind, Except.bind, pure, Except.pure]
  rw [nextEval]
  simp only [falsy, Bool.false_eq_true, ↓reduceIte, executePrivateControl]

theorem execute_enqueue (extra limit : Nat) (before : State) (target temp : Nat) (prior : List Value)
    (binding : before.environment.lookup "tempNodes" = some (.array temp))
    (targetBinding : before.environment.lookup "nextNode" = some (.object target))
    (found : before.heap[temp]? = some prior) :
    execute (extra + 20) limit [enqueue] before =
      .ok (.normal (enqueuedState before temp prior (.object target))) := by
  simp [enqueue, execute, evalExpression, evalArguments, lookupVariable, binding, targetBinding,
    intrinsic, found, enqueuedState,
    bind, Except.bind, pure, Except.pure]

theorem nonlast_satisfies (extra : Nat) (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (parent children target receiver stamp collector temp nodeParams : Nat)
    (part query : JSString) (last old : Value) (prior : List Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old)
    (falsy : truthy last = false)
    (tempFound : before.heap[temp]? = some prior) (capacity : prior.length + 1 ≤ 4294967295) :
    (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
      (fun source => executePrivateControl (extra + 200) defaultSplitLimit table source before) =
        some (.ok (.normal (enqueuedState (writtenState before target stamp nodeParams) temp prior (.object target)))) ∧
    BranchContract before closure (.object target) receiver collector temp stamp query nodeParams
      (enqueuedState (writtenState before target stamp nodeParams) temp prior (.object target)) := by
  refine ⟨?_, .nonlast target rfl last entry.lastBinding falsy old _ (propagation_contract _ _ _ _ _ _ _ _ _ _ _ _ _ entry) prior tempFound capacity⟩
  rw [parses_source, Option.map_some]
  apply congrArg some
  have declared := execute_declaration (extra + 188) defaultSplitLimit before parent children part (.object target) entry.lookup
  have propagated := execute_propagation (extra + 161) defaultSplitLimit before parent children target receiver stamp collector temp nodeParams
    part query last old entry
  have appended := execute_enqueue (extra + 172) defaultSplitLimit (writtenState before target stamp nodeParams) target temp prior
    entry.tempBinding (by simp [writtenState, writePrivateDataState, declaredState]) tempFound
  simp only [program, childBody, executePrivateControl, executePrivateControlStmt]
  rw [declared]
  simp only [bind, Except.bind]
  have nextEval : evalExpression (extra + 197) defaultSplitLimit (.variable "nextNode") (declaredState before (.object target)) =
      .ok (.object target, declaredState before (.object target)) := by
    simp [evalExpression, lookupVariable, declaredState, bind, Except.bind, pure, Except.pure]
  rw [nextEval]
  simp only [pure, Except.pure, show truthy (.object target) = true from rfl, ↓reduceIte]
  simp only [executePrivateControl, executePrivateControlStmt]
  rw [propagated]
  simp only [bind, Except.bind]
  have lastBinding : (writtenState before target stamp nodeParams).environment.lookup "isLast" = some last := by
    simpa [writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lastBinding
  rw [show evalExpression (extra + 194) defaultSplitLimit (.variable "isLast")
      (writtenState before target stamp nodeParams) = .ok (last, writtenState before target stamp nodeParams) by
    simp [evalExpression, lookupVariable, lastBinding, bind, Except.bind, pure, Except.pure]]
  simp only [falsy, Bool.false_eq_true, ↓reduceIte]
  simp only [executePrivateControl, executePrivateControlStmt, enqueue]
  simp only [enqueue] at appended
  rw [appended]
  simp [bind, Except.bind]

theorem direct_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (parent children target receiver stamp handle collector temp childMap keyBound nodeParams : Nat)
    (part query : JSString) (last old wildcard : Value) (records : List Record) (initial : List Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old)
    (lastTruthy : truthy last = true)
    (ready : DirectEntry before table closure target receiver stamp handle collector temp childMap keyBound nodeParams
      query wildcard records initial) :
    ∃ after,
      (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl (ready.direct.rows.length + keyBound + 200) defaultSplitLimit table source before) =
          some (.ok (.normal after)) ∧
      BranchContract before closure (.object target) receiver collector temp stamp query nodeParams after := by
  let written := writtenState before target stamp nodeParams
  have callable := callable_after_propagation before table closure target receiver stamp handle nodeParams old
    entry.scope entry.writable ready.callable
  have storage := storage_after_propagation before closure target target stamp ready.direct.methods collector nodeParams ready.direct.rows
    old entry.writable ready.direct.storage
  have parentRead := parent_after_propagation before parent target stamp nodeParams old entry.writable entry.parentRead
  have childrenRead := children_after_propagation before target stamp childMap nodeParams old entry.scope entry.writable ready.childrenRead
  have reads : NodePrivateCall.FourReads written collector target query nodeParams :=
    ⟨entry.collectorBinding, by simp [written, writtenState, writePrivateDataState, declaredState], entry.methodBinding,
      .object parent, by simpa [written, writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lookup.parentBinding, parentRead⟩
  have layout : Layout (NodePrivateCall.bodyState written closure (.object receiver) collector target query nodeParams .undefined)
      ready.direct.rows query collector (keyBound + 88) records .undefined nodeParams initial :=
    layout_keyBound (NodePrivateWrite.layout_frame ready.layout rfl rfl rfl rfl) (by omega)
  have arguments : evalArguments (ready.direct.rows.length + (keyBound + 88) + 103) defaultSplitLimit
      NodePrivateCall.fourCall.arguments written = .ok (NodePrivateCall.fourValues collector target query nodeParams, written) := by
    simpa [Nat.add_assoc] using NodePrivateCall.eval_four_arguments (ready.direct.rows.length + keyBound + 183)
      written collector target query nodeParams reads
  obtain ⟨after, run, call⟩ := actual_call_satisfies written table closure receiver handle target stamp ready.direct.methods collector
    (keyBound + 88) ready.direct.rows query nodeParams records initial NodePrivateCall.fourCall.arguments callable arguments storage layout
  have lastRun := execute_last_direct (ready.direct.rows.length + keyBound + 174) written after table target childMap receiver wildcard
    reads.targetBinding entry.thisValue childrenRead ready.wildcardRead ready.wildcardFalsy (by simpa [Nat.add_assoc, NodePrivateCall.fourCall] using run)
  have whole := execute_child_last (ready.direct.rows.length + keyBound) before after table parent children target receiver stamp collector temp
    nodeParams part query last old entry lastTruthy (by simpa [Nat.add_assoc] using lastRun)
  have frames := call_frames call rfl rfl rfl rfl rfl
  refine ⟨after, ?_, .direct target rfl last entry.lastBinding lastTruthy old written
    (propagation_contract _ _ _ _ _ _ _ _ _ _ _ _ _ entry) childMap wildcard childrenRead ready.wildcardRead ready.wildcardFalsy
    ready.direct.methods ready.direct.rows storage after call ?_⟩
  · rw [parses_source, Option.map_some, whole]
  · exact frames.2.2.2.2.2.2 temp ready.tempSeparate

theorem wildcard_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (parent children target wildcardTarget receiver stamp handle collector temp childMap keyBound nodeParams : Nat)
    (part query : JSString) (last old : Value) (records : List Record) (initial : List Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old)
    (lastTruthy : truthy last = true)
    (ready : WildcardEntry before table closure target wildcardTarget receiver stamp handle collector temp childMap keyBound nodeParams
      query records initial) :
    ∃ after,
      (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl
          (ready.wildcard.rows.length + ready.direct.rows.length + keyBound + 200) defaultSplitLimit table source before) =
          some (.ok (.normal after)) ∧
      BranchContract before closure (.object target) receiver collector temp stamp query nodeParams after := by
  let written := writtenState before target stamp nodeParams
  have callable := callable_after_propagation before table closure target receiver stamp handle nodeParams old
    entry.scope entry.writable ready.callable
  have wildcardStorage := storage_after_propagation before closure target wildcardTarget stamp ready.wildcard.methods collector nodeParams
    ready.wildcard.rows old entry.writable ready.wildcard.storage
  have directStorage := storage_after_propagation before closure target target stamp ready.direct.methods collector nodeParams ready.direct.rows
    old entry.writable ready.direct.storage
  have parentRead := parent_after_propagation before parent target stamp nodeParams old entry.writable entry.parentRead
  have childrenRead := children_after_propagation before target stamp childMap nodeParams old entry.scope entry.writable ready.childrenRead
  have reads : NodePrivateCall.FourReads written collector target query nodeParams :=
    ⟨entry.collectorBinding, by simp [written, writtenState, writePrivateDataState, declaredState], entry.methodBinding,
      .object parent, by simpa [written, writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lookup.parentBinding, parentRead⟩
  have initialLayout : Layout (NodePrivateCall.bodyState written closure (.object receiver)
      collector wildcardTarget query nodeParams .undefined) (ready.wildcard.rows ++ ready.direct.rows)
      query collector keyBound records .undefined nodeParams initial :=
    NodePrivateWrite.layout_frame ready.layout rfl rfl rfl rfl
  have wildcardLayout := layout_keyBound (layout_prefix initialLayout)
    (show keyBound ≤ ready.direct.rows.length + keyBound + 87 by omega)
  have wildcardArgs : evalArguments (ready.wildcard.rows.length + (ready.direct.rows.length + keyBound + 87) + 103)
      defaultSplitLimit wildcardCall.arguments written =
      .ok (NodePrivateCall.fourValues collector wildcardTarget query nodeParams, written) := by
    simpa [Nat.add_assoc] using eval_wildcard_arguments (ready.wildcard.rows.length + ready.direct.rows.length + keyBound + 178)
      written parent target childMap collector query nodeParams wildcardTarget reads.collectorBinding reads.targetBinding
      reads.methodBinding (by simpa [written, writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lookup.parentBinding)
      childrenRead ready.wildcardRead parentRead
  obtain ⟨middle, wildcardRun, wildcardContract⟩ := actual_call_satisfies written table closure receiver handle wildcardTarget stamp
    ready.wildcard.methods collector (ready.direct.rows.length + keyBound + 87) ready.wildcard.rows query nodeParams records initial
    wildcardCall.arguments callable wildcardArgs wildcardStorage wildcardLayout
  have firstFrames := call_frames wildcardContract rfl rfl rfl rfl rfl
  have directCallable := callable_after_call callable firstFrames.2.2.1 firstFrames.2.2.2.1 firstFrames.2.2.2.2.2.1
  have directStorage := storage_after_call directStorage firstFrames.2.2.1 firstFrames.2.2.2.2.2.2 firstFrames.2.2.2.2.2.1
  have directReads := reads_after_call written middle closure receiver target wildcardTarget parent collector nodeParams ready.wildcard.rows query
    reads (by simpa [written, writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lookup.parentBinding) wildcardContract
  obtain ⟨currentRecords, current, directLayout⟩ := second_layout written middle closure receiver wildcardTarget target collector keyBound nodeParams
    ready.wildcard.rows ready.direct.rows query records initial initialLayout wildcardContract
  have directLayout := layout_keyBound directLayout (show keyBound ≤ ready.wildcard.rows.length + keyBound + 88 by omega)
  have directArgs : evalArguments (ready.direct.rows.length + (ready.wildcard.rows.length + keyBound + 88) + 103) defaultSplitLimit
      NodePrivateCall.fourCall.arguments middle = .ok (NodePrivateCall.fourValues collector target query nodeParams, middle) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using NodePrivateCall.eval_four_arguments
      (ready.direct.rows.length + ready.wildcard.rows.length + keyBound + 183) middle collector target query nodeParams directReads
  obtain ⟨after, directRun, directContract⟩ := actual_call_satisfies middle table closure receiver handle target stamp ready.direct.methods collector
    (ready.wildcard.rows.length + keyBound + 88) ready.direct.rows query nodeParams currentRecords current
    NodePrivateCall.fourCall.arguments directCallable directArgs directStorage directLayout
  have middleThis : middle.thisValue = .object receiver := firstFrames.2.1.trans entry.thisValue
  have lastRun := execute_last_wildcard (ready.wildcard.rows.length + ready.direct.rows.length + keyBound + 174) written middle after table
    target childMap receiver wildcardTarget reads.targetBinding entry.thisValue middleThis childrenRead ready.wildcardRead
    (by simpa [Nat.add_assoc, wildcardCall] using wildcardRun)
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, NodePrivateCall.fourCall] using directRun)
  have whole := execute_child_last (ready.wildcard.rows.length + ready.direct.rows.length + keyBound) before after table parent children target
    receiver stamp collector temp nodeParams part query last old entry lastTruthy (by simpa [Nat.add_assoc] using lastRun)
  have secondFrames := call_frames directContract rfl rfl rfl rfl rfl
  refine ⟨after, ?_, .wildcard target wildcardTarget rfl last entry.lastBinding lastTruthy old written
    (propagation_contract _ _ _ _ _ _ _ _ _ _ _ _ _ entry) childMap childrenRead ready.wildcardRead
    ready.wildcard.methods ready.direct.methods ready.wildcard.rows ready.direct.rows middle after
    wildcardStorage directStorage wildcardContract directContract ?_⟩
  · rw [parses_source, Option.map_some, whole]
  · exact (secondFrames.2.2.2.2.2.2 temp ready.tempSeparate).trans (firstFrames.2.2.2.2.2.2 temp ready.tempSeparate)

/-- info: 'HonoLean.Upstream.NodeLiteralBranch.wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wildcard_satisfies

end HonoLean.Upstream.NodeLiteralBranch
