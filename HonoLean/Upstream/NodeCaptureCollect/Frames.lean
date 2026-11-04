import HonoLean.Upstream.NodeCaptureCollect.Correctness

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureCollect

open SourceSubset ECMA2025 MethodsLoopInitial

/-- A consequence of the completed actual161 call, not a future admission
premise. Protected ordinary objects stay unchanged, while handler records keep
only Shape: their params fields may be replaced on every shared-record visit. -/
theorem call_protected_invariant (before after : State) (closure : PrivateMethodClosure)
    (receiver child collector parent q keyBound : Nat) (rows initial : List Value) (query : JSString)
    (records : List Record)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial)
    (called : NodePrivateCall.CallContract before
      (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q))
      rows query collector .undefined after) :
    Invariant before after collector records := by
  have layout := body_layout_from_twoSource before closure.environment rows query collector keyBound records parent
    (.object q) initial closure (.object receiver) child facts rfl
  obtain ⟨_, bodyAfter, ⟨completed, selected, trace, rfl⟩, rfl⟩ := called
  have current := processed_invariant layout trace
  exact ⟨current.oldBound, current.protectedFrame, current.arrays, current.functions, current.closed, current.handlers⟩

/-- Extensional reads of protected ordinary cells, including their complete
prototype paths, survive the call. This is not a raw handler-cell frame: aliases
in an old collector prefix continue to observe the handler's current params. -/
structure ProtectedCallFrames (before after : State) (collector : Nat) (records : List Record)
    (parent q : Nat) : Prop where
  ordinary : ∀ reference, Protected before records reference → after.objects[reference]? = before.objects[reference]?
  descriptors : ∀ fuel reference, Protected before records reference → ∀ key,
    lookupProperty fuel after.objects reference key = lookupProperty fuel before.objects reference key
  reads : ∀ fuel reference, Protected before records reference → ∀ key,
    getProperty fuel after.objects reference key = getProperty fuel before.objects reference key
  parentObject : after.objects[parent]? = before.objects[parent]?
  localObject : after.objects[q]? = before.objects[q]?
  parentReads : ∀ fuel key, getProperty fuel after.objects parent key = getProperty fuel before.objects parent key
  localReads : ∀ fuel key, getProperty fuel after.objects q key = getProperty fuel before.objects q key
  keyArrays : ∀ record ∈ records, after.heap[record.keysArray]? = before.heap[record.keysArray]?
  handlers : ∀ record ∈ records, ∃ object, after.objects[record.reference]? = some object ∧ Shape record object
  otherArrays : ∀ reference, reference ≠ collector → after.heap[reference]? = before.heap[reference]?

/-- Initial structural facts plus the already-proved CallContract suffice.
Neither a future Layout nor any successful evaluator result is a new premise. -/
theorem call_protected_frames (before after : State) (closure : PrivateMethodClosure)
    (receiver child collector parent q keyBound : Nat) (rows initial : List Value) (query : JSString)
    (records : List Record)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial)
    (called : NodePrivateCall.CallContract before
      (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q))
      rows query collector .undefined after) :
    ProtectedCallFrames before after collector records parent q := by
  have current := call_protected_invariant before after closure receiver child collector parent q keyBound rows initial query records facts called
  refine {
    ordinary := current.protectedFrame
    descriptors := ?_
    reads := ?_
    parentObject := current.protectedFrame parent facts.sources.nodeProtected
    localObject := current.protectedFrame q (facts.sources.parameterProtected q rfl)
    parentReads := ?_
    localReads := ?_
    keyArrays := ?_
    handlers := current.handlers
    otherArrays := current.arrays }
  · intro fuel reference safe key
    exact (lookup_protected fuel current.protectedFrame facts.frame.protectedParents reference safe key).symm
  · intro fuel reference safe key
    exact (get_protected fuel current.protectedFrame facts.frame.protectedParents reference safe key).symm
  · intro fuel key
    exact (get_protected fuel current.protectedFrame facts.frame.protectedParents parent facts.sources.nodeProtected key).symm
  · intro fuel key
    exact (get_protected fuel current.protectedFrame facts.frame.protectedParents q (facts.sources.parameterProtected q rfl) key).symm
  · intro record member
    exact current.arrays record.keysArray (Ne.symm (facts.frame.recordsFound record member).separate)

/-- The rows' GET/ALL selection stays the same in the closure's captured
import view. The restored caller environment may have conflicting imports, so
this does not identify that caller environment with the helper's module scope. -/
theorem call_preserves_captured_choice (before after : State) (closure : PrivateMethodClosure)
    (receiver child collector parent q keyBound : Nat) (rows initial : List Value) (query : JSString)
    (records : List Record) (row : Nat) (chosen : Value)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial)
    (safeRow : Protected before records row)
    (called : NodePrivateCall.CallContract before
      (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q))
      rows query collector .undefined after) :
    SearchEntry.Choice (capturedView after closure.environment) row query chosen ↔
      SearchEntry.Choice (capturedView before closure.environment) row query chosen := by
  have frames := call_protected_frames before after closure receiver child collector parent q keyBound rows initial query records facts called
  unfold SearchEntry.Choice capturedView
  simp only [frames.reads propertyFuel row safeRow]

/-- Actual source161, with its existing parsed call theorem, now yields the
protected-object/read and handler-shape consequences without a later-state
Layout, body run, completed trace or future readiness supplied by the caller. -/
theorem source_call_protected_frames (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent q keyBound : Nat)
    (rows initial : List Value) (query : JSString) (records : List Record)
    (installed : Installed before table closure receiver handle)
    (reads : CallReads before receiver node parentIdentity child collector parent q query)
    (stored : Storage before closure child slot methods collector rows)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial) :
    ∃ after, sourceCall (rows.length + keyBound + 103) table before = some (.ok (.undefined, after)) ∧
      Contract before after closure receiver child slot methods collector parent q rows initial query ∧
      ProtectedCallFrames before after collector records parent q := by
  obtain ⟨after, executed, contract⟩ := source_call_satisfies before table closure receiver handle node parentIdentity child slot methods collector parent q keyBound
    rows initial query records installed reads stored facts
  exact ⟨after, executed, contract, call_protected_frames before after closure receiver child collector parent q keyBound
    rows initial query records facts contract.called⟩

end HonoLean.Upstream.NodeCaptureCollect
