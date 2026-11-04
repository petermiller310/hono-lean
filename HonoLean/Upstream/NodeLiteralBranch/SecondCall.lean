import HonoLean.Upstream.NodeLiteralBranch.Evaluation

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025 MethodsLoopInitial

/-- The wildcard helper's independent trace establishes the direct helper's
entire fresh initial layout. Union records permit repeated/shared handlers;
their descriptors are rebased onto the current heap after the first reset. -/
theorem second_layout (before middle : State) (closure : PrivateMethodClosure)
    (receiver wildcardTarget target collector keyBound nodeParams : Nat)
    (wildcardRows directRows : List Value) (query : JSString) (records : List Record) (initial : List Value)
    (layout : Layout (NodePrivateCall.bodyState before closure (.object receiver)
      collector wildcardTarget query nodeParams .undefined)
      (wildcardRows ++ directRows) query collector keyBound records .undefined nodeParams initial)
    (first : NodePrivateCall.CallContract before
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
      wildcardRows query collector .undefined middle) :
    ∃ currentRecords current,
      Layout (NodePrivateCall.bodyState middle closure (.object receiver) collector target query nodeParams .undefined)
        directRows query collector keyBound currentRecords .undefined nodeParams current := by
  obtain ⟨_, bodyAfter, ⟨completed, selected, trace, rfl⟩, rfl⟩ := first
  have prefixLayout := layout_prefix layout
  have invariant := processed_invariant prefixLayout trace
  have newNull := processed_new_null prefixLayout trace
  let nextOrigin := NodePrivateCall.bodyState
    (restoreMethodCaller before {completed with environment :=
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined).environment})
    closure (.object receiver) collector target query nodeParams .undefined
  have lifted : Invariant
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
      nextOrigin collector records :=
    ⟨invariant.oldBound, invariant.protectedFrame, invariant.arrays, invariant.functions, invariant.closed, invariant.handlers⟩
  have liftedNull : ∀ reference,
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined).objects.length ≤ reference →
      ∀ object, nextOrigin.objects[reference]? = some object → object.prototype = none := newNull
  have bindings : ∀ name, name ∈ ["handlerSets", "params", "nodeParams", "METHOD_NAME_ALL", "createNullObject"] →
      nextOrigin.environment.lookup name =
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined).environment.lookup name := by
    intro name member
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  have collectorFound : nextOrigin.heap[collector]? = some (initial ++ selected.map Value.object) := by
    change completed.heap[collector]? = some (initial ++ selected.map Value.object)
    exact MethodsLoop.processed_collector layout.collectorFound trace
  have capacity : (initial ++ selected.map Value.object).length + directRows.length ≤ 4294967295 := by
    have selectedBound := selected_length_bound trace
    have bound := layout.capacity
    simp only [List.length_append, List.length_map] at *
    omega
  exact ⟨_, _, rebase_layout (layout_suffix layout) lifted liftedNull bindings collectorFound capacity⟩

/-- The actual private params read in the direct call is performed after the
wildcard helper. It is derived from private-store and allocation frames. -/
theorem reads_after_call (before middle : State) (closure : PrivateMethodClosure)
    (receiver target wildcardTarget parent collector nodeParams : Nat) (rows : List Value) (query : JSString)
    (reads : NodePrivateCall.FourReads before collector target query nodeParams)
    (parentBinding : before.environment.lookup "node" = some (.object parent))
    (call : NodePrivateCall.CallContract before
      (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
      rows query collector .undefined middle) :
    NodePrivateCall.FourReads middle collector target query nodeParams := by
  have frames := call_frames call rfl rfl rfl rfl rfl
  obtain ⟨value, binding, read⟩ := reads.callerNode
  have equal : value = .object parent := Option.some.inj (binding.symm.trans parentBinding)
  subst value
  refine ⟨frames.1 ▸ reads.collectorBinding, frames.1 ▸ reads.targetBinding,
    frames.1 ▸ reads.methodBinding, .object parent, frames.1 ▸ binding,
    privateGet_growth parent "params" (.object nodeParams) frames.2.2.1 frames.2.2.2.2.2.1 read⟩

end HonoLean.Upstream.NodeLiteralBranch
