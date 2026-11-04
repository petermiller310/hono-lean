import HonoLean.Upstream.NodeChildEnumeration.Contract

namespace HonoLean.Upstream.NodeChildEnumeration

open SourceSubset ECMA2025

theorem children_read (before : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject)
    (inputs : ChildrenInputs before owner childrenIdentity children object) :
    privateGet (.object owner) "children" (forInStateView before) = .ok (.object children) := by
  obtain ⟨ownerObject, allocated⟩ := inputs.allocated
  obtain ⟨fields, brand, field⟩ := inputs.data
  simp [privateGet, forInStateView, embedIndexedState, inputs.lexical, allocated,
    PrivateStore.slots_lookup, brand, lookup_map_values, field, bind, Except.bind]

theorem children_keys (fuel : Nat) (before : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject)
    (inputs : ChildrenInputs before owner childrenIdentity children object) :
    forInChildren (fuel + 3) "_" collection before = .ok (enumerableOwn object) := by
  obtain ⟨ownerObject, allocated⟩ := inputs.allocated
  obtain ⟨fields, brand, field⟩ := inputs.data
  exact forInChildren_private_data fuel "_" "child" "children" before owner childrenIdentity children ownerObject object fields
    (by decide) inputs.binding inputs.lexical allocated brand field inputs.found inputs.nullPrototype

/-- Empty/nonenumerable descriptors skip every body operation. In particular,
m, params, queue and a writable params slot are not initial premises. -/
theorem source_empty_satisfies (extra : Nat) (before : ForInState) (owner childrenIdentity children : Nat) (object : OrdinaryObject)
    (inputs : ChildrenInputs before owner childrenIdentity children object) (noneEnumerable : NoEnumerable object) :
    pinnedSource = pinnedPrefix ++ NodeComponentCount.pinnedFullSource ++ pinnedSuffix ∧
    sourceLoop (extra + 120) before = some (.ok (.normal before)) ∧
    EmptyContract before before owner childrenIdentity children object := by
  have keys := children_keys (extra + 116) before owner childrenIdentity children object inputs
  rw [enumerableOwn_empty_of_descriptors object noneEnumerable] at keys
  refine ⟨reassembles_source, ?_, ⟨inputs, noneEnumerable, rfl⟩⟩
  simp only [sourceLoop, parses_source]
  dsimp only [bind, pure, Option.bind]
  simp only [program, executeForInSequence]
  rw [keys]
  simp [executeForInKeys, bind, Except.bind]

theorem scoped_children_binding (before : ForInState) (key : JSString) (owner childrenIdentity children : Nat) (object : OrdinaryObject)
    (inputs : ChildrenInputs before owner childrenIdentity children object) :
    (bindForInKey "_" key before).regexp.arrays.environment.lookup "child" = some (.object owner) := by
  simpa [bindForInKey, List.lookup_cons] using inputs.binding

theorem scoped_children_inputs (before : ForInState) (key : JSString) (owner childrenIdentity children : Nat) (object : OrdinaryObject)
    (inputs : ChildrenInputs before owner childrenIdentity children object) :
    ChildrenInputs (bindForInKey "_" key before) owner childrenIdentity children object :=
  ⟨scoped_children_binding before key owner childrenIdentity children object inputs, inputs.allocated, inputs.lexical,
    inputs.data, inputs.found, inputs.nullPrototype, inputs.wellFormed⟩

theorem scoped_body_inputs (before : ForInState) (key : JSString) (owner childrenIdentity paramsIdentity : Nat)
    (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input) :
    BodyInputs (bindForInKey "_" key before) owner childrenIdentity paramsIdentity old params m queue matched queued input := by
  refine ⟨⟨inputs.writable.scope, inputs.writable.allocated, inputs.writable.data⟩, ?_, inputs.distinct, ?_, ?_, inputs.admitted⟩
  · simpa [bindForInKey, List.lookup_cons] using inputs.paramsBinding
  · refine ⟨?_, inputs.count.found, inputs.count.input, inputs.count.wellFormed, inputs.count.legalLength⟩
    simpa [bindForInKey, List.lookup_cons] using inputs.count.binding
  · refine ⟨?_, ?_, inputs.queue.queueFound, inputs.queue.wellFormed, inputs.queue.legalLength, inputs.queue.stringBound⟩
    · simpa [bindForInKey, List.lookup_cons] using inputs.queue.queueBinding
    · simpa [bindForInKey, List.lookup_cons] using inputs.queue.childBinding

theorem execute_parameter (extra : Nat) (before : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input) :
    executeForInPrivateWrite (extra + 117) NodePrivateWrite.parameter before =
      .ok (forInDataState before owner paramsIdentity params) := by
  obtain ⟨ownerObject, allocated⟩ := inputs.writable.allocated
  obtain ⟨fields, brand, field⟩ := inputs.writable.data
  exact executeForInPrivateWrite_data (extra + 113) "child" "params" "params" before owner paramsIdentity params old ownerObject fields
    childrenInputs.binding inputs.paramsBinding inputs.writable.scope allocated brand field

theorem private_write_contract (before : ForInState) (owner paramsIdentity : Nat) (old params : Value)
    (writable : NodePrivateWrite.Writable (forInStateView before) owner paramsIdentity old) :
    NodePrivateWrite.WriteContract (forInStateView before) (forInStateView (forInDataState before owner paramsIdentity params))
      owner paramsIdentity old params params := by
  rw [forInDataState_view]
  exact NodePrivateWrite.write_contract _ owner paramsIdentity old params writable

theorem children_read_after_write (before : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (params : Value) (inputs : ChildrenInputs before owner childrenIdentity children object)
    (different : childrenIdentity ≠ paramsIdentity) :
    privateGet (.object owner) "children" (forInStateView (forInDataState before owner paramsIdentity params)) = .ok (.object children) := by
  obtain ⟨fields, brand, _⟩ := inputs.data
  rw [forInDataState_view, privateGet_write_other_identity (forInStateView before) owner paramsIdentity childrenIdentity params "children" fields inputs.lexical brand different]
  exact children_read before owner childrenIdentity children object inputs

end HonoLean.Upstream.NodeChildEnumeration
