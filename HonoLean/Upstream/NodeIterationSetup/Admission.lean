import HonoLean.Upstream.NodeIterationSetup.Setup

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset ECMA2025 MethodsLoopInitial

theorem lookup_entry (before : State) (parts : List JSString) (nodes : List Nat) (i j children : Nat) (next : Value)
    (reads : InitialLookup before parts nodes i j children next) :
    NodeLiteralBranch.Lookup (branchEntry before parts nodes i j) (selectedNode nodes j) children (selectedPart parts i) next := by
  refine ⟨?_, ?_, reads.childrenRead, reads.nextRead⟩
  · simp [branchEntry, nodeState]
  · simp [branchEntry, nodeState, innerActivation, outerState, List.lookup]

theorem child_entry (before : State) (parts : List JSString) (nodes : List Nat)
    (i j children target receiver stamp collector nodeParams : Nat) (query : JSString) (old : Value)
    (entry : InitialChild before parts nodes i j children target receiver stamp collector nodeParams query old) :
    NodeLiteralBranch.ChildEntry (branchEntry before parts nodes i j) (selectedNode nodes j) children target receiver stamp collector
      before.heap.length nodeParams (selectedPart parts i) query (lastValue parts i) old := by
  refine ⟨lookup_entry before parts nodes i j children (.object target) entry.lookup, entry.scope,
    ⟨entry.writable.scope, entry.writable.allocated, entry.writable.data⟩, entry.parentRead, ?_, entry.thisValue, ?_, ?_, ?_⟩
  · simp [branchEntry, nodeState, innerActivation, outerState, List.lookup]
  · rw [branch_lookup_other before parts nodes i j "handlerSets" (by decide)]
    exact entry.collectorBinding
  · rw [branch_lookup_other before parts nodes i j "method" (by decide)]
    exact entry.methodBinding
  · simp [branchEntry, nodeState, innerActivation, outerState, outerActivation, lengthState, List.lookup]

def direct_ready (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target receiver stamp handle collector children keyBound nodeParams : Nat) (query : JSString)
    (wildcard : Value) (records : List Record) (initial : List Value)
    (ready : InitialDirect before table closure target receiver stamp handle collector children keyBound nodeParams query wildcard records initial) :
    NodeLiteralBranch.DirectEntry (branchEntry before parts nodes i j) table closure target receiver stamp handle collector before.heap.length
      children keyBound nodeParams query wildcard records initial :=
  ⟨branch_callable parts nodes i j ready.callable,
    ⟨ready.direct.methods, ready.direct.rows, branch_storage parts nodes i j ready.direct.storage⟩,
    ready.childrenRead, ready.wildcardRead, ready.wildcardFalsy,
    fresh_queue_separate collector initial ready.layout.collectorFound, branch_layout parts nodes i j ready.layout⟩

def wildcard_ready (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target wildcardTarget receiver stamp handle collector children keyBound nodeParams : Nat) (query : JSString)
    (records : List Record) (initial : List Value)
    (ready : InitialWildcard before table closure target wildcardTarget receiver stamp handle collector children keyBound nodeParams
      query records initial) :
    NodeLiteralBranch.WildcardEntry (branchEntry before parts nodes i j) table closure target wildcardTarget receiver stamp handle collector
      before.heap.length children keyBound nodeParams query records initial :=
  ⟨branch_callable parts nodes i j ready.callable,
    ⟨ready.direct.methods, ready.direct.rows, branch_storage parts nodes i j ready.direct.storage⟩,
    ⟨ready.wildcard.methods, ready.wildcard.rows, branch_storage parts nodes i j ready.wildcard.storage⟩,
    ready.childrenRead, ready.wildcardRead, fresh_queue_separate collector initial ready.layout.collectorFound,
    branch_layout parts nodes i j ready.layout⟩

theorem fresh_queue_empty (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) :
    (branchEntry before parts nodes i j).heap[before.heap.length]? = some [] := by simp [branch_heap]

theorem fresh_queue_capacity : ([] : List Value).length + 1 ≤ 4294967295 := by decide

/-- The full source entry105–119 starts by selecting node from the actual
current dense curNodes array. The existing literal branch then executes in
that declared scope, with no assumed node binding. -/
theorem execute_node_branch (extra : Nat) (before after : State) (table : PrivateMethodTable)
    (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (inputs : Inputs before partsRef nodesRef parts nodes i j)
    (branch : executePrivateControl (extra + 200) defaultSplitLimit table NodeLiteralBranch.program
      (branchEntry before parts nodes i j) = .ok (.normal after)) :
    executePrivateControl (extra + 201) defaultSplitLimit table nodeBranchProgram
      (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j) = .ok (.normal after) := by
  let staged := innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j
  have nodesBinding : staged.environment.lookup "curNodes" = some (.array nodesRef) := by
    simpa [staged, innerActivation, outerState, outerActivation, lengthState, List.lookup] using inputs.nodesBinding
  have nodesFound : staged.heap[nodesRef]? = some (nodes.map Value.object) :=
    old_array_append [[]] rfl nodesRef _ inputs.nodesFound
  have indexBinding : staged.environment.lookup "j" = some (.number j) := by simp [staged, innerActivation]
  have declared := execute_node (extra + 167) defaultSplitLimit staged nodesRef nodes j nodesBinding nodesFound indexBinding inputs.innerInside
  simp only [nodeBranchProgram, executePrivateControl, executePrivateControlStmt, nodeDeclaration] at ⊢
  simp only [nodeDeclaration] at declared
  rw [declared]
  simp only [bind, Except.bind]
  exact branch

end HonoLean.Upstream.NodeIterationSetup
