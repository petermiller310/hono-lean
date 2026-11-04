import HonoLean.Upstream.NodeIterationSetup.Admission

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset ECMA2025 MethodsLoopInitial

theorem preparation_satisfies (before : State) (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (inputs : Inputs before partsRef nodesRef parts nodes i j) :
    SetupSource before parts i ∧ SetupContract before parts nodes i j := by
  obtain ⟨search, searchContract, iteration, iterationContract⟩ := setup_satisfies before partsRef nodesRef parts nodes i j inputs
  exact ⟨⟨search, iteration⟩, searchContract, iterationContract, node_contract _ nodes j⟩

theorem missing_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat) (i j children receiver collector stamp nodeParams : Nat)
    (query : JSString) (next : Value)
    (inputs : Inputs before partsRef nodesRef parts nodes i j)
    (reads : InitialLookup before parts nodes i j children next) (falsy : truthy next = false) :
    SetupSource before parts i ∧ SetupContract before parts nodes i j ∧
    ∃ after,
      (parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl 201 defaultSplitLimit table source
          (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j)) =
        some (.ok (.normal after)) ∧
      NodeLiteralBranch.BranchContract (branchEntry before parts nodes i j) closure next receiver collector before.heap.length stamp query nodeParams after := by
  have setup := preparation_satisfies before partsRef nodesRef parts nodes i j inputs
  obtain ⟨run, contract⟩ := NodeLiteralBranch.missing_satisfies 0 (branchEntry before parts nodes i j) table closure
    (selectedNode nodes j) children receiver collector before.heap.length stamp nodeParams (selectedPart parts i) query next
    (lookup_entry before parts nodes i j children next reads) falsy
  rw [NodeLiteralBranch.parses_source, Option.map_some] at run
  have full := execute_node_branch 0 before _ table partsRef nodesRef parts nodes i j inputs (Option.some.inj run)
  refine ⟨setup.1, setup.2, _, ?_, contract⟩
  rw [parses_node_branch, Option.map_some, full]

theorem nonlast_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat)
    (i j children target receiver stamp collector nodeParams : Nat) (query : JSString) (old : Value)
    (inputs : Inputs before partsRef nodesRef parts nodes i j)
    (entry : InitialChild before parts nodes i j children target receiver stamp collector nodeParams query old)
    (notLast : i + 1 ≠ parts.length) :
    SetupSource before parts i ∧ SetupContract before parts nodes i j ∧
    ∃ after,
      (parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl 201 defaultSplitLimit table source
          (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j)) =
        some (.ok (.normal after)) ∧
      NodeLiteralBranch.BranchContract (branchEntry before parts nodes i j) closure (.object target) receiver collector before.heap.length stamp query nodeParams after := by
  have setup := preparation_satisfies before partsRef nodesRef parts nodes i j inputs
  obtain ⟨run, contract⟩ := NodeLiteralBranch.nonlast_satisfies 0 (branchEntry before parts nodes i j) table closure
    (selectedNode nodes j) children target receiver stamp collector before.heap.length nodeParams (selectedPart parts i) query (lastValue parts i) old []
    (child_entry before parts nodes i j children target receiver stamp collector nodeParams query old entry)
    (by simp [lastValue, notLast]) (fresh_queue_empty before parts nodes i j) fresh_queue_capacity
  rw [NodeLiteralBranch.parses_source, Option.map_some] at run
  have full := execute_node_branch 0 before _ table partsRef nodesRef parts nodes i j inputs (Option.some.inj run)
  refine ⟨setup.1, setup.2, _, ?_, contract⟩
  rw [parses_node_branch, Option.map_some, full]

theorem direct_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat)
    (i j children target receiver stamp handle collector childMap keyBound nodeParams : Nat)
    (query : JSString) (old wildcard : Value) (records : List Record) (initial : List Value)
    (inputs : Inputs before partsRef nodesRef parts nodes i j)
    (entry : InitialChild before parts nodes i j children target receiver stamp collector nodeParams query old)
    (lastIndex : i + 1 = parts.length)
    (ready : InitialDirect before table closure target receiver stamp handle collector childMap keyBound nodeParams query wildcard records initial) :
    SetupSource before parts i ∧ SetupContract before parts nodes i j ∧
    ∃ after,
      (parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl (ready.direct.rows.length + keyBound + 201) defaultSplitLimit table source
          (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j)) =
        some (.ok (.normal after)) ∧
      NodeLiteralBranch.BranchContract (branchEntry before parts nodes i j) closure (.object target) receiver collector before.heap.length stamp query nodeParams after := by
  have setup := preparation_satisfies before partsRef nodesRef parts nodes i j inputs
  let derived := direct_ready before parts nodes i j table closure target receiver stamp handle collector childMap keyBound nodeParams
    query wildcard records initial ready
  obtain ⟨after, run, contract⟩ := NodeLiteralBranch.direct_satisfies (branchEntry before parts nodes i j) table closure
    (selectedNode nodes j) children target receiver stamp handle collector before.heap.length childMap keyBound nodeParams (selectedPart parts i) query
    (lastValue parts i) old wildcard records initial
    (child_entry before parts nodes i j children target receiver stamp collector nodeParams query old entry)
    (by simp [lastValue, lastIndex]) derived
  rw [NodeLiteralBranch.parses_source, Option.map_some] at run
  have full := execute_node_branch (ready.direct.rows.length + keyBound) before after table partsRef nodesRef parts nodes i j inputs (Option.some.inj run)
  refine ⟨setup.1, setup.2, after, ?_, contract⟩
  rw [parses_node_branch, Option.map_some, full]

theorem wildcard_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat)
    (i j children target wildcardTarget receiver stamp handle collector childMap keyBound nodeParams : Nat)
    (query : JSString) (old : Value) (records : List Record) (initial : List Value)
    (inputs : Inputs before partsRef nodesRef parts nodes i j)
    (entry : InitialChild before parts nodes i j children target receiver stamp collector nodeParams query old)
    (lastIndex : i + 1 = parts.length)
    (ready : InitialWildcard before table closure target wildcardTarget receiver stamp handle collector childMap keyBound nodeParams query records initial) :
    SetupSource before parts i ∧ SetupContract before parts nodes i j ∧
    ∃ after,
      (parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames).map
        (fun source => executePrivateControl (ready.wildcard.rows.length + ready.direct.rows.length + keyBound + 201) defaultSplitLimit table source
          (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j)) =
        some (.ok (.normal after)) ∧
      NodeLiteralBranch.BranchContract (branchEntry before parts nodes i j) closure (.object target) receiver collector before.heap.length stamp query nodeParams after := by
  have setup := preparation_satisfies before partsRef nodesRef parts nodes i j inputs
  let derived := wildcard_ready before parts nodes i j table closure target wildcardTarget receiver stamp handle collector childMap keyBound nodeParams
    query records initial ready
  obtain ⟨after, run, contract⟩ := NodeLiteralBranch.wildcard_satisfies (branchEntry before parts nodes i j) table closure
    (selectedNode nodes j) children target wildcardTarget receiver stamp handle collector before.heap.length childMap keyBound nodeParams (selectedPart parts i) query
    (lastValue parts i) old records initial
    (child_entry before parts nodes i j children target receiver stamp collector nodeParams query old entry)
    (by simp [lastValue, lastIndex]) derived
  rw [NodeLiteralBranch.parses_source, Option.map_some] at run
  have full := execute_node_branch (ready.wildcard.rows.length + ready.direct.rows.length + keyBound) before after table
    partsRef nodesRef parts nodes i j inputs (Option.some.inj run)
  refine ⟨setup.1, setup.2, after, ?_, contract⟩
  rw [parses_node_branch, Option.map_some, full]

/-- info: 'HonoLean.Upstream.NodeIterationSetup.wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wildcard_satisfies

end HonoLean.Upstream.NodeIterationSetup
