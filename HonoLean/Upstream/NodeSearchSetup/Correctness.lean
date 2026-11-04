import HonoLean.Upstream.NodeSearchSetup.Setup

namespace HonoLean.Upstream.NodeSearchSetup

open SourceSubset ECMA2025

/-- One execution of the complete parsed startup. The split declaration calls
the actual source body in the current heap and binds its returned identity. -/
theorem execute_startup (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString)
    (inputs : Inputs before methods functions closure owner identity handle emptyParams old path) :
    executeFunctionStatements 100 defaultSplitLimit methods functions program before =
      .ok (.normal (resultState before owner identity emptyParams (producedParts path))) := by
  have collector := execute_collector 67 defaultSplitLimit before
  have reset := execute_reset 66 defaultSplitLimit before owner identity emptyParams old inputs.writable inputs.thisValue inputs.emptyBinding
  have alias := execute_alias 65 defaultSplitLimit before owner identity emptyParams inputs.thisValue
  have nodes := execute_nodes 64 defaultSplitLimit before owner identity emptyParams
  have called := execute_parts before methods functions closure owner identity handle emptyParams old path inputs
  have pending := execute_pending 62 defaultSplitLimit before owner identity emptyParams (producedParts path)
  have partsBinding : (pendingState before owner identity emptyParams (producedParts path)).environment.lookup "parts" =
      some (.array (before.heap.length + 2)) := by simp [pendingState, partsState, List.lookup]
  have partsFound : (pendingState before owner identity emptyParams (producedParts path)).heap[before.heap.length + 2]? =
      some ((producedParts path).map Value.string) := by simp [pendingState]
  have saved := execute_saved_length 60 defaultSplitLimit (pendingState before owner identity emptyParams (producedParts path))
    methods functions (before.heap.length + 2) (producedParts path) partsBinding partsFound
  simp only [SearchEntry.collectorProgram] at collector
  simp only [program, SearchEntry.collectorProgram, List.cons_append, List.nil_append, executeFunctionStatements]
  rw [collector]
  simp only [bind, Except.bind]
  rw [reset]
  dsimp only
  rw [alias]
  dsimp only
  rw [nodes]
  dsimp only
  rw [called]
  dsimp only
  rw [pending]
  dsimp only
  rw [saved, length_pending_eq]
  dsimp only [splitDeclaration]

theorem startup_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString)
    (inputs : Inputs before methods functions closure owner identity handle emptyParams old path) :
    (parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true).map
      (fun source => executeFunctionStatements 100 defaultSplitLimit methods functions source before) =
      some (.ok (.normal (resultState before owner identity emptyParams (producedParts path)))) ∧
    StartupContract before (resultState before owner identity emptyParams (producedParts path)) owner identity emptyParams old path (producedParts path) := by
  refine ⟨?_, result_contract before owner identity emptyParams old path inputs.writable⟩
  rw [parses_source, Option.map_some, execute_startup before methods functions closure owner identity handle emptyParams old path inputs]

/-- Subsequent actual iteration setup and the first entry declaration. Outer
i and inner j=0 activations are supplied across omitted headers99/104; the
source-produced singleton derives the j=0 bound. Taking the first parsed entry statement intentionally selects source105,
without claiming execution of its following branch or omitted loop headers. -/
theorem startup_iteration_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString) (i : Nat)
    (inputs : Inputs before methods functions closure owner identity handle emptyParams old path)
    (inside : i < (producedParts path).length) :
    let after := resultState before owner identity emptyParams (producedParts path)
    let activated := NodeIterationSetup.outerActivation after i
    let iterated := NodeIterationSetup.outerState activated (producedParts path) i
    let entered := NodeIterationSetup.innerActivation iterated 0
    (parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true).map
      (fun source => executeFunctionStatements 100 defaultSplitLimit methods functions source before) = some (.ok (.normal after)) ∧
    StartupContract before after owner identity emptyParams old path (producedParts path) ∧
    NodeIterationSetup.Inputs after (before.heap.length + 2) (before.heap.length + 1) (producedParts path) [owner] i 0 ∧
    (parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings).map
      (fun source => execute 32 defaultSplitLimit source activated) = some (.ok (.normal iterated)) ∧
    NodeIterationSetup.OuterContract activated iterated (producedParts path) i ∧
    (parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames).map
      (fun source => executePrivateControl 34 defaultSplitLimit methods (source.take 1) entered) =
      some (.ok (.normal (NodeIterationSetup.nodeState entered [owner] 0))) ∧
    NodeIterationSetup.NodeContract entered (NodeIterationSetup.nodeState entered [owner] 0) [owner] 0 := by
  dsimp only
  let after := resultState before owner identity emptyParams (producedParts path)
  let activated := NodeIterationSetup.outerActivation after i
  let iterated := NodeIterationSetup.outerState activated (producedParts path) i
  let entered := NodeIterationSetup.innerActivation iterated 0
  obtain ⟨startupRun, startup⟩ := startup_satisfies before methods functions closure owner identity handle emptyParams old path inputs
  have derived := derived_iteration_inputs before after owner identity emptyParams old path (producedParts path) i startup inside
  have partsBinding : activated.environment.lookup "parts" = some (.array (before.heap.length + 2)) := by
    simpa [activated, NodeIterationSetup.outerActivation, List.lookup] using derived.partsBinding
  have indexBinding : activated.environment.lookup "i" = some (.number i) := by simp [activated, NodeIterationSetup.outerActivation]
  have lengthBinding : activated.environment.lookup "len" = some (.number (producedParts path).length) := by
    simp [activated, NodeIterationSetup.outerActivation, after, resultState, resultEnvironment, List.lookup]
  have iteration := NodeIterationSetup.execute_outer 0 defaultSplitLimit activated (before.heap.length + 2) (producedParts path) i
    partsBinding derived.partsFound indexBinding lengthBinding inside
  have nodesBinding : entered.environment.lookup "curNodes" = some (.array (before.heap.length + 1)) := by
    simpa [entered, iterated, NodeIterationSetup.innerActivation, NodeIterationSetup.outerState, activated,
      NodeIterationSetup.outerActivation, List.lookup] using derived.nodesBinding
  have nodesFound : entered.heap[before.heap.length + 1]? = some ([owner].map Value.object) :=
    NodeIterationSetup.old_array_append [[]] rfl (before.heap.length + 1) _ derived.nodesFound
  have jBinding : entered.environment.lookup "j" = some (.number 0) := by simp [entered, NodeIterationSetup.innerActivation]
  have nodeRun := NodeIterationSetup.execute_node 0 defaultSplitLimit entered (before.heap.length + 1) [owner] 0 nodesBinding nodesFound jBinding (by simp)
  refine ⟨startupRun, startup, derived, ?_, NodeIterationSetup.outer_contract activated (producedParts path) i, ?_,
    NodeIterationSetup.node_contract entered [owner] 0⟩
  · rw [NodeIterationSetup.parses_outer, Option.map_some, iteration]
  · rw [NodeIterationSetup.parses_node_branch, Option.map_some]
    apply congrArg some
    simp only [NodeIterationSetup.nodeBranchProgram, List.take_succ_cons, List.take_zero, executePrivateControl, executePrivateControlStmt,
      NodeIterationSetup.nodeDeclaration]
    simp only [NodeIterationSetup.nodeDeclaration] at nodeRun
    rw [nodeRun]
    simp only [bind, Except.bind]
    rfl

/-- info: 'HonoLean.Upstream.NodeSearchSetup.startup_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_satisfies

end HonoLean.Upstream.NodeSearchSetup
