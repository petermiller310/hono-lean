import HonoLean.Upstream.NodeLoopEntry.Setup

namespace HonoLean.Upstream.NodeLoopEntry

open SourceSubset ECMA2025

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

/-- This executor supports exactly the selected continuation through source105.
It dispatches the actual parsed initializers/tests and selected statements;
it is not an implementation of the omitted complete for bodies or suffixes. -/
def executePrefix (startup : List Stmt) (outer : ForHeader) (iteration : List Stmt) (inner : ForHeader)
    (entry : List PrivateControlStmt) (methods : PrivateMethodTable) (functions : FunctionTable) (before : State) :
    Except EvalError PrefixResult := do
  let started ← normalState (← executeFunctionStatements 100 defaultSplitLimit methods functions startup before)
  let outerEntered ← enterForHeader 32 defaultSplitLimit outer started
  let (outerTaken, outerChecked) ← testForHeader 32 defaultSplitLimit outer outerEntered
  if !outerTaken then pure ⟨outerChecked, false, none, false⟩ else do
  let iterated ← normalState (← execute 32 defaultSplitLimit iteration outerChecked)
  let innerEntered ← enterForHeader 32 defaultSplitLimit inner iterated
  let (innerTaken, innerChecked) ← testForHeader 32 defaultSplitLimit inner innerEntered
  if !innerTaken then pure ⟨innerChecked, true, some false, false⟩ else do
  let after ← normalState (← executePrivateControl 34 defaultSplitLimit methods (entry.take 1) innerChecked)
  pure ⟨after, true, some true, true⟩

def sourcePrefix (methods : PrivateMethodTable) (functions : FunctionTable) (before : State) :
    Option (Except EvalError PrefixResult) := do
  let startup ← parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true
  let outer ← parseForHeader pinnedOuterSource outerBindings
  let iteration ← parseBlock NodeIterationSetup.pinnedIterationSource NodeIterationSetup.outerBindings
  let inner ← parseForHeader pinnedInnerSource innerBindings
  let entry ← parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames
  pure (executePrefix startup outer iteration inner entry methods functions before)

def result (before : State) (owner identity emptyParams : Nat) (path : JSString) : PrefixResult :=
  if NodeSearchSetup.producedParts path = [] then
    ⟨outerState (started before owner identity emptyParams path), false, none, false⟩
  else ⟨selected before owner identity emptyParams path, true, some true, true⟩

theorem result_contract (before : State) (owner identity emptyParams : Nat) (old : Value) (path : JSString)
    (writable : NodePrivateWrite.Writable before owner identity old) :
    PrefixContract before owner identity emptyParams old path (result before owner identity emptyParams path) := by
  have startup := NodeSearchSetup.result_contract before owner identity emptyParams old path writable
  by_cases empty : NodeSearchSetup.producedParts path = []
  · simp only [result, empty, ↓reduceIte]
    refine .empty _ empty _ _ _ startup (outer_entry_contract _) ?_
    simpa [empty, started] using outer_guard_contract (started before owner identity emptyParams path)
      (NodeSearchSetup.producedParts path).length (startup_len before owner identity emptyParams path)
  · simp only [result, empty, ↓reduceIte]
    have inside : 0 < (NodeSearchSetup.producedParts path).length := List.length_pos_iff.mpr empty
    refine .nonempty (NodeSearchSetup.producedParts path) empty
      (started before owner identity emptyParams path)
      (outerState (started before owner identity emptyParams path))
      (outerState (started before owner identity emptyParams path))
      (iterated before owner identity emptyParams path)
      (innerState (iterated before owner identity emptyParams path) 1)
      (innerState (iterated before owner identity emptyParams path) 1)
      (selected before owner identity emptyParams path) startup (outer_entry_contract _) ?_
      (NodeIterationSetup.outer_contract _ _ 0) (inner_entry_contract _ 1) ?_ (NodeIterationSetup.node_contract _ [owner] 0)
    · simpa [inside] using outer_guard_contract (started before owner identity emptyParams path)
        (NodeSearchSetup.producedParts path).length (startup_len before owner identity emptyParams path)
    · simpa using inner_guard_contract (iterated before owner identity emptyParams path) 1

theorem source_prefix_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString)
    (inputs : NodeSearchSetup.Inputs before methods functions closure owner identity handle emptyParams old path) :
    sourcePrefix methods functions before = some (.ok (result before owner identity emptyParams path)) ∧
    PrefixContract before owner identity emptyParams old path (result before owner identity emptyParams path) := by
  refine ⟨?_, result_contract before owner identity emptyParams old path inputs.writable⟩
  have startup := NodeSearchSetup.execute_startup before methods functions closure owner identity handle emptyParams old path inputs
  change executeFunctionStatements 100 defaultSplitLimit methods functions NodeSearchSetup.program before =
    .ok (.normal (started before owner identity emptyParams path)) at startup
  have outerTest := test_outer (started before owner identity emptyParams path) (NodeSearchSetup.producedParts path).length
    (startup_len before owner identity emptyParams path)
  simp only [sourcePrefix, NodeSearchSetup.parses_source, parses_outer, NodeIterationSetup.parses_outer, parses_inner,
    NodeIterationSetup.parses_node_branch]
  dsimp only [bind, pure, Option.bind]
  unfold executePrefix
  rw [startup]
  dsimp only [normalState, bind, pure, Except.bind, Except.pure]
  rw [enter_outer]
  dsimp only
  rw [outerTest]
  dsimp only
  by_cases empty : NodeSearchSetup.producedParts path = []
  · simp [empty, result]
  · have inside : 0 < (NodeSearchSetup.producedParts path).length := List.length_pos_iff.mpr empty
    simp only [inside, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [iteration_from_entered before owner identity emptyParams path inside]
    dsimp only [normalState, bind, pure, Except.bind, Except.pure]
    rw [inner_from_iteration]
    dsimp only
    rw [test_inner]
    dsimp only
    have node := node_from_inner before owner identity emptyParams path
    simp only [NodeIterationSetup.nodeBranchProgram, List.take_succ_cons, List.take_zero, executePrivateControl,
      executePrivateControlStmt, NodeIterationSetup.nodeDeclaration]
    simp only [NodeIterationSetup.nodeDeclaration] at node
    rw [node]
    simp [result, empty, bind, Except.bind]

/-- The empty guard path adds no temporary body queue. Startup's four arrays
still exist, including the actual empty returned split array. -/
theorem empty_skips_body_allocation (before : State) (owner identity emptyParams : Nat) (path : JSString)
    (empty : NodeSearchSetup.producedParts path = []) :
    (result before owner identity emptyParams path).state.heap.length = before.heap.length + 4 ∧
    (result before owner identity emptyParams path).outerTaken = false ∧
    (result before owner identity emptyParams path).innerTaken = none ∧
    (result before owner identity emptyParams path).nodeDeclared = false := by
  simp [result, empty, outerState, started, NodeSearchSetup.resultState]

/-- Given a normal continuation's preserved current j/len2 bindings, the
actual postfix update changes j to1 and the saved singleton bound exits.
No claim is made that the omitted source suffix preserved these bindings. -/
theorem inner_progress (completed : State)
    (counter : completed.environment.lookup "j" = some (.number 0))
    (saved : completed.environment.lookup "len2" = some (.number 1)) :
    HeaderIncrementDomain 0 ∧ ∃ after,
      advanceForHeader innerHeader completed = .ok after ∧
      HeaderIncrementContract completed after "j" 0 ∧
      testForHeader 32 defaultSplitLimit innerHeader after = .ok (false, after) := by
  refine ⟨uint32_guard_increment_safe 0 1 (by decide) (by decide), ?_⟩
  simpa [innerHeader] using advanceForHeader_then_test 28 defaultSplitLimit innerHeader completed "len2" 0 1 rfl counter saved (by decide)

/-- Updating the actual current counter retests the saved numeric len. The
native exact-integer boundary is derived from the admitted UInt32 guard.
This theorem deliberately supplies no current-array indexing conclusion. -/
theorem outer_progress (completed : State) (counter length : Nat)
    (counterFound : completed.environment.lookup "i" = some (.number counter))
    (saved : completed.environment.lookup "len" = some (.number length))
    (inside : counter < length) (bounded : length ≤ 4294967295) :
    HeaderIncrementDomain counter ∧ ∃ after,
      advanceForHeader outerHeader completed = .ok after ∧
      HeaderIncrementContract completed after "i" counter ∧
      testForHeader 32 defaultSplitLimit outerHeader after = .ok (decide (counter + 1 < length), after) := by
  refine ⟨uint32_guard_increment_safe counter length inside bounded, ?_⟩
  have comparison : (counter : Int) + 1 < (length : Int) ↔ counter + 1 < length := by omega
  simpa [outerHeader, comparison] using advanceForHeader_then_test 28 defaultSplitLimit outerHeader completed "len" counter length rfl counterFound saved (by decide)

/-- A true saved-bound guard admits the next actual part declaration only
with separately protected CURRENT parts binding and dense array contents.
The post-update frames derive those reads; saved len alone would not suffice
after arbitrary aliasing or rebinding by a body continuation. -/
theorem outer_progress_with_current_parts (completed : State) (partsRef counter : Nat) (parts : List JSString)
    (counterFound : completed.environment.lookup "i" = some (.number counter))
    (saved : completed.environment.lookup "len" = some (.number parts.length))
    (partsBinding : completed.environment.lookup "parts" = some (.array partsRef))
    (partsFound : completed.heap[partsRef]? = some (parts.map Value.string))
    (inside : counter < parts.length) (bounded : parts.length ≤ 4294967295) :
    ∃ after,
      advanceForHeader outerHeader completed = .ok after ∧
      HeaderIncrementContract completed after "i" counter ∧
      testForHeader 32 defaultSplitLimit outerHeader after = .ok (decide (counter + 1 < parts.length), after) ∧
      (decide (counter + 1 < parts.length) = true →
        execute 32 defaultSplitLimit NodeIterationSetup.outerProgram after =
          .ok (.normal (NodeIterationSetup.outerState after parts (counter + 1)))) := by
  obtain ⟨_, after, advanced, increment, guard⟩ := outer_progress completed counter parts.length counterFound saved inside bounded
  refine ⟨after, advanced, increment, guard, ?_⟩
  intro taken
  have nextInside : counter + 1 < parts.length := of_decide_eq_true taken
  have nextCounter : after.environment.lookup "i" = some (.number (counter + 1)) := by
    simpa [Int.natCast_add] using increment.counter
  exact NodeIterationSetup.execute_outer 0 defaultSplitLimit after partsRef parts (counter + 1)
    ((increment.otherBindings "parts" (by decide)).trans partsBinding)
    (increment.heap ▸ partsFound) nextCounter
    ((increment.otherBindings "len" (by decide)).trans saved) nextInside

/-- info: 'HonoLean.Upstream.NodeLoopEntry.source_prefix_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_prefix_satisfies

end HonoLean.Upstream.NodeLoopEntry
