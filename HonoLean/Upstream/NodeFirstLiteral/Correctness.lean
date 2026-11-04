import HonoLean.Upstream.NodeFirstLiteral.Admission

namespace HonoLean.Upstream.NodeFirstLiteral

open SourceSubset ECMA2025 MethodsLoopInitial

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | _ => .error .unsupported

/-- Continue the actual parsed source106–119 only when the actual entry
declared node. This is still the selected first literal fragment, not the
remaining inner body or a completed traversal. -/
def executeFirst (budget : Nat) (methods : PrivateMethodTable) (literal : List PrivateControlStmt)
    (entry : NodeLoopEntry.PrefixResult) : Except EvalError Result := do
  if !entry.nodeDeclared then pure ⟨entry, entry.state⟩ else do
  let after ← normalState (← executePrivateControl budget defaultSplitLimit methods literal entry.state)
  pure ⟨entry, after⟩

def sourceFirst (budget : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (before : State) :
    Option (Except EvalError Result) := do
  let literal ← parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames
  let entry ← NodeLoopEntry.sourcePrefix methods functions before
  pure do
    let entry ← entry
    executeFirst budget methods literal entry

theorem empty_satisfies (budget : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure) (owner stamp splitHandle emptyParams : Nat)
    (oldRoot : Value) (path query : JSString)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (empty : NodeSearchSetup.producedParts path = []) :
    SourceBound ∧ sourceFirst budget methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path,
        (NodeLoopEntry.result before owner (stamp + 4) emptyParams path).state⟩) ∧
    Contract before closure owner stamp emptyParams oldRoot path query
      ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path,
        (NodeLoopEntry.result before owner (stamp + 4) emptyParams path).state⟩ := by
  obtain ⟨run, contract⟩ := NodeLoopEntry.source_prefix_satisfies before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path inputs
  refine ⟨source_bound, ?_, .empty _ contract (by simp [NodeLoopEntry.result, empty])⟩
  simp only [sourceFirst, NodeLiteralBranch.parses_source, run]
  dsimp only [bind, pure, Option.bind, Except.bind, Except.pure]
  simp [executeFirst, NodeLoopEntry.result, empty, pure, Except.pure]

private theorem combine_branch (budget : Nat) (before after : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure) (owner stamp splitHandle emptyParams children : Nat)
    (oldRoot : Value) (path query : JSString) (next : Value)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (nonempty : NodeSearchSetup.producedParts path ≠ [])
    (reads : Lookup before owner children path next)
    (run : (parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames).map
      (fun source => executePrivateControl budget defaultSplitLimit methods source (selected before owner stamp emptyParams path)) =
        some (.ok (.normal after)))
    (literal : NodeLiteralBranch.BranchContract (selected before owner stamp emptyParams path) closure next owner before.heap.length
      (before.heap.length + 4) stamp query emptyParams after) :
    sourceFirst budget methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩) ∧
    Contract before closure owner stamp emptyParams oldRoot path query
      ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩ := by
  obtain ⟨prefixRun, prefixContract⟩ := NodeLoopEntry.source_prefix_satisfies before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path inputs
  have state : (NodeLoopEntry.result before owner (stamp + 4) emptyParams path).state = selected before owner stamp emptyParams path := by
    simp [NodeLoopEntry.result, nonempty, selected]
  have entered : (NodeLoopEntry.result before owner (stamp + 4) emptyParams path).nodeDeclared = true := by
    simp [NodeLoopEntry.result, nonempty]
  refine ⟨?_, .branch _ after next prefixContract entered ⟨children, reads⟩ (state.symm ▸ literal)⟩
  rw [NodeLiteralBranch.parses_source, Option.map_some] at run
  simp only [sourceFirst, NodeLiteralBranch.parses_source, prefixRun]
  dsimp only [bind, pure, Option.bind, Except.bind, Except.pure]
  simp only [executeFirst, entered, Bool.not_true, Bool.false_eq_true, ↓reduceIte, state]
  rw [Option.some.inj run]
  simp [normalState, bind, Except.bind, pure, Except.pure]

theorem missing_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure) (owner stamp splitHandle emptyParams children : Nat)
    (oldRoot : Value) (path query : JSString) (next : Value)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (scope : before.privates.names = NodeClass.names stamp)
    (nonempty : NodeSearchSetup.producedParts path ≠ [])
    (reads : Lookup before owner children path next) (falsy : truthy next = false) :
    SourceBound ∧ ∃ after, sourceFirst 200 methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩) ∧
      Contract before closure owner stamp emptyParams oldRoot path query
        ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩ := by
  refine ⟨source_bound, ?_⟩
  obtain ⟨run, contract⟩ := NodeLiteralBranch.missing_satisfies 0 (selected before owner stamp emptyParams path) methods closure owner children owner
    before.heap.length (before.heap.length + 4) stamp emptyParams (firstPart path) query next
    (lookup_selected before owner children stamp emptyParams oldRoot path next scope inputs.writable reads) falsy
  exact ⟨_, combine_branch 200 before _ methods functions splitClosure closure owner stamp splitHandle emptyParams children oldRoot path query next inputs nonempty reads run contract⟩

theorem nonlast_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure) (owner children target stamp splitHandle emptyParams : Nat)
    (oldRoot oldTarget : Value) (path query : JSString)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (scope : before.privates.names = NodeClass.names stamp)
    (queryBinding : before.environment.lookup "method" = some (.string query))
    (nonempty : NodeSearchSetup.producedParts path ≠ []) (notLast : 1 ≠ (NodeSearchSetup.producedParts path).length)
    (entry : Child before owner children target stamp path oldTarget) :
    SourceBound ∧ ∃ after, sourceFirst 200 methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩) ∧
      Contract before closure owner stamp emptyParams oldRoot path query
        ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩ := by
  refine ⟨source_bound, ?_⟩
  obtain ⟨run, contract⟩ := NodeLiteralBranch.nonlast_satisfies 0 (selected before owner stamp emptyParams path) methods closure owner children target owner stamp
    before.heap.length (before.heap.length + 4) emptyParams (firstPart path) query (NodeIterationSetup.lastValue (NodeSearchSetup.producedParts path) 0)
    (targetOld owner target emptyParams oldTarget) []
    (child_selected before owner children target stamp emptyParams oldRoot oldTarget path query scope inputs.writable inputs.thisValue queryBinding entry)
    (by simp [NodeIterationSetup.lastValue, notLast]) (selected_temp_empty before owner stamp emptyParams path) (by decide)
  exact ⟨_, combine_branch 200 before _ methods functions splitClosure closure owner stamp splitHandle emptyParams children oldRoot path query (.object target)
    inputs nonempty entry.lookup run contract⟩

theorem direct_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure)
    (owner children target stamp splitHandle methodHandle emptyParams childMap keyBound : Nat)
    (oldRoot oldTarget wildcard : Value) (path query : JSString) (records : List Record)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (scope : before.privates.names = NodeClass.names stamp)
    (queryBinding : before.environment.lookup "method" = some (.string query))
    (onePart : (NodeSearchSetup.producedParts path).length = 1)
    (entry : Child before owner children target stamp path oldTarget)
    (ready : Direct before methods closure owner target stamp methodHandle childMap keyBound emptyParams query wildcard records) :
    SourceBound ∧ ∃ after, sourceFirst (ready.storage.rows.length + keyBound + 200) methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩) ∧
      Contract before closure owner stamp emptyParams oldRoot path query
        ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩ := by
  refine ⟨source_bound, ?_⟩
  have nonempty : NodeSearchSetup.producedParts path ≠ [] := by intro empty; simp [empty] at onePart
  obtain ⟨after, run, contract⟩ := NodeLiteralBranch.direct_satisfies (selected before owner stamp emptyParams path) methods closure owner children target owner stamp
    methodHandle before.heap.length (before.heap.length + 4) childMap keyBound emptyParams (firstPart path) query
    (NodeIterationSetup.lastValue (NodeSearchSetup.producedParts path) 0) (targetOld owner target emptyParams oldTarget) wildcard records []
    (child_selected before owner children target stamp emptyParams oldRoot oldTarget path query scope inputs.writable inputs.thisValue queryBinding entry)
    (by simp [NodeIterationSetup.lastValue, onePart])
    (direct_selected before methods closure owner target stamp methodHandle childMap emptyParams keyBound oldRoot path query wildcard records scope inputs.writable ready)
  exact ⟨after, combine_branch _ before after methods functions splitClosure closure owner stamp splitHandle emptyParams children oldRoot path query (.object target)
    inputs nonempty entry.lookup run contract⟩

theorem wildcard_satisfies (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (splitClosure : StringFunctionClosure) (closure : PrivateMethodClosure)
    (owner children target wildcardTarget stamp splitHandle methodHandle emptyParams childMap keyBound : Nat)
    (oldRoot oldTarget : Value) (path query : JSString) (records : List Record)
    (inputs : NodeSearchSetup.Inputs before methods functions splitClosure owner (stamp + 4) splitHandle emptyParams oldRoot path)
    (scope : before.privates.names = NodeClass.names stamp)
    (queryBinding : before.environment.lookup "method" = some (.string query))
    (onePart : (NodeSearchSetup.producedParts path).length = 1)
    (entry : Child before owner children target stamp path oldTarget)
    (ready : Wildcard before methods closure owner target wildcardTarget stamp methodHandle childMap keyBound emptyParams query records) :
    SourceBound ∧ ∃ after, sourceFirst (ready.wildcard.rows.length + ready.direct.rows.length + keyBound + 200) methods functions before =
      some (.ok ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩) ∧
      Contract before closure owner stamp emptyParams oldRoot path query
        ⟨NodeLoopEntry.result before owner (stamp + 4) emptyParams path, after⟩ := by
  refine ⟨source_bound, ?_⟩
  have nonempty : NodeSearchSetup.producedParts path ≠ [] := by intro empty; simp [empty] at onePart
  obtain ⟨after, run, contract⟩ := NodeLiteralBranch.wildcard_satisfies (selected before owner stamp emptyParams path) methods closure owner children target wildcardTarget owner stamp
    methodHandle before.heap.length (before.heap.length + 4) childMap keyBound emptyParams (firstPart path) query
    (NodeIterationSetup.lastValue (NodeSearchSetup.producedParts path) 0) (targetOld owner target emptyParams oldTarget) records []
    (child_selected before owner children target stamp emptyParams oldRoot oldTarget path query scope inputs.writable inputs.thisValue queryBinding entry)
    (by simp [NodeIterationSetup.lastValue, onePart])
    (wildcard_selected before methods closure owner target wildcardTarget stamp methodHandle childMap emptyParams keyBound oldRoot path query records scope inputs.writable ready)
  exact ⟨after, combine_branch _ before after methods functions splitClosure closure owner stamp splitHandle emptyParams children oldRoot path query (.object target)
    inputs nonempty entry.lookup run contract⟩

/-- The actual entry source105–119 parses as the first declaration followed
by exactly the separately parsed literal continuation106–119. -/
theorem entry_tail_is_literal_source :
    (parsePrivateControl NodeIterationSetup.pinnedEntrySource NodeIterationSetup.nodeBranchBindings NodePrivateCall.classPrivateNames).map
      (fun source => source.drop 1) =
      parsePrivateControl NodeLiteralBranch.pinnedSource NodeLiteralBranch.bindings NodePrivateCall.classPrivateNames := by
  rw [NodeIterationSetup.parses_node_branch, NodeLiteralBranch.parses_source]
  rfl

/-- info: 'HonoLean.Upstream.NodeFirstLiteral.wildcard_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wildcard_satisfies

end HonoLean.Upstream.NodeFirstLiteral
