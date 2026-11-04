import HonoLean.Upstream.NodeLoopEntry.Contract

namespace HonoLean.Upstream.NodeLoopEntry

open SourceSubset ECMA2025

theorem frame_refl (before : State) : HeapFrame before before := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem outer_entry_contract (before : State) : EntryContract before (outerState before) ["i"] [("i", .number 0)] :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem inner_entry_contract (before : State) (length : Nat) :
    EntryContract before (innerState before length) ["j", "len2"] [("len2", .number length), ("j", .number 0)] :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem enter_outer (before : State) : enterForHeader 32 defaultSplitLimit outerHeader before = .ok (outerState before) := by
  simp [enterForHeader, outerHeader, initializeBindings, evalExpression, outerState, bind, Except.bind, pure, Except.pure]

theorem enter_inner (before : State) (reference : Nat) (nodes : List Value)
    (binding : before.environment.lookup "curNodes" = some (.array reference))
    (found : before.heap[reference]? = some nodes) :
    enterForHeader 32 defaultSplitLimit innerHeader before = .ok (innerState before nodes.length) := by
  have clean : (withoutBindings before.environment ["j", "len2"]).lookup "curNodes" = some (.array reference) :=
    (lookup_withoutBindings before.environment ["j", "len2"] "curNodes" (by decide)).trans binding
  simp [enterForHeader, innerHeader, initializeBindings, evalExpression, lookupVariable, clean, readProperty, found,
    NodeParamLoop.lengthKey, innerState, bind, Except.bind, pure, Except.pure, List.lookup]

theorem outer_i (before : State) : (outerState before).environment.lookup "i" = some (.number 0) := by simp [outerState]

theorem outer_other (before : State) (name : String) (different : name ≠ "i") :
    (outerState before).environment.lookup name = before.environment.lookup name := by
  simpa [outerState, List.lookup_cons, beq_false_of_ne different] using
    lookup_withoutBindings before.environment ["i"] name (by simpa using different)

theorem inner_j (before : State) (length : Nat) : (innerState before length).environment.lookup "j" = some (.number 0) := by
  simp [innerState, List.lookup]

theorem inner_length (before : State) (length : Nat) :
    (innerState before length).environment.lookup "len2" = some (.number length) := by simp [innerState]

theorem inner_other (before : State) (length : Nat) (name : String) (notJ : name ≠ "j") (notLen : name ≠ "len2") :
    (innerState before length).environment.lookup name = before.environment.lookup name := by
  simpa [innerState, List.lookup_cons, beq_false_of_ne notJ, beq_false_of_ne notLen] using
    lookup_withoutBindings before.environment ["j", "len2"] name (by simpa using And.intro notJ notLen)

theorem test_outer (before : State) (length : Nat)
    (binding : before.environment.lookup "len" = some (.number length)) :
    testForHeader 32 defaultSplitLimit outerHeader (outerState before) = .ok (decide (0 < length), outerState before) := by
  have test := testForHeader_numeric 28 defaultSplitLimit outerHeader (outerState before) "i" "len" 0 length rfl
    (outer_i before) ((outer_other before "len" (by decide)).trans binding)
  simpa using test

theorem test_inner (before : State) (length : Nat) :
    testForHeader 32 defaultSplitLimit innerHeader (innerState before length) = .ok (decide (0 < length), innerState before length) := by
  have test := testForHeader_numeric 28 defaultSplitLimit innerHeader (innerState before length) "j" "len2" 0 length rfl
    (inner_j before length) (inner_length before length)
  simpa using test

theorem outer_guard_contract (before : State) (length : Nat)
    (binding : before.environment.lookup "len" = some (.number length)) :
    GuardContract (outerState before) (outerState before) "i" "len" 0 length (decide (0 < length)) :=
  ⟨outer_i before, (outer_other before "len" (by decide)).trans binding, by simp, rfl, frame_refl _⟩

theorem inner_guard_contract (before : State) (length : Nat) :
    GuardContract (innerState before length) (innerState before length) "j" "len2" 0 length (decide (0 < length)) :=
  ⟨inner_j before length, inner_length before length, by simp, rfl, frame_refl _⟩

def started (before : State) (owner identity emptyParams : Nat) (path : JSString) : State :=
  NodeSearchSetup.resultState before owner identity emptyParams (NodeSearchSetup.producedParts path)

def iterated (before : State) (owner identity emptyParams : Nat) (path : JSString) : State :=
  NodeIterationSetup.outerState (outerState (started before owner identity emptyParams path)) (NodeSearchSetup.producedParts path) 0

def selected (before : State) (owner identity emptyParams : Nat) (path : JSString) : State :=
  NodeIterationSetup.nodeState (innerState (iterated before owner identity emptyParams path) 1) [owner] 0

theorem startup_len (before : State) (owner identity emptyParams : Nat) (path : JSString) :
    (started before owner identity emptyParams path).environment.lookup "len" = some (.number (NodeSearchSetup.producedParts path).length) := by
  simp [started, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup]

/-- Actual split output is UInt32-bounded. The saved outer length and the
initial zero/singleton inner operands therefore lie inside the declared exact
integer interpretation domain; this is not general Number coercion adequacy. -/
theorem initial_header_numeric_domain (path : JSString) :
    Arithmetic.SafeInteger (NodeSearchSetup.producedParts path).length ∧ HeaderIncrementDomain 0 ∧ Arithmetic.SafeInteger 1 := by
  have bound := NodeSearchSetup.parts_length_bound path (NodeSearchSetup.producedParts path) (NodeSearchSetup.produced_parts_contract path)
  have safe := Arithmetic.denseLength_subtract_one (NodeSearchSetup.producedParts path).length bound
  refine ⟨safe.1, uint32_guard_increment_safe 0 1 (by decide) (by decide), ?_⟩
  exact (Arithmetic.denseLength_subtract_one 1 (by decide)).1

theorem iteration_from_entered (before : State) (owner identity emptyParams : Nat) (path : JSString)
    (inside : 0 < (NodeSearchSetup.producedParts path).length) :
    execute 32 defaultSplitLimit NodeIterationSetup.outerProgram (outerState (started before owner identity emptyParams path)) =
      .ok (.normal (iterated before owner identity emptyParams path)) := by
  have binding : (outerState (started before owner identity emptyParams path)).environment.lookup "parts" =
      some (.array (before.heap.length + 2)) := by
    rw [outer_other _ "parts" (by decide)]
    simp [started, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup]
  have found : (outerState (started before owner identity emptyParams path)).heap[before.heap.length + 2]? =
      some ((NodeSearchSetup.producedParts path).map Value.string) := by simp [outerState, started, NodeSearchSetup.resultState]
  exact NodeIterationSetup.execute_outer 0 defaultSplitLimit _ (before.heap.length + 2) (NodeSearchSetup.producedParts path) 0 binding found
    (outer_i _) ((outer_other _ "len" (by decide)).trans (startup_len before owner identity emptyParams path)) inside

theorem iterated_nodes_binding (before : State) (owner identity emptyParams : Nat) (path : JSString) :
    (iterated before owner identity emptyParams path).environment.lookup "curNodes" = some (.array (before.heap.length + 1)) := by
  simp [iterated, NodeIterationSetup.outerState, List.lookup]
  rw [outer_other _ "curNodes" (by decide)]
  simp [started, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup]

theorem iterated_nodes_found (before : State) (owner identity emptyParams : Nat) (path : JSString) :
    (iterated before owner identity emptyParams path).heap[before.heap.length + 1]? = some [.object owner] := by
  simp [iterated, NodeIterationSetup.outerState, outerState, started, NodeSearchSetup.resultState, List.append_assoc]

theorem inner_from_iteration (before : State) (owner identity emptyParams : Nat) (path : JSString) :
    enterForHeader 32 defaultSplitLimit innerHeader (iterated before owner identity emptyParams path) =
      .ok (innerState (iterated before owner identity emptyParams path) 1) :=
  enter_inner _ (before.heap.length + 1) [.object owner] (iterated_nodes_binding before owner identity emptyParams path)
    (iterated_nodes_found before owner identity emptyParams path)

theorem node_from_inner (before : State) (owner identity emptyParams : Nat) (path : JSString) :
    execute 32 defaultSplitLimit [NodeIterationSetup.nodeDeclaration] (innerState (iterated before owner identity emptyParams path) 1) =
      .ok (.normal (selected before owner identity emptyParams path)) := by
  have binding := (inner_other (iterated before owner identity emptyParams path) 1 "curNodes" (by decide) (by decide)).trans
    (iterated_nodes_binding before owner identity emptyParams path)
  exact NodeIterationSetup.execute_node 0 defaultSplitLimit _ (before.heap.length + 1) [owner] 0 binding
    (iterated_nodes_found before owner identity emptyParams path) (inner_j _ 1) (by simp)

end HonoLean.Upstream.NodeLoopEntry
