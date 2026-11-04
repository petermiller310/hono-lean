import HonoLean.Upstream.NodeIterationSetup.Transport
import HonoLean.Upstream.SourceSubset.Arithmetic

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset ECMA2025

theorem dense_part_read (parts : List JSString) (i : Nat) (inside : i < parts.length) :
    (parts.map Value.string)[i]?.getD .undefined = .string (selectedPart parts i) := by
  have found : parts[i]? = some parts[i] := List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
  simp [selectedPart, List.getElem?_map, found]

theorem dense_node_read (nodes : List Nat) (j : Nat) (inside : j < nodes.length) :
    (nodes.map Value.object)[j]?.getD .undefined = .object (selectedNode nodes j) := by
  have found : nodes[j]? = some nodes[j] := List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
  simp [selectedNode, List.getElem?_map, found]

/-- Signed integer subtraction is retained, including len=0 giving -1.
This equivalence does not substitute saturating Nat subtraction. -/
theorem last_index_iff (i length : Nat) : (i : Int) = (length : Int) - 1 ↔ i + 1 = length := by omega

theorem admitted_arithmetic (before : State) (partsRef nodesRef : Nat)
    (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (inputs : Inputs before partsRef nodesRef parts nodes i j) :
    Arithmetic.ExactSubtractionDomain parts.length 1 ∧ Arithmetic.SafeInteger i ∧ Arithmetic.SafeInteger j :=
  ⟨Arithmetic.denseLength_subtract_one parts.length inputs.partsBound,
    Arithmetic.denseIndex_safe i parts.length inputs.outerInside inputs.partsBound,
    Arithmetic.denseIndex_safe j nodes.length inputs.innerInside inputs.nodesBound⟩

theorem last_value_iff (parts : List JSString) (i : Nat) :
    truthy (lastValue parts i) = true ↔ i + 1 = parts.length := by simp [lastValue]

theorem eval_last (extra limit : Nat) (before : State) (parts : List JSString) (i : Nat)
    (indexBinding : before.environment.lookup "i" = some (.number i))
    (lengthBinding : before.environment.lookup "len" = some (.number parts.length)) :
    evalExpression (extra + 12) limit lastExpression before = .ok (lastValue parts i, before) := by
  have equal : (i : Int) = (parts.length : Int) - 1 ↔ i + 1 = parts.length := last_index_iff i parts.length
  simp [lastExpression, evalExpression, lookupVariable, indexBinding, lengthBinding, lastValue,
    equal, bind, Except.bind, pure, Except.pure]

theorem length_contract (before : State) (parts : List JSString) :
    LengthContract before (lengthState before parts) parts := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem outer_contract (before : State) (parts : List JSString) (i : Nat) :
    OuterContract before (outerState before parts i) parts i := by
  refine ⟨rfl, rfl, by simp, by simp [outerState], ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro reference inside
  exact List.getElem?_append_left inside

theorem node_contract (before : State) (nodes : List Nat) (j : Nat) :
    NodeContract before (nodeState before nodes j) nodes j := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem execute_length (extra limit : Nat) (before : State) (partsRef : Nat) (parts : List JSString)
    (binding : before.environment.lookup "parts" = some (.array partsRef))
    (found : before.heap[partsRef]? = some (parts.map Value.string)) :
    execute (extra + 32) limit lengthProgram before = .ok (.normal (lengthState before parts)) := by
  simp [lengthProgram, execute, evalExpression, lookupVariable, binding, readProperty, found,
    NodeParamLoop.lengthKey, lengthState, bind, Except.bind, pure, Except.pure]

theorem execute_outer (extra limit : Nat) (before : State) (partsRef : Nat) (parts : List JSString) (i : Nat)
    (binding : before.environment.lookup "parts" = some (.array partsRef))
    (found : before.heap[partsRef]? = some (parts.map Value.string))
    (indexBinding : before.environment.lookup "i" = some (.number i))
    (lengthBinding : before.environment.lookup "len" = some (.number parts.length))
    (inside : i < parts.length) :
    execute (extra + 32) limit outerProgram before = .ok (.normal (outerState before parts i)) := by
  have indexed := dense_part_read parts i inside
  simp only [List.getElem?_map] at indexed
  have partRun : evalExpression (extra + 31) limit (.index (.variable "parts") (.variable "i")) before =
      .ok (.string (selectedPart parts i), before) := by
    simp [evalExpression, lookupVariable, binding, indexBinding, readProperty, found, indexed,
      bind, Except.bind, pure, Except.pure]
  let partState := {before with environment := ("part", .string (selectedPart parts i)) :: before.environment}
  have indexAfter : partState.environment.lookup "i" = some (.number i) := by
    simpa [partState, List.lookup] using indexBinding
  have lengthAfter : partState.environment.lookup "len" = some (.number parts.length) := by
    simpa [partState, List.lookup] using lengthBinding
  have lastRun := eval_last (extra + 18) limit partState parts i indexAfter lengthAfter
  simp only [outerProgram, execute]
  rw [partRun]
  simp only [bind, Except.bind]
  rw [lastRun]
  simp [evalExpression, evalLiteralElements, outerState, partState, bind, Except.bind, pure, Except.pure]

theorem execute_node (extra limit : Nat) (before : State) (nodesRef : Nat) (nodes : List Nat) (j : Nat)
    (binding : before.environment.lookup "curNodes" = some (.array nodesRef))
    (found : before.heap[nodesRef]? = some (nodes.map Value.object))
    (indexBinding : before.environment.lookup "j" = some (.number j)) (inside : j < nodes.length) :
    execute (extra + 32) limit [nodeDeclaration] before = .ok (.normal (nodeState before nodes j)) := by
  have indexed := dense_node_read nodes j inside
  simp only [List.getElem?_map] at indexed
  simp [nodeDeclaration, execute, evalExpression, lookupVariable, binding, indexBinding,
    readProperty, found, indexed, nodeState, bind, Except.bind, pure, Except.pure]

/-- Two setup source entries, separated by the explicitly supplied i
activation. Saved length and current indexed contents remain related because
the first entry and activation preserve every array. -/
theorem setup_satisfies (before : State) (partsRef nodesRef : Nat) (parts : List JSString) (nodes : List Nat) (i j : Nat)
    (inputs : Inputs before partsRef nodesRef parts nodes i j) :
    (parseBlock pinnedSearchSource lengthBindings).map (fun source => execute 32 defaultSplitLimit source before) =
      some (.ok (.normal (lengthState before parts))) ∧
    LengthContract before (lengthState before parts) parts ∧
    (parseBlock pinnedIterationSource outerBindings).map
      (fun source => execute 32 defaultSplitLimit source (outerActivation (lengthState before parts) i)) =
      some (.ok (.normal (outerState (outerActivation (lengthState before parts) i) parts i))) ∧
    OuterContract (outerActivation (lengthState before parts) i)
      (outerState (outerActivation (lengthState before parts) i) parts i) parts i := by
  refine ⟨?_, length_contract before parts, ?_, outer_contract _ parts i⟩
  · rw [parses_length, Option.map_some, execute_length 0 defaultSplitLimit before partsRef parts inputs.partsBinding inputs.partsFound]
  · rw [parses_outer, Option.map_some]
    apply congrArg some
    exact execute_outer 0 defaultSplitLimit _ partsRef parts i
      (by simpa [outerActivation, lengthState, List.lookup] using inputs.partsBinding)
      inputs.partsFound (by simp [outerActivation]) (by simp [outerActivation, lengthState, List.lookup]) inputs.outerInside

end HonoLean.Upstream.NodeIterationSetup
