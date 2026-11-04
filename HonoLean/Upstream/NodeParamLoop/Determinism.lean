import HonoLean.Upstream.NodeParamLoop.Contract

namespace HonoLean.Upstream.NodeParamLoop

open SourceSubset ECMA2025

/-- Functional selection follows from the independent disjoint cases, without
exposing an evaluator-defined selector in the public contract. -/
theorem selected_unique (parameter node : Value) (index : Int) (left right : Value)
    (first : NodeParamAssignment.Selected parameter node index left)
    (second : NodeParamAssignment.Selected parameter node index right) : left = right := by
  by_cases truth : NodeParamAssignment.Truthy parameter <;>
    by_cases zero : index = 0 <;>
    by_cases nullish : NodeParamAssignment.Nullish node <;>
    simp [NodeParamAssignment.Selected, truth, zero, nullish] at first second <;>
    exact first.trans second.symm

theorem captures_unique {snapshot : Snapshot} {count : Nat} {left right : List (JSString × Value)}
    (first : Captures snapshot count left) (second : Captures snapshot count right) : left = right := by
  induction first generalizing right with
  | empty => cases second; rfl
  | @step count entries key value prior atKey selected ih =>
    cases second with
    | @step _ otherEntries otherKey otherValue otherPrior otherAtKey otherSelected =>
      have sameKey : key = otherKey := Option.some.inj (atKey.symm.trans otherAtKey)
      subst otherKey
      have sameValue := selected_unique (snapshot.parameter key) (snapshot.node key) (count : Int)
        value otherValue selected otherSelected
      have sameEntries := ih otherPrior
      simp [sameEntries, sameValue]

theorem prefix_unique {snapshot : Snapshot} {count : Nat} {left right : OrdinaryObject}
    (first : Prefix snapshot count left) (second : Prefix snapshot count right) : left = right := by
  obtain ⟨leftEntries, leftCaptures, rfl⟩ := first
  obtain ⟨rightEntries, rightCaptures, rfl⟩ := second
  rw [captures_unique leftCaptures rightCaptures]

theorem block_contract_unique (before left right : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets : Nat) (priorHandlers : List Value) (snapshot : Snapshot)
    (first : BlockContract before left handlerSet handler handlerSets priorHandlers snapshot)
    (second : BlockContract before right handlerSet handler handlerSets priorHandlers snapshot) : left = right := by
  obtain ⟨leftOutput, leftPrefix, rfl⟩ := first
  obtain ⟨rightOutput, rightPrefix, rfl⟩ := second
  rw [prefix_unique leftPrefix rightPrefix]

/-- info: 'HonoLean.Upstream.NodeParamLoop.block_contract_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_contract_unique

end HonoLean.Upstream.NodeParamLoop
