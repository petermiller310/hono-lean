import HonoLean.Upstream.NodePartOffsets.Correctness
import HonoLean.Upstream.NodeSearchSetup.Correctness

namespace HonoLean.Upstream.NodePartOffsets
open SourceSubset ECMA2025

theorem weights_join (parts : List JSString) (nonempty : parts ≠ []) :
    weights parts = ([47].intercalate parts).length + 1 := by
  induction parts with
  | nil => contradiction
  | cons head tail ih =>
    cases tail with
    | nil => simp [weights]
    | cons next rest =>
      have smaller := ih (by simp)
      simp only [weights, List.map_cons, List.sum_cons] at smaller ⊢
      simp only [List.intercalate_cons_cons, List.length_append, List.length_cons, List.length_nil]
      omega

theorem parts_length_le_weights (parts : List JSString) : parts.length ≤ weights parts := by
  induction parts with
  | nil => simp [weights]
  | cons head tail ih => simp only [List.length_cons, weights, List.map_cons, List.sum_cons] at *; omega

theorem split_length_bound (path : JSString) : (path.splitOn 47).length ≤ path.length + 1 := by
  have bound := parts_length_le_weights (path.splitOn 47)
  rw [weights_join _ (List.splitOn_ne_nil _ _), List.intercalate_splitOn] at bound
  exact bound

theorem producedParts_complete (path : JSString) (bound : path.length < defaultSplitLimit) :
    NodeSearchSetup.producedParts path = dropLeadingEmpty (path.splitOn 47) := by
  unfold NodeSearchSetup.producedParts
  rw [List.take_of_length_le (by have := split_length_bound path; omega)]

def leadingUnits (path : JSString) : JSString := if path[0]? = some 47 then [47] else []

theorem leadingUnits_length (path : JSString) : (leadingUnits path).length = initialOffset path := by
  unfold leadingUnits initialOffset
  split <;> rfl

theorem split_reassemble (path : JSString) :
    path = leadingUnits path ++ [47].intercalate (dropLeadingEmpty (path.splitOn 47)) := by
  cases path with
  | nil => rfl
  | cons unit tail =>
    by_cases slash : unit = 47
    · subst unit
      simp [leadingUnits, List.splitOn_cons_eq_ite_modifyHead, dropLeadingEmpty, List.intercalate_splitOn]
    · have fields := List.splitOn_ne_nil (47 : UInt16) tail
      cases eq : tail.splitOn 47 with
      | nil => exact False.elim (fields eq)
      | cons head rest =>
        have joined := List.intercalate_splitOn (xs := unit :: tail) (47 : UInt16)
        simpa [leadingUnits, slash, List.splitOn_cons_eq_ite_modifyHead, eq, dropLeadingEmpty] using joined.symm

def prefixUnits (parts : List JSString) (index : Nat) : JSString :=
  (parts.take index).flatMap (fun part => part ++ [47])

theorem prefixUnits_length (parts : List JSString) (index : Nat) :
    (prefixUnits parts index).length = weights (parts.take index) := by
  simp [prefixUnits, weights, List.length_flatMap]

theorem join_prefix (parts : List JSString) (index : Nat) (inside : index < parts.length) :
    [47].intercalate parts = prefixUnits parts index ++ [47].intercalate (parts.drop index) := by
  induction parts generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => simp [prefixUnits]
    | succ index =>
      have bound : index < tail.length := by simpa using inside
      have nonempty : tail ≠ [] := by intro same; simp [same] at bound
      cases tail with
      | nil => contradiction
      | cons next rest =>
        rw [List.intercalate_cons_cons, ih index bound]
        simp [prefixUnits, List.append_assoc]

theorem aligned_suffix (path : JSString) (parts : List JSString)
    (split : SplitPathContract defaultSplitLimit path parts) (bound : path.length < defaultSplitLimit)
    (index : Nat) (inside : index < parts.length) :
    offsetAt path parts index ≤ path.length ∧ path.drop (offsetAt path parts index) = [47].intercalate (parts.drop index) := by
  have actual := (contract_iff defaultSplitLimit path parts).mp split
  have complete : parts = dropLeadingEmpty (path.splitOn 47) := by
    rw [← producedParts_complete path bound]
    exact actual
  have joined : path = leadingUnits path ++ (prefixUnits parts index ++ [47].intercalate (parts.drop index)) := by
    calc
      path = leadingUnits path ++ [47].intercalate parts := by simpa [← complete] using split_reassemble path
      _ = _ := congrArg (leadingUnits path ++ ·) (join_prefix parts index inside)
  have lengthPrefix : (leadingUnits path ++ prefixUnits parts index).length = offsetAt path parts index := by
    simp [leadingUnits_length, prefixUnits_length, offsetAt]
  have decomposed : path = (leadingUnits path ++ prefixUnits parts index) ++ [47].intercalate (parts.drop index) := by
    simpa only [List.append_assoc] using joined
  constructor
  · have sized := congrArg List.length decomposed
    simp only [List.length_append, lengthPrefix] at sized
    omega
  · have dropped := congrArg (List.drop (offsetAt path parts index)) decomposed
    rw [← lengthPrefix, List.drop_left] at dropped
    simpa [lengthPrefix] using dropped

theorem cumulative_final_bound (path : JSString) (parts : List JSString)
    (split : SplitPathContract defaultSplitLimit path parts) (bound : path.length < defaultSplitLimit) :
    initialOffset path + weights parts ≤ path.length + 1 := by
  have actual := (contract_iff defaultSplitLimit path parts).mp split
  have complete : parts = dropLeadingEmpty (path.splitOn 47) := by
    rw [← producedParts_complete path bound]
    exact actual
  cases parts with
  | nil => unfold initialOffset; split <;> simp [weights] <;> omega
  | cons head tail =>
    have joined : path = leadingUnits path ++ [47].intercalate (head :: tail) := by
      simpa [← complete] using split_reassemble path
    have sized := congrArg List.length joined
    rw [List.length_append, leadingUnits_length] at sized
    rw [weights_join _ (by simp)]
    omega

/-- Actual startup supplies arrays, saved len and the null cache. This separate
activation supplies only the requested i; reaching source146 from the omitted
pattern branch remains outside the theorem. -/
def indexActivation (state : State) (index : Nat) : State :=
  {state with environment := ("i", .number index) :: state.environment}

theorem startup_fresh_inputs (before after : State) (owner identity emptyParams : Nat) (old : Value)
    (path : JSString) (parts : List JSString) (startup : NodeSearchSetup.StartupContract before after owner identity emptyParams old path parts)
    (pathRead : before.environment.lookup "path" = some (.string path))
    (bound : path.length < defaultSplitLimit) (index : Nat) :
    FreshInputs (indexActivation after index) (before.heap.length + 2) path parts [("i", .number index)]
      ((NodeSearchSetup.resultEnvironment before owner parts).tail) := by
  have finalBound := cumulative_final_bound path parts startup.split bound
  have partBound : parts.length ≤ maximumArrayLength := by
    have := parts_length_le_weights parts
    change parts.length ≤ 4294967295
    change path.length < 4294967295 at bound
    omega
  refine ⟨?_, by simp, ?_, ?_, startup.partsFound, ?_, partBound, ?_⟩
  · simp [indexActivation, startup.environment, NodeSearchSetup.resultEnvironment]
  · simp only [indexActivation, List.lookup_cons]
    simp only [startup.environment, NodeSearchSetup.resultEnvironment, List.cons_append, List.nil_append, List.lookup_cons]
    exact pathRead
  · simp [indexActivation, startup.environment, NodeSearchSetup.resultEnvironment, List.lookup]
  · simp [indexActivation, startup.environment, NodeSearchSetup.resultEnvironment, List.lookup]
  · change (initialOffset path : Int) + weights parts ≤ Arithmetic.maximumSafeInteger
    unfold Arithmetic.maximumSafeInteger
    change path.length < 4294967295 at bound
    omega

def sourceStartup (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) :=
  (parseFunctionStatements NodeSearchSetup.pinnedSource NodeSearchSetup.bindings NodePrivateCall.classPrivateNames true).map
    (fun source => executeFunctionStatements 100 defaultSplitLimit methods functions source before)

/-- Two actual source activations. No produced parts, len, null cache or offset
table is an input. The size bound explicitly removes split's native limit. -/
theorem startup_offsets_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString) (index : Nat)
    (inputs : NodeSearchSetup.Inputs before methods functions closure owner identity handle emptyParams old path)
    (bound : path.length < defaultSplitLimit) (inside : index < (NodeSearchSetup.producedParts path).length) :
    let parts := NodeSearchSetup.producedParts path
    let startup := NodeSearchSetup.resultState before owner identity emptyParams parts
    let active := indexActivation startup index
    let front := [("i", .number index)]
    let back := (NodeSearchSetup.resultEnvironment before owner parts).tail
    let prepared := prepareState active front back path parts
    let output := [47].intercalate (parts.drop index)
    sourceStartup before methods functions = some (.ok (.normal startup)) ∧
    NodeSearchSetup.StartupContract before startup owner identity emptyParams old path parts ∧
    sourceOffsets (extra + parts.length + 80) active = some (.ok (sliceState prepared output)) ∧
    PreparedContract active prepared path parts ∧
    CachedContract prepared (sliceState prepared output) active.heap.length (tableValues path parts parts.length)
      path index (offsetAt path parts index) ∧
    offsetAt path parts index ≤ path.length ∧ path.drop (offsetAt path parts index) = output := by
  dsimp only
  obtain ⟨run, startup⟩ := NodeSearchSetup.startup_satisfies before methods functions closure owner identity handle emptyParams old path inputs
  have fresh := startup_fresh_inputs before _ owner identity emptyParams old path _ startup inputs.pathBinding bound index
  have executed := source_fresh_satisfies extra _ _ path _ _ _ fresh index inside (by simp [indexActivation])
  have suffix := aligned_suffix path _ startup.split bound index inside
  refine ⟨run, startup, ?_, ?_, ?_, suffix⟩
  · simpa only [suffix.2] using executed.1
  · exact executed.2.1
  · simpa only [suffix.2] using executed.2.2

/-- A later explicit fragment activation reuses the table actually created by
its first source execution. Correct cached contents are derived here; none are
supplied as a second-call premise. No intervening mutation/reachability claim. -/
theorem source_fresh_then_cached (extra : Nat) (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) (inputs : FreshInputs before partsRef path parts front back)
    (split : SplitPathContract defaultSplitLimit path parts) (bound : path.length < defaultSplitLimit)
    (firstIndex nextIndex : Nat) (firstInside : firstIndex < parts.length) (nextInside : nextIndex < parts.length)
    (firstRead : before.environment.lookup "i" = some (.number firstIndex)) :
    let prepared := prepareState before front back path parts
    let first := sliceState prepared ([47].intercalate (parts.drop firstIndex))
    let next := indexActivation first nextIndex
    let last := sliceState next ([47].intercalate (parts.drop nextIndex))
    sourceOffsets (extra + parts.length + 80) before = some (.ok first) ∧
    sourceOffsets (extra + 64) next = some (.ok last) ∧
    CachedContract next last before.heap.length (tableValues path parts parts.length) path nextIndex (offsetAt path parts nextIndex) ∧
    last.heap = prepared.heap ∧ last.environment.lookup "partOffsets" = some (.array before.heap.length) := by
  dsimp only
  have firstSuffix := (aligned_suffix path parts split bound firstIndex firstInside).2
  have nextSuffix := (aligned_suffix path parts split bound nextIndex nextInside).2
  have first := source_fresh_satisfies extra before partsRef path parts front back inputs firstIndex firstInside firstRead
  have nextInputs : CachedInputs
      (indexActivation (sliceState (prepareState before front back path parts) ([47].intercalate (parts.drop firstIndex))) nextIndex)
      before.heap.length (tableValues path parts parts.length) path nextIndex (offsetAt path parts nextIndex) := by
    refine ⟨?_, by simp [indexActivation, sliceState, prepareState], ?_, by simp [indexActivation], ?_,
      Nat.lt_of_lt_of_le nextInside inputs.partsBound, by simpa [tableValues_length] using inputs.partsBound,
      offsetAt_safe before partsRef path parts front back inputs nextIndex⟩
    · simpa [indexActivation, sliceState, prepareState, List.lookup_cons] using updated_cache before front back inputs.first
    · simpa [indexActivation, sliceState, prepareState, List.lookup_cons] using
        (updated_lookup_other before front back inputs.reference "path" (by decide)).trans inputs.pathBinding
    · rw [(tableValues_cumulative path parts).index nextIndex nextInside]
      rfl
  have later := source_cached_satisfies extra _ before.heap.length _ path nextIndex (offsetAt path parts nextIndex) nextInputs
  refine ⟨by simpa only [firstSuffix] using first.1, ?_, ?_, rfl, ?_⟩
  · simpa only [stringSlice_from_nat, nextSuffix] using later.1
  · simpa only [stringSlice_from_nat, nextSuffix] using later.2
  · simpa only [stringSlice_from_nat, nextSuffix] using later.2.cacheBinding

/-- info: 'HonoLean.Upstream.NodePartOffsets.startup_offsets_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_offsets_satisfies
/-- info: 'HonoLean.Upstream.NodePartOffsets.source_fresh_then_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_fresh_then_cached
/-- info: 'HonoLean.Upstream.NodePartOffsets.aligned_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aligned_suffix

end HonoLean.Upstream.NodePartOffsets
