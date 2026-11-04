import HonoLean.Upstream.NodeComponentCount.Contract

namespace HonoLean.Upstream.NodeComponentCount

open SourceSubset ECMA2025

theorem slashRun_contract (input : JSString) : UnitMatchContract input 47 (slashRun input) :=
  executeUnitGlobal_satisfies input ⟨47, 0⟩

theorem slashCount_bound (input : JSString) : slashCount input ≤ input.length :=
  matchingPositions_length_le 47 input

theorem slashCount_legal_index (input : JSString) (bound : input.length < maximumArrayLength) :
    slashCount input < maximumArrayLength := Nat.lt_of_le_of_lt (slashCount_bound input) bound

theorem count_contract (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) : CountContract before (countState before input) input := by
  have execution := slashRun_contract input
  refine ⟨⟨m, matched, inputs⟩, matchingPositions_ordered 47 input, matchingPositions_member 47 input, slashCount_bound input,
    rfl, rfl, rfl, by simp, by simp [countState], ?_, rfl, execution, rfl, ?_⟩
  · intro reference inside
    exact List.getElem?_append_left inside
  · by_cases zero : slashCount input = 0
    · left
      refine ⟨zero, by simp [matchResult, zero], ?_⟩
      rw [execution.positions]
      exact List.length_eq_zero_iff.mp zero
    · right
      refine ⟨Nat.pos_of_ne_zero zero, by simp [matchResult, zero], ?_⟩
      intro empty
      have length := congrArg List.length empty
      rw [execution.positions] at length
      exact zero length

theorem source_receiver (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) :
    evalSparseExpression (extra + 96) (.index (.variable "m") (.number 0)) before.arrays =
      .ok (.string input, before.arrays) := by
  simp [evalSparseExpression, inputs.binding, inputs.found, sparseRead, numericGet, inputs.input,
    maximumArrayLength, bind, pure, Except.bind, Except.pure]

/-- The actual match subexpression returns null for no slashes and the tracked
accumulator reference otherwise. The accumulator exists in both cases. -/
theorem execute_match (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) (legal : input.length ≤ maximumArrayLength) :
    evalRegExpExpression (extra + 97)
      (.stringMatch (.index (.variable "m") (.number 0)) (.literal 47)) before =
        .ok (.ordinary (matchResult before input), unitLiteralMatchState before 47 input) := by
  let literalState : RegExpState := {before with regexps := before.regexps ++ [⟨47, 0⟩]}
  have found : literalState.regexps[before.regexps.length]? = some ⟨47, 0⟩ := by simp [literalState]
  have called := matchUnitRegExp_found literalState before.regexps.length input ⟨47, 0⟩ found legal
  have endpoint : unitMatchState literalState before.regexps.length input ⟨47, 0⟩ = unitLiteralMatchState before 47 input := by
    simp [unitMatchState, unitLiteralMatchState, literalState, List.set_append_right]
  simp only [evalRegExpExpression, source_receiver extra before m matched input inputs, bind, pure, Except.bind, Except.pure]
  rw [called, endpoint]
  cases positions : matchingPositions 47 input with
  | nil => simp [unitMatchValues, positions, matchResult, slashCount, slashPositions]
  | cons first rest => simp [unitMatchValues, positions, matchResult, slashCount, slashPositions, literalState]

theorem execute_initializer (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) (legal : input.length ≤ maximumArrayLength) :
    evalRegExpExpression (extra + 99) initializer before =
      .ok (.ordinary (.number (slashCount input)), unitLiteralMatchState before 47 input) := by
  simpa [unitCountExpression, initializer, slashCount, slashPositions] using
    evalRegExp_count (extra + 93) (.index (.variable "m") (.number 0)) before 47 input
      (source_receiver extra before m matched input inputs) legal

theorem execute_count (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) (legal : input.length ≤ maximumArrayLength) :
    executeRegExpSequence (extra + 100) program before = .ok (countState before input) := by
  simp only [program, executeRegExpSequence]
  rw [execute_initializer extra before m matched input inputs legal]
  simp [countState, accumulator, unitLiteralMatchState, unitMatchValues, slashRun, slashCount, slashPositions,
    List.map_const', bind, Except.bind]

/-- Public count theorem starts at the actual input match array and string.
No componentCount binding, match result, or completed regex state is supplied. -/
theorem source_count_satisfies (extra : Nat) (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString)
    (inputs : Inputs before m matched input) (legal : input.length ≤ maximumArrayLength) :
    sourceCount (extra + 100) before = some (.ok (countState before input)) ∧
    CountContract before (countState before input) input := by
  refine ⟨?_, count_contract before m matched input inputs⟩
  simpa [sourceCount, parses_source] using congrArg some (execute_count extra before m matched input inputs legal)

end HonoLean.Upstream.NodeComponentCount
