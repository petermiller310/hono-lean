import HonoLean.Upstream.SourceSubset.Semantics
import Init.Data.List.Nat.Range

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-! Fixed global, non-Unicode, one-code-unit atom specialization of ECMA2025
RegExpBuiltinExec / RegExp.prototype[@@match]. No captures, zero-width matches,
Unicode flags, coercions, custom exec, getters or arbitrary regex grammar. The
scan advances through UTF16 code units and records successful lastIndex writes;
the final failed global exec resets lastIndex to zero. -/

structure UnitRegExpCell where
  unit : UInt16
  lastIndex : Nat := 0
  deriving Repr, DecidableEq

structure UnitScan where
  positions : List Nat
  lastIndex : Nat
  writes : List Nat
  deriving Repr, DecidableEq

/-- Operational left-to-right atom scan. A hit records its start and writes
one past it; exhaustion performs the final global-exec lastIndex reset. -/
def scanUnit (unit : UInt16) (cursor : Nat) : JSString → Nat → UnitScan
  | [], _ => ⟨[], 0, [0]⟩
  | head :: rest, lastIndex =>
    if head = unit then
      let suffix := scanUnit unit (cursor + 1) rest (cursor + 1)
      ⟨cursor :: suffix.positions, suffix.lastIndex, (cursor + 1) :: suffix.writes⟩
    else scanUnit unit (cursor + 1) rest lastIndex

/-- Independent specification: enumerate all input positions, select matching
code units, and project the ascending indices. This does not call scanUnit. -/
def matchingPositionsFrom (unit : UInt16) (start : Nat) (input : JSString) : List Nat :=
  ((input.zipIdx start).filter (fun entry => entry.1 == unit)).map Prod.snd

def matchingPositions (unit : UInt16) (input : JSString) : List Nat := matchingPositionsFrom unit 0 input

theorem scanUnit_positions (unit : UInt16) (input : JSString) (cursor lastIndex : Nat) :
    (scanUnit unit cursor input lastIndex).positions = matchingPositionsFrom unit cursor input := by
  induction input generalizing cursor lastIndex with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : head = unit <;> simp [scanUnit, matchingPositionsFrom, same, ih]

theorem scanUnit_final_zero (unit : UInt16) (input : JSString) (cursor lastIndex : Nat) :
    (scanUnit unit cursor input lastIndex).lastIndex = 0 := by
  induction input generalizing cursor lastIndex with
  | nil => rfl
  | cons head rest ih => by_cases same : head = unit <;> simp [scanUnit, same, ih]

theorem scanUnit_writes (unit : UInt16) (input : JSString) (cursor lastIndex : Nat) :
    (scanUnit unit cursor input lastIndex).writes =
      (scanUnit unit cursor input lastIndex).positions.map (· + 1) ++ [0] := by
  induction input generalizing cursor lastIndex with
  | nil => rfl
  | cons head rest ih => by_cases same : head = unit <;> simp [scanUnit, same, ih]

theorem matchingPositions_length_le (unit : UInt16) (input : JSString) :
    (matchingPositions unit input).length ≤ input.length := by
  simpa [matchingPositions, matchingPositionsFrom] using
    List.length_filter_le (fun entry : UInt16 × Nat => entry.1 == unit) (input.zipIdx 0)

theorem matchingPositions_member (unit : UInt16) (input : JSString) (index : Nat) :
    index ∈ matchingPositions unit input ↔ input[index]? = some unit := by
  simp [matchingPositions, matchingPositionsFrom, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?]

theorem matchingPositions_ordered (unit : UInt16) (input : JSString) :
    (matchingPositions unit input).Pairwise (· < ·) := by
  have sub := (List.filter_sublist (p := fun entry : UInt16 × Nat => entry.1 == unit) (l := input.zipIdx 0)).map Prod.snd
  rw [List.zipIdx_map_snd] at sub
  exact List.Pairwise.sublist sub (List.pairwise_lt_range' (s := 0) (n := input.length))

structure UnitExecution where
  positions : List Nat
  cell : UnitRegExpCell
  lastIndexWrites : List Nat
  deriving Repr, DecidableEq

/-- Global @@match resets lastIndex before the first exec, independently of
its incoming value. The scanner records all later writes, including final0. -/
def executeUnitGlobal (input : JSString) (cell : UnitRegExpCell) : UnitExecution :=
  let run := scanUnit cell.unit 0 input 0
  ⟨run.positions, {cell with lastIndex := run.lastIndex}, 0 :: run.writes⟩

structure UnitMatchContract (input : JSString) (unit : UInt16) (run : UnitExecution) : Prop where
  positions : run.positions = matchingPositions unit input
  members : ∀ index, index ∈ run.positions ↔ input[index]? = some unit
  ordered : run.positions.Pairwise (· < ·)
  countBound : run.positions.length ≤ input.length
  unitKept : run.cell.unit = unit
  lastIndexZero : run.cell.lastIndex = 0
  writes : run.lastIndexWrites = 0 :: (run.positions.map (· + 1) ++ [0])

theorem executeUnitGlobal_satisfies (input : JSString) (cell : UnitRegExpCell) :
    UnitMatchContract input cell.unit (executeUnitGlobal input cell) := by
  have positions : (executeUnitGlobal input cell).positions = matchingPositions cell.unit input :=
    scanUnit_positions cell.unit input 0 0
  refine ⟨positions, ?_, ?_, ?_, rfl, scanUnit_final_zero cell.unit input 0 0, ?_⟩
  · intro index
    rw [show (executeUnitGlobal input cell).positions = matchingPositions cell.unit input from positions]
    exact matchingPositions_member cell.unit input index
  · rw [positions]
    exact matchingPositions_ordered cell.unit input
  · rw [positions]
    exact matchingPositions_length_le cell.unit input
  · exact congrArg (0 :: ·) (scanUnit_writes cell.unit input 0 0)

end HonoLean.Upstream.ECMA2025
