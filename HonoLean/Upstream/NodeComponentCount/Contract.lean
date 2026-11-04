import HonoLean.Upstream.NodeComponentCount.Source

namespace HonoLean.Upstream.NodeComponentCount

open SourceSubset ECMA2025

/-- Earlier source156's matcher.exec result remains an input boundary. This fragment
starts with its actual array and own primitive UTF16 string at index0. -/
structure Inputs (before : RegExpState) (m : Nat) (matched : IndexedArray) (input : JSString) : Prop where
  binding : before.arrays.environment.lookup "m" = some (.array m)
  found : before.arrays.heap[m]? = some matched
  input : matched.own 0 = some (.string input)
  wellFormed : WellFormedIndexed matched
  legalLength : LegalArrayLength matched

/-- Independent specification: all slash positions in ascending UTF16 order.
The executable scanner is separately proved to agree with this enumeration. -/
def slashPositions (input : JSString) : List Nat := matchingPositions 47 input
def slashCount (input : JSString) : Nat := (slashPositions input).length
def slashRun (input : JSString) : UnitExecution := executeUnitGlobal input ⟨47, 0⟩
def accumulator (input : JSString) : IndexedArray := ofList (List.replicate (slashCount input) (.string [47]))
def matchResult (before : RegExpState) (input : JSString) : Value :=
  if slashCount input = 0 then .null else .array before.arrays.heap.length

def countState (before : RegExpState) (input : JSString) : RegExpState :=
  {arrays :=
    {environment := ("componentCount", .number (slashCount input)) :: before.arrays.environment
     heap := before.arrays.heap ++ [accumulator input]}
   regexps := before.regexps ++ [⟨47, 0⟩]
   executions := before.executions ++ [slashRun input]}

/-- One tracked global-match accumulator exists even when the returned match
is null. Per-exec internal result arrays are recorded only by the execution
trace, so this is not a total native-allocation theorem. -/
structure CountContract (before after : RegExpState) (input : JSString) : Prop where
  initialInput : ∃ m matched, Inputs before m matched input
  positionsOrdered : (slashPositions input).Pairwise (· < ·)
  positionsComplete : ∀ index, index ∈ slashPositions input ↔ input[index]? = some 47
  countBound : slashCount input ≤ input.length
  environment : after.arrays.environment = ("componentCount", .number (slashCount input)) :: before.arrays.environment
  countBinding : after.arrays.environment.lookup "componentCount" = some (.number (slashCount input))
  heap : after.arrays.heap = before.arrays.heap ++ [accumulator input]
  accumulatorFresh : before.arrays.heap[before.arrays.heap.length]? = none
  accumulatorFound : after.arrays.heap[before.arrays.heap.length]? = some (accumulator input)
  oldArrays : ∀ reference, reference < before.arrays.heap.length → after.arrays.heap[reference]? = before.arrays.heap[reference]?
  regexps : after.regexps = before.regexps ++ [⟨47, 0⟩]
  execution : UnitMatchContract input 47 (slashRun input)
  executions : after.executions = before.executions ++ [slashRun input]
  resultBranch : (slashCount input = 0 ∧ matchResult before input = .null ∧ (slashRun input).positions = []) ∨
    (0 < slashCount input ∧ matchResult before input = .array before.arrays.heap.length ∧ (slashRun input).positions ≠ [])

end HonoLean.Upstream.NodeComponentCount
