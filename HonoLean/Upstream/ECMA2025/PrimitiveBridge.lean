import HonoLean.Upstream.ECMA2025.StringSplit
import HonoLean.Upstream.ECMA2025.DenseArray
import HonoLean.Upstream.SourceSubset.SplitPath

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-- The fixed function's observable path through the detailed primitive models.
This is a second formal description, not a new TypeScript frontend or a native
engine semantics. The source connection is proved below, never assumed. -/
def splitPathSteps (input : JSString) (limit : Nat) : Except EvalError (List Value) := do
  let array := ofList ((stringSplit input 47 limit).map Value.string)
  let shift ← equalsEmpty (numericGet array 0)
  return observe (if shift then (shiftSteps array).2 else array)

private theorem get_zero_ofList (elements : List Value) :
    numericGet (ofList elements) 0 = elements.headD .undefined := by
  cases elements <;> rfl

theorem splitPathSteps_refines (input : JSString) (limit : Nat) :
    splitPathSteps input limit =
      .ok ((dropLeadingEmpty ((input.splitOn (47 : UInt16)).take limit)).map Value.string) := by
  unfold splitPathSteps
  rw [stringSplit_refines]
  generalize parts : (input.splitOn (47 : UInt16)).take limit = fields
  cases fields with
  | nil =>
    simp [get_zero_ofList, equalsEmpty, observe_ofList, dropLeadingEmpty,
      bind, pure, Except.bind, Except.pure]
  | cons first remaining =>
    cases first with
    | nil =>
      simp [get_zero_ofList, equalsEmpty, shiftSteps_ofList, observe_ofList,
        dropLeadingEmpty, bind, pure, Except.bind, Except.pure]
    | cons unit rest =>
      simp [get_zero_ofList, equalsEmpty, observe_ofList, dropLeadingEmpty,
        bind, pure, Except.bind, Except.pure]

/-- The source parser and existing evaluator are linked to the cursor-based
split and indexed-property mutation model for every mathematical input/limit. -/
theorem parsed_source_refines_steps (input : JSString) (limit : Nat) :
    (parse pinnedSource).map (fun program => run program input limit) =
      some (splitPathSteps input limit) := by
  rw [parses_pinned_source, Option.map_some, run_splitPath, splitPathSteps_refines]

theorem steps_contract_iff (input : JSString) (output : List JSString) :
    splitPathSteps input defaultSplitLimit = .ok (output.map Value.string) ↔
      SplitPathContract defaultSplitLimit input output := by
  rw [splitPathSteps_refines, contract_iff]
  simp only [Except.ok.injEq]
  rw [List.map_inj_right (fun _ _ equal => Value.string.inj equal)]
  exact eq_comm

/-- Default splitting always creates an array of legal ECMAScript Array length.
LegalString, standard realm/dispatch, ordinary data properties and successful
allocation are still required by the intended native interpretation. -/
theorem default_split_legal_array (input : JSString) :
    LegalArrayLength (ofList ((stringSplit input 47 defaultSplitLimit).map Value.string)) := by
  simpa [LegalArrayLength, ofList, maximumArrayLength, defaultSplitLimit] using
    stringSplit_length_le input 47 defaultSplitLimit

/-- info: 'HonoLean.Upstream.ECMA2025.parsed_source_refines_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_refines_steps

end HonoLean.Upstream.ECMA2025
