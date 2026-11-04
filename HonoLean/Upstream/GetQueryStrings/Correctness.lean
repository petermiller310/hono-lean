import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.GetQueryStrings.Generated

namespace HonoLean.Upstream.GetQueryStrings

open SourceSubset

def queryProgram : Function :=
  ⟨"getQueryStrings", "url", [
    .declare "queryIndex" (.call (.variable "url") "indexOf" [.string [63], .number 8]),
    .branch (.strictEqual (.variable "queryIndex") (.number (-1))) [.ret (.string [])],
    .declare "hashIndex" (.call (.variable "url") "indexOf" [.string [35], .number 8]),
    .ret (.conditional
      (.strictEqual (.variable "hashIndex") (.number (-1)))
      (.call (.variable "url") "slice" [.variable "queryIndex"])
      (.conditional (.compare .less (.variable "queryIndex") (.variable "hashIndex"))
        (.call (.variable "url") "slice" [.variable "queryIndex", .variable "hashIndex"])
        (.string [])))]⟩

set_option maxRecDepth 65536 in
/-- The full pinned function text, including signed literals, lazy conditionals,
method arguments and string annotations, is parsed by the shared Lean parser. -/
theorem parses_pinned_source : parseString pinnedSource = some queryProgram := by cbv

/-- An eligible marker is the first occurrence at or after code-unit offset8.
This indexed occurrence/minimality contract neither runs the source evaluator
nor imposes URL validity, decoding, scalar-Unicode, or HTTP assumptions. -/
def FirstFrom (input : JSString) (marker : UInt16) (index : Nat) : Prop :=
  8 ≤ index ∧ input[index]? = some marker ∧
    ∀ earlier, 8 ≤ earlier → earlier < index → input[earlier]? ≠ some marker

def MissingFrom (input : JSString) (marker : UInt16) : Prop :=
  ∀ index, 8 ≤ index → input[index]? ≠ some marker

/-- Include the leading question mark. The first eligible hash is searched
independently from offset8, so an earlier eligible hash suppresses the query. -/
def QueryStringsContract (input output : JSString) : Prop :=
  (MissingFrom input 63 ∧ output = []) ∨
    ∃ query, FirstFrom input 63 query ∧
      ((MissingFrom input 35 ∧ output = input.drop query) ∨
       ∃ hash, FirstFrom input 35 hash ∧
         ((query < hash ∧ output = (input.drop query).take (hash - query)) ∨
          (hash ≤ query ∧ output = [])))

/-- A compact description of the already-parsed execution, used only to state
the refinement lemma. The independent contract above uses occurrence witnesses. -/
def queryOutput (input : JSString) : JSString :=
  let query := ECMA2025.stringIndexOf input 63 8
  if query = -1 then []
  else
    let hash := ECMA2025.stringIndexOf input 35 8
    if hash = -1 then ECMA2025.stringSlice input query none
    else if query < hash then ECMA2025.stringSlice input query (some hash) else []

theorem run_queryStrings (input : JSString) (limit : Nat) :
    runString queryProgram input limit = .ok (queryOutput input) := by
  by_cases noQuery : ECMA2025.stringIndexOf input 63 8 = -1
  · simp [runString, queryProgram, execute, evalExpression, evalArguments,
      lookupVariable, List.lookup, intrinsic, noQuery, queryOutput,
      bind, pure, Except.bind, Except.pure]
  · by_cases noHash : ECMA2025.stringIndexOf input 35 8 = -1
    · simp [runString, queryProgram, execute, evalExpression, evalArguments,
        lookupVariable, List.lookup, intrinsic, noQuery, noHash, queryOutput,
        bind, pure, Except.bind, Except.pure]
    · by_cases ordered : ECMA2025.stringIndexOf input 63 8 < ECMA2025.stringIndexOf input 35 8
      · simp [runString, queryProgram, execute, evalExpression, evalArguments,
          lookupVariable, List.lookup, intrinsic, noQuery, noHash, ordered, compareNumbers, queryOutput,
          bind, pure, Except.bind, Except.pure]
      · simp [runString, queryProgram, execute, evalExpression, evalArguments,
          lookupVariable, List.lookup, intrinsic, noQuery, noHash, ordered, compareNumbers, queryOutput,
          bind, pure, Except.bind, Except.pure]

theorem queryOutput_satisfies (input : JSString) :
    QueryStringsContract input (queryOutput input) := by
  rcases ECMA2025.stringIndexOf_result input 63 8 with noQuery | ⟨query, foundQuery⟩
  · left
    exact ⟨(ECMA2025.stringIndexOf_from_nat_missing_iff input 63 8).mp noQuery,
      by simp [queryOutput, noQuery]⟩
  · right
    have firstQuery : FirstFrom input 63 query :=
      (ECMA2025.stringIndexOf_from_nat_iff input 63 8 query).mp foundQuery
    refine ⟨query, firstQuery, ?_⟩
    rcases ECMA2025.stringIndexOf_result input 35 8 with noHash | ⟨hash, foundHash⟩
    · left
      refine ⟨(ECMA2025.stringIndexOf_from_nat_missing_iff input 35 8).mp noHash, ?_⟩
      simp [queryOutput, foundQuery, noHash, ECMA2025.stringSlice_from_nat]
    · right
      have firstHash : FirstFrom input 35 hash :=
        (ECMA2025.stringIndexOf_from_nat_iff input 35 8 hash).mp foundHash
      refine ⟨hash, firstHash, ?_⟩
      by_cases ordered : query < hash
      · left
        exact ⟨ordered, by simp [queryOutput, foundQuery, foundHash,
          ordered, ECMA2025.stringSlice_from_nat_to_nat]⟩
      · right
        exact ⟨by omega, by simp [queryOutput, foundQuery, foundHash, ordered]⟩

theorem contract_output_unique {input left right : JSString}
    (leftContract : QueryStringsContract input left)
    (rightContract : QueryStringsContract input right) : left = right := by
  rcases leftContract with ⟨noQuery, output⟩ | ⟨query, firstQuery, branch⟩
  · rcases rightContract with ⟨_, other⟩ | ⟨otherQuery, otherFirst, _⟩
    · exact output.trans other.symm
    · exact False.elim (noQuery otherQuery otherFirst.1 otherFirst.2.1)
  · rcases rightContract with ⟨noQuery, _⟩ | ⟨otherQuery, otherFirst, otherBranch⟩
    · exact False.elim (noQuery query firstQuery.1 firstQuery.2.1)
    · have equalQuery : query = otherQuery :=
        ECMA2025.firstUnitAt_unique firstQuery otherFirst
      subst otherQuery
      rcases branch with ⟨noHash, output⟩ | ⟨hash, firstHash, output⟩
      · rcases otherBranch with ⟨_, other⟩ | ⟨otherHash, otherFirstHash, _⟩
        · exact output.trans other.symm
        · exact False.elim (noHash otherHash otherFirstHash.1 otherFirstHash.2.1)
      · rcases otherBranch with ⟨noHash, _⟩ | ⟨otherHash, otherFirstHash, otherOutput⟩
        · exact False.elim (noHash hash firstHash.1 firstHash.2.1)
        · have equalHash : hash = otherHash :=
            ECMA2025.firstUnitAt_unique firstHash otherFirstHash
          subst otherHash
          rcases output with ⟨ordered, same⟩ | ⟨ordered, same⟩ <;>
            rcases otherOutput with ⟨otherOrdered, otherSame⟩ | ⟨otherOrdered, otherSame⟩
          · exact same.trans otherSame.symm
          · omega
          · omega
          · exact same.trans otherSame.symm

theorem contract_iff (input output : JSString) :
    QueryStringsContract input output ↔ output = queryOutput input := by
  constructor
  · intro contract
    exact contract_output_unique contract (queryOutput_satisfies input)
  · intro equal
    rw [equal]
    exact queryOutput_satisfies input

/-- Exact embedded source execution iff the independent marker/range contract,
for every mathematical UTF-16 input. Native interpretation additionally needs
LegalString, standard method lookup and exact safe-integer interpretation.
The theorem does not establish full ECMAScript or native-engine adequacy. -/
theorem parsed_source_correct (input output : JSString) :
    (parseString pinnedSource).map (fun program => runString program input) =
      some (.ok output) ↔ QueryStringsContract input output := by
  rw [parses_pinned_source, Option.map_some, run_queryStrings, contract_iff]
  simp only [Option.some.injEq, Except.ok.injEq]
  exact eq_comm

/-- info: 'HonoLean.Upstream.GetQueryStrings.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.GetQueryStrings
