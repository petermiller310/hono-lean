import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.CreateNullObject.Generated

namespace HonoLean.Upstream.CreateNullObject

open SourceSubset

def createProgram : NoArgFunction :=
  ⟨"createNullObject", .call (.variable "Object") "create" [.null]⟩

set_option maxRecDepth 32768 in
/-- The entire pinned module, including its actual null argument, is parsed by
the shared zero-parameter expression parser, not recognized as one fixed token. -/
theorem parses_pinned_source : parseNoArg pinnedSource = some createProgram := by cbv

/-- A fresh allocated address, one appended empty-own object with null internal
prototype, and preservation of the existing heap and local environment.
This contract does not call the evaluator or the allocation primitive. Its
freshness is relative to allocated cells, not arbitrary dangling model values. -/
def NullObjectContract (before : State) (value : Value) (after : State) : Prop :=
  ∃ reference object,
    value = .object reference ∧ reference = before.objects.length ∧
    before.objects[reference]? = none ∧ after.objects = before.objects ++ [object] ∧
    object.own = [] ∧ object.prototype = none ∧ object.extensible = true ∧
    after.environment = before.environment ∧ after.heap = before.heap ∧
    after.functions = before.functions ∧ after.sets = before.sets ∧ after.privates = before.privates ∧
    after.thisValue = before.thisValue

theorem contract_iff (before : State) (value : Value) (after : State) :
    NullObjectContract before value after ↔
      value = .object before.objects.length ∧
      after = {before with objects := before.objects ++ [ECMA2025.emptyNullObject]} := by
  constructor
  · rintro ⟨reference, object, returned, address, fresh, appended, own, prototype,
      extensible, environment, arrays, functions, sets, privates, thisValue⟩
    have canonical : object = ECMA2025.emptyNullObject := by
      cases object
      simp_all [ECMA2025.emptyNullObject]
    refine ⟨returned.trans (congrArg Value.object address), ?_⟩
    cases before
    cases after
    simp_all
  · rintro ⟨returned, afterEqual⟩
    subst after
    exact ⟨before.objects.length, ECMA2025.emptyNullObject, returned, rfl,
      by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Explicit standard-builtin binding and dispatch are interpretation premises;
fresh ordinary-object allocation is proved within the declared object model.
The result retains both the abstract object identity and the whole state. -/
theorem run_createNullObject (state : State) (standard : StandardObjectBinding state)
    (limit : Nat) :
    runNoArg createProgram state limit =
      .ok (.object state.objects.length,
        {state with objects := state.objects ++ [ECMA2025.emptyNullObject]}) := by
  rcases standard with binding | binding <;>
    simp [runNoArg, createProgram, evalExpression, evalArguments, lookupVariable,
      binding, intrinsic, ECMA2025.createNull, bind, pure, Except.bind, Except.pure]

/-- Actual pinned source execution iff the independent fresh/null-prototype
contract. This is a theorem in the declared source/object model, not a proof
of mutable global lookup, a complete TypeScript frontend or a native engine. -/
theorem parsed_source_correct (before : State) (standard : StandardObjectBinding before)
    (value : Value) (after : State) :
    (parseNoArg pinnedSource).map (fun program => runNoArg program before) =
      some (.ok (value, after)) ↔ NullObjectContract before value after := by
  rw [parses_pinned_source, Option.map_some, run_createNullObject before standard, contract_iff]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨valueEqual, stateEqual⟩ => ⟨valueEqual.symm, stateEqual.symm⟩,
    fun ⟨valueEqual, stateEqual⟩ => ⟨valueEqual.symm, stateEqual.symm⟩⟩

theorem parsed_source_satisfies (before : State) (standard : StandardObjectBinding before) :
    ∃ value after,
      (parseNoArg pinnedSource).map (fun program => runNoArg program before) =
        some (.ok (value, after)) ∧ NullObjectContract before value after := by
  refine ⟨.object before.objects.length,
    {before with objects := before.objects ++ [ECMA2025.emptyNullObject]}, ?_, ?_⟩
  · simp [parses_pinned_source, run_createNullObject before standard]
  · exact (contract_iff _ _ _).mpr ⟨rfl, rfl⟩

/-- info: 'HonoLean.Upstream.CreateNullObject.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.CreateNullObject
