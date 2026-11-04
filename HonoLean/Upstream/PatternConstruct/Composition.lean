import HonoLean.Upstream.PatternConstruct.Correctness

set_option autoImplicit false
namespace HonoLean.Upstream.PatternConstruct
open SourceSubset ECMA2025

/-- Load actual tuple2, then invoke the CLOSED STANDARD builtin operation.
This is intentionally not dynamic matcher.exec/source156 and does not invent
node138 destructuring, name/matcher lexical bindings or a current exec path. -/
def invokeProducedBuiltin (returned : Value) (input : JSString) (constructed : RegExpCallState) : Except RegExpCallError (Value × RegExpCallState) := do
  let matcher ← (readProperty returned (.number 2) constructed.ambient).mapError RegExpCallError.evaluation
  invokeRegExpExec matcher [.string input] constructed

theorem produced_tuple_regex_read (before after : RegExpCallState) (returned : Value) (label name : JSString)
    (prototype : Nat) (lower upper : UInt16) (contract : Contract before after returned label name prototype lower upper) :
    readProperty returned (.number 2) after.ambient = .ok (.object before.ambient.objects.length) := by
  rw [contract.tupleFresh]
  simp [readProperty, contract.tupleContents, tupleValues]

/-- Constructor output, not a supplied brand/compiled matcher, discharges the
builtin's actual receiver/lastIndex/code prerequisites. Every query outcome is
computed operationally and characterized by the independent range language. -/
theorem constructor_result_direct_builtin (before after : RegExpCallState) (returned : Value) (label name input : JSString)
    (prototype : Nat) (lower upper : UInt16) (contract : Contract before after returned label name prototype lower upper) :
    invokeProducedBuiltin returned input after =
      .ok (rangeExecValue lower upper after input, rangeExecState lower upper after input) := by
  have called := invokeRegExpExec_range after before.ambient.objects.length (constructedRangeRecord lower upper) (initializedRegExpObject prototype)
    input [] 0 true lower upper contract.internal contract.regexFound contract.lastIndex (by decide) rfl rfl
  simp only [invokeProducedBuiltin, produced_tuple_regex_read before after returned label name prototype lower upper contract, Except.mapError, bind, Except.bind]
  exact called

/-- Actual selected46B expression followed by direct standard builtin exec on
its produced tuple2. Initial inputs contain neither a branded record nor any
match outcome. Constructor/getPattern/cache/selected-branch/native adequacy and
actual138/current-exec property selection remain separate obligations. -/
theorem source_construct_then_direct_builtin_satisfies (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name input : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    let constructed := resultState before constructor.prototype lower upper label name
    sourceConstruct (extra + 16) context before = some (.ok (.array before.ambient.heap.length, constructed)) ∧
    Contract before constructed (.array before.ambient.heap.length) label name constructor.prototype lower upper ∧
    ConstructionPhases extra before context label name handle lower upper constructor.prototype ∧
    invokeProducedBuiltin (.array before.ambient.heap.length) input constructed =
      .ok (rangeExecValue lower upper constructed input, rangeExecState lower upper constructed input) := by
  dsimp only
  obtain ⟨run, contract, phases⟩ := source_construct_satisfies extra before context label name matched handle values lower upper constructor prototypeObject inputs
  exact ⟨run, contract, phases, constructor_result_direct_builtin before _ _ label name input constructor.prototype lower upper contract⟩

/-- info: 'HonoLean.Upstream.PatternConstruct.constructor_result_direct_builtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms constructor_result_direct_builtin
/-- info: 'HonoLean.Upstream.PatternConstruct.source_construct_then_direct_builtin_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_construct_then_direct_builtin_satisfies

end HonoLean.Upstream.PatternConstruct
