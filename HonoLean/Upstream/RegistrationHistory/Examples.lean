import HonoLean.Upstream.RegistrationHistory.Correctness

namespace HonoLean.Upstream.RegistrationHistory.Examples

open SourceSubset ECMA2025

set_option maxRecDepth 32768

private def idKey : JSString := [105, 100]
private def nameKey : JSString := [110, 97, 109, 101]
private def get : JSString := [71, 69, 84]
private def all : JSString := [65, 76, 76]
private def post : JSString := [80, 79, 83, 84]
private def sharedHandler : Value := .string [104]
private def requests : List Request :=
  [⟨get, sharedHandler, [idKey, nameKey, idKey]⟩,
   ⟨all, sharedHandler, [nameKey]⟩,
   ⟨post, .number 0, []⟩]
private def base : State :=
  {environment := [("order", .number 7)]
   objects := [objectPrototypeProjection [], {prototype := some 0}]
   heap := [[]]
   privates := PrivateStore.ofData ([("methods", 9)]) ([(1, [(9, .array 0)])])}

private theorem seed : Seed base 1 9 0 7 [] :=
  ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨{prototype := some 0}, rfl⟩,
    rfl, ⟨[(9, .array 0)], rfl, rfl⟩, rfl⟩

/-- Nonempty source-history witness. Duplicate supplied events become one key
snapshot entry. Equal user handler values still receive distinct inner records. -/
theorem mixed_three_registration_history : ∃ after,
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source 1 requests base) = some (.ok after) ∧
    HistoryContract base after 0 7 [] requests :=
  parsed_history_satisfies base 1 9 0 7 [] requests seed

private def observe : Except EvalError (List Value × List (List Value) × List Value × Nat × Nat × Value) := do
  let after ← runSourceHistory NodeMethodsPush.expression 1 requests base
  let first ← (getProperty propertyFuel after.objects 3 HandlerRecord.scoreKey).mapError EvalError.objectError
  let second ← (getProperty propertyFuel after.objects 5 HandlerRecord.scoreKey).mapError EvalError.objectError
  let third ← (getProperty propertyFuel after.objects 7 HandlerRecord.scoreKey).mapError EvalError.objectError
  let order ← lookupVariable after "order"
  pure (after.heap[0]?.getD [], (after.heap.drop 1), [first, second, third],
    after.objects.length, after.sets.length, order)

example : observe = .ok
    ([.object 2, .object 4, .object 6],
     [[.string idKey, .string nameKey], [.string nameKey], []],
     [.number 8, .number 9, .number 10], 8, 3, .number 10) := by cbv

example : (endState base 1 0 7 [] requests).objects[3]? ≠
    (endState base 1 0 7 [] requests).objects[5]? := by decide

example : NativeHistoryBounds base 7 [] requests := by
  simp [NativeHistoryBounds, HandlerRecord.NativeBounds, HandlerRecord.SafeOrder,
    requests, Request.keys, StringSet.fromTrace, StringSet.add, base,
    idKey, nameKey, get, all, post]

end HonoLean.Upstream.RegistrationHistory.Examples
