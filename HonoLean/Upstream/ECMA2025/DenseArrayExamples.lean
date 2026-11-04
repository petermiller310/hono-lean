import HonoLean.Upstream.ECMA2025.DenseArray

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

example : numericGet (ofList []) 0 = .undefined := by rfl
example : equalsEmpty .undefined = .ok false := by rfl
example : equalsEmpty (.string []) = .ok true := by rfl
example : equalsEmpty (.string [55296]) = .ok false := by rfl
/-- Number equality is deliberately not part of this comparison operation. -/
example : equalsEmpty (.number 0) = .error .unsupported := by rfl

example : (shiftSteps (ofList [])).1 = .undefined ∧
    observe (shiftSteps (ofList [])).2 = [] := by cbv

example : (shiftSteps (ofList [.string [97]])).1 = .string [97] ∧
    (shiftSteps (ofList [.string [97]])).2.length = 0 ∧
    (shiftSteps (ofList [.string [97]])).2.own 0 = none := by cbv

example : observe (shiftSteps (ofList [.string [], .string [97], .string []])).2 =
    [.string [97], .string []] := by cbv

private def aliasState : State :=
  {environment := [("paths", .array 0), ("alias", .array 0)],
   heap := [[.string [], .string [97]], [.string [98]]]}

/-- Both names still denote address zero, whose contents changed; the unrelated
cell at address one preserves its contents. Address values are not JS numbers. -/
example : (shiftAt 0 (liftState aliasState)).map (fun result =>
    (result.2.environment.lookup "paths", result.2.environment.lookup "alias",
     result.2.heap[0]?.map observe, result.2.heap[1]?.map observe)) =
      .ok (some (.array 0), some (.array 0),
        some [.string [97]], some [.string [98]]) := by cbv

example : (allocateFresh [.string []] (liftState aliasState)).1 = .array 2 ∧
    (allocateFresh [.string []] (liftState aliasState)).2.heap[2]?.map observe =
      some [.string []] := by cbv

private def copyBackward : Nat → (Nat → Option Value) → (Nat → Option Value)
  | 0, properties => properties
  | count + 1, properties =>
    copyBackward count (put properties count (properties (count + 1)))

private def wrongOrderShift (array : IndexedArray) : IndexedArray :=
  ⟨array.length - 1,
    put (copyBackward (array.length - 1) array.own) (array.length - 1) none⟩

/-- A real fault witness: reversing the copy order overwrites an unread source,
so [a,b,c] becomes [c,c] instead of [b,c]. The kernel checks both evaluations. -/
example : observe (wrongOrderShift (ofList [.string [97], .string [98], .string [99]])) =
    [.string [99], .string [99]] ∧
    observe (shiftSteps (ofList [.string [97], .string [98], .string [99]])).2 =
      [.string [98], .string [99]] := by cbv

/-- Copying alone leaves the old last own property. The explicit deletion in
the declared step contract removes it; observing only the length misses this. -/
example : copyForward 0 2 (ofList [.string [97], .string [98], .string [99]]).own 2 =
      some (.string [99]) ∧
    (shiftSteps (ofList [.string [97], .string [98], .string [99]])).2.own 2 = none := by cbv

end HonoLean.Upstream.ECMA2025
