import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-! Normalized own-index specialization of ECMA-262 (2025) 23.1.3.2:
https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.concat
Array inputs are existing dense ordinary arrays, standard species/concat and
spreadability are fixed, and each index is an own data cell. Nonarray values
are copied as one element under default non-spreadability. No sparse holes,
getters, proxies, inherited indices, species effects or native resource/error
adequacy are modeled. Values are copied shallowly, including array/object aliases.
Native array interpretation additionally requires the resulting UInt32 length.
The specification allocates its standard result before reading item indices;
our final append endpoint is equivalent only under the stated effect-free own
reads/frozen species assumptions. In particular an ordinary object must not
override Symbol.isConcatSpreadable; a string argument is a single string value.
-/

/-- Independent indexed description of the two consecutive own-index copies. -/
structure DenseConcatContents (left right output : List Value) : Prop where
  length : output.length = left.length + right.length
  leftIndex : ∀ index, index < left.length → output[index]? = left[index]?
  rightIndex : ∀ index, index < right.length → output[left.length + index]? = right[index]?

theorem append_denseConcatContents (left right : List Value) : DenseConcatContents left right (left ++ right) := by
  refine ⟨List.length_append, ?_, ?_⟩
  · intro index inside
    exact List.getElem?_append_left inside
  · intro index _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- A fresh own dense result and exact old-cell/nonarray frames. This is not
a statement about general ArraySpeciesCreate or IsConcatSpreadable dispatch. -/
structure DenseConcatContract (before : State) (receiver argument : Nat)
    (returned : Value) (after : State) : Prop where
  inputs : ∃ left right output,
    before.heap[receiver]? = some left ∧ before.heap[argument]? = some right ∧
    returned = .array before.heap.length ∧ after.heap[before.heap.length]? = some output ∧
    DenseConcatContents left right output
  heapLength : after.heap.length = before.heap.length + 1
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  objects : after.objects = before.objects
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  privates : after.privates = before.privates

theorem intrinsic_concat (before : State) (receiver argument : Nat) (left right : List Value)
    (leftFound : before.heap[receiver]? = some left) (rightFound : before.heap[argument]? = some right)
    (limit : Nat) :
    intrinsic limit (.array receiver) "concat" [.array argument] before =
      .ok (.array before.heap.length, {before with heap := before.heap ++ [left ++ right]}) := by
  simp [intrinsic, leftFound, rightFound]

theorem intrinsic_concat_satisfies (before : State) (receiver argument : Nat) (left right : List Value)
    (leftFound : before.heap[receiver]? = some left) (rightFound : before.heap[argument]? = some right) :
    DenseConcatContract before receiver argument (.array before.heap.length)
      {before with heap := before.heap ++ [left ++ right]} := by
  refine ⟨⟨left, right, left ++ right, leftFound, rightFound, rfl, ?_, append_denseConcatContents left right⟩,
    ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp
  · simp
  · intro reference inside
    exact List.getElem?_append_left inside

theorem prepare_array_concat (before : State) (reference : Nat) (elements : List Value)
    (found : before.heap[reference]? = some elements) :
    prepareMethod (.array reference) "concat" before = .ok (.standard (.array reference) "concat") := by simp [found]

/-- Default IsConcatSpreadable normalization: dense arrays contribute their
own cells; every modeled nonarray argument contributes exactly one value. -/
def DenseConcatArgument (before : State) (argument : Value) (copied : List Value) : Prop :=
  match argument with
  | .array reference => before.heap[reference]? = some copied
  | _ => copied = [argument]

structure DenseConcatValueContract (before : State) (receiver : Nat) (argument returned : Value)
    (after : State) : Prop where
  inputs : ∃ left copied output,
    before.heap[receiver]? = some left ∧ DenseConcatArgument before argument copied ∧
    returned = .array before.heap.length ∧ after.heap[before.heap.length]? = some output ∧
    DenseConcatContents left copied output
  heapLength : after.heap.length = before.heap.length + 1
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  objects : after.objects = before.objects
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  privates : after.privates = before.privates

theorem intrinsic_concat_scalar (before : State) (receiver : Nat) (argument : Value) (left : List Value)
    (leftFound : before.heap[receiver]? = some left)
    (notArray : ∀ reference, argument ≠ .array reference) (limit : Nat) :
    intrinsic limit (.array receiver) "concat" [argument] before =
      .ok (.array before.heap.length, {before with heap := before.heap ++ [left ++ [argument]]}) := by
  cases argument <;> simp_all [intrinsic]

theorem intrinsic_concat_scalar_satisfies (before : State) (receiver : Nat) (argument : Value) (left : List Value)
    (leftFound : before.heap[receiver]? = some left)
    (notArray : ∀ reference, argument ≠ .array reference) :
    DenseConcatValueContract before receiver argument (.array before.heap.length)
      {before with heap := before.heap ++ [left ++ [argument]]} := by
  have copied : DenseConcatArgument before argument [argument] := by
    cases argument <;> simp_all [DenseConcatArgument]
  refine ⟨⟨left, [argument], left ++ [argument], leftFound, copied, rfl, ?_, append_denseConcatContents left [argument]⟩,
    ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp
  · simp
  · intro reference inside
    exact List.getElem?_append_left inside

end HonoLean.Upstream.ECMA2025
