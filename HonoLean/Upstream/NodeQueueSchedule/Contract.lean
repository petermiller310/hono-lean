import HonoLean.Upstream.NodeQueueSchedule.Source

namespace HonoLean.Upstream.NodeQueueSchedule

open SourceSubset ECMA2025

/-- Initial source operands. Array indices end at 2^32−2; 2^32−1 is the
maximum length, and is not an admitted array-index property here. These
arrays model own writable data cells, clean indexed prototypes, writable
length and successful allocation; descriptors/exotics remain outside. -/
structure Inputs (before : IndexedState) (queue index : Nat) (queued : IndexedArray) (child : Value) : Prop where
  queueBinding : before.environment.lookup "curNodesQueue" = some (.array queue)
  countBinding : before.environment.lookup "componentCount" = some (.number index)
  childBinding : before.environment.lookup "child" = some child
  queueFound : before.heap[queue]? = some queued
  wellFormed : WellFormedIndexed queued
  legalLength : LegalArrayLength queued
  legalIndex : index < maximumArrayLength

/-- Independent own-property description of the addressed Set. Existing
indices other than index, including holes, retain their exact presence. -/
structure OwnWrite (before after : IndexedArray) (index : Nat) (value : Value) : Prop where
  length : after.length = max before.length (index + 1)
  selected : after.own index = some value
  other : ∀ key, key ≠ index → after.own key = before.own key

/-- The appended value is written at the target's CURRENT length. Old holes
stay holes; absent properties are not filled with own undefined values. -/
structure OwnAppend (before after : IndexedArray) (value : Value) : Prop where
  length : after.length = before.length + 1
  appended : after.own before.length = some value
  old : ∀ key, key < before.length → after.own key = before.own key
  wellFormed : WellFormedIndexed after

def reusedState (before : IndexedState) (target : Nat) (initial : IndexedArray) (child : Value) : IndexedState :=
  {before with
    environment := ("targetCurNodes", .array target) :: before.environment
    heap := before.heap.set target (pushOwn initial child)}

def createdState (before : IndexedState) (queue index : Nat) (queued : IndexedArray) (child : Value) : IndexedState :=
  {before with
    environment := ("targetCurNodes", .array before.heap.length) :: before.environment
    heap := before.heap.set queue (indexedSet queued index (.array before.heap.length)) ++ [pushOwn (ofList []) child]}

/-- The two source cases, without an evaluator or a future readiness premise.
The reused case never performs the addressed Set or allocates. The created
case allocates once, stores the selected reference, then appends child. -/
inductive Effect (before : IndexedState) (queue index : Nat) (queued : IndexedArray) (child : Value)
    (target : Nat) (after : IndexedState) : Prop
  | reused (initial output : IndexedArray)
      (selected : numericGet queued index = .array target)
      (found : before.heap[target]? = some initial)
      (append : OwnAppend initial output child)
      (environment : after.environment = ("targetCurNodes", .array target) :: before.environment)
      (heap : after.heap = before.heap.set target output) : Effect before queue index queued child target after
  | created (written output : IndexedArray)
      (falsy : truthy (numericGet queued index) = false)
      (fresh : target = before.heap.length)
      (write : OwnWrite queued written index (.array target))
      (append : OwnAppend (ofList []) output child)
      (environment : after.environment = ("targetCurNodes", .array target) :: before.environment)
      (heap : after.heap = before.heap.set queue written ++ [output]) : Effect before queue index queued child target after

/-- The indexed queue and selected target remain actual heap cells. The
selected queue property is own and points at the target after the push,
including when the target aliases the queue itself. Only those two old
cells may change. This is an array/environment projection; it does not
execute object/private-field methods or establish full loop reachability. -/
structure Contract (before : IndexedState) (queue index : Nat) (queued : IndexedArray) (child : Value)
    (after : IndexedState) : Prop where
  initialQueueBinding : before.environment.lookup "curNodesQueue" = some (.array queue)
  initialCountBinding : before.environment.lookup "componentCount" = some (.number index)
  initialChildBinding : before.environment.lookup "child" = some child
  initialQueue : before.heap[queue]? = some queued
  legalIndex : index < maximumArrayLength
  target : ∃ selected currentQueue currentTarget,
    Effect before queue index queued child selected after ∧
    after.heap[queue]? = some currentQueue ∧ after.heap[selected]? = some currentTarget ∧
    currentQueue.own index = some (.array selected) ∧
    WellFormedIndexed currentQueue ∧ LegalArrayLength currentQueue ∧
    WellFormedIndexed currentTarget ∧ LegalArrayLength currentTarget ∧
    (∀ reference, reference < before.heap.length → reference ≠ queue → reference ≠ selected →
      after.heap[reference]? = before.heap[reference]?)
  allocations : after.heap.length = before.heap.length +
    (if truthy (numericGet queued index) then 0 else 1)

end HonoLean.Upstream.NodeQueueSchedule
