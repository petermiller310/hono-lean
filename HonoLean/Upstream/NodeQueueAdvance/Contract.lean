import HonoLean.Upstream.NodeQueueAdvance.Source

namespace HonoLean.Upstream.NodeQueueAdvance

open SourceSubset ECMA2025

/-- The initial first lexical reference. The previous curNodes value is
unrestricted, and same-name entries in back remain shadowed. -/
structure Inputs (before : State) (queue temp : Nat) (queued temporary : List Value)
    (front : List (String × Value)) (old : Value) (back : List (String × Value)) : Prop where
  queueBinding : before.environment.lookup "curNodesQueue" = some (.array queue)
  tempBinding : before.environment.lookup "tempNodes" = some (.array temp)
  queueFound : before.heap[queue]? = some queued
  tempFound : before.heap[temp]? = some temporary
  lexical : before.environment = front ++ ("curNodes", old) :: back
  first : front.lookup "curNodes" = none

/-- A shift changes this cell before the source reads temp or the shifted
array. In particular self-queue and temp=queue aliases see the tail. -/
def currentValues (queue reference : Nat) (queued initial : List Value) : List Value :=
  if reference = queue then queued.tail else initial

def shiftState (before : State) (queue : Nat) (queued : List Value) : State :=
  {before with heap := before.heap.set queue queued.tail}

def declaredState (before : State) (queue : Nat) (queued : List Value) : State :=
  {shiftState before queue queued with
    environment := ("shifted", queued.headD .undefined) :: before.environment}

def finish (before : State) (queue : Nat) (queued : List Value)
    (front : List (String × Value)) (value : Value) (heap : List (List Value)) : State :=
  writeMutableBinding {declaredState before queue queued with heap}
    (front.length + 1) "curNodes" value

def falsyState (before : State) (queue temp : Nat) (queued : List Value)
    (front : List (String × Value)) : State :=
  finish before queue queued front (.array temp) (shiftState before queue queued).heap

def copiedState (before : State) (queue : Nat) (queued copied : List Value)
    (front : List (String × Value)) : State :=
  finish before queue queued front (.array before.heap.length)
    ((shiftState before queue queued).heap ++ [copied])

/-- Independent source result: the false arm reuses temp; the true arm makes
a shallow, fresh result using the CURRENT cells after the shift. The array
case describes each copied index, not an evaluator equation. -/
inductive Contents (before : State) (queue temp : Nat) (queued temporary : List Value)
    (value : Value) (after : State) : Prop
  | falsy (test : truthy (queued.headD .undefined) = false)
      (returned : value = .array temp)
      (heap : after.heap = before.heap.set queue queued.tail) : Contents before queue temp queued temporary value after
  | array (argument : Nat) (initial output : List Value)
      (head : queued.headD .undefined = .array argument)
      (found : before.heap[argument]? = some initial)
      (returned : value = .array before.heap.length)
      (fresh : after.heap[before.heap.length]? = some output)
      (copy : DenseConcatContents (currentValues queue temp queued temporary)
        (currentValues queue argument queued initial) output)
      (heap : after.heap = before.heap.set queue queued.tail ++ [output]) : Contents before queue temp queued temporary value after
  | scalar (test : truthy (queued.headD .undefined) = true)
      (notArray : ∀ reference, queued.headD .undefined ≠ .array reference)
      (output : List Value)
      (returned : value = .array before.heap.length)
      (copy : DenseConcatContents (currentValues queue temp queued temporary) [queued.headD .undefined] output)
      (heap : after.heap = before.heap.set queue queued.tail ++ [output]) : Contents before queue temp queued temporary value after

/-- A relation on the observable source endpoint. Dense standard arrays and
standard concat/shift are the model; sparse producer queues and complete
search-loop reachability are not established by this contract. -/
structure Contract (before : State) (queue temp : Nat) (queued temporary : List Value) (after : State) : Prop where
  initialQueueBinding : before.environment.lookup "curNodesQueue" = some (.array queue)
  initialTempBinding : before.environment.lookup "tempNodes" = some (.array temp)
  initialQueue : before.heap[queue]? = some queued
  initialTemp : before.heap[temp]? = some temporary
  lexical : ∃ front old back value,
    before.environment = front ++ ("curNodes", old) :: back ∧ front.lookup "curNodes" = none ∧
    after.environment = ("shifted", queued.headD .undefined) :: (front ++ ("curNodes", value) :: back) ∧
    Contents before queue temp queued temporary value after
  shifted : after.environment.lookup "shifted" = some (queued.headD .undefined)
  queueTail : after.heap[queue]? = some queued.tail
  oldArrays : ∀ reference, reference < before.heap.length → reference ≠ queue →
    after.heap[reference]? = before.heap[reference]?
  objects : after.objects = before.objects
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  privates : after.privates = before.privates
  thisValue : after.thisValue = before.thisValue

end HonoLean.Upstream.NodeQueueAdvance
