import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.NodeKeySet

open SourceSubset ECMA2025

/-- Independent single-event state change: keep an existing string's position,
or append a previously absent string. It does not invoke the primitive model. -/
def AddDelta (before : List JSString) (key : JSString) (after : List JSString) : Prop :=
  (key ∈ before ∧ after = before) ∨ (key ∉ before ∧ after = before ++ [key])

def createState (before : State) : State :=
  {before with
    environment := ("possibleKeys", .set before.sets.length) :: withoutBindings before.environment ["possibleKeys"]
    sets := before.sets ++ [[]]}

/-- Freshness is relative to allocated Set cells, not arbitrary dangling model
references. The declaration enters its own const scope and binds the fresh ID. -/
def CreateContract (before after : State) : Prop :=
  after = createState before ∧ before.sets[before.sets.length]? = none

def AddContract (before : State) (reference : Nat) (entries : List JSString) (key : JSString)
    (returned : Value) (after : State) : Prop :=
  returned = .set reference ∧ ∃ changed, AddDelta entries key changed ∧
    after = {before with sets := before.sets.set reference changed}

/-- A fresh dense array observes the current ordered entries. It is a snapshot;
no Set reference or mutable iterator is stored in the array. Native iterable
hooks, concurrent iteration mutation and Array-index/resource limits remain
separate interpretation restrictions. -/
def SnapshotContract (before : State) (entries : List JSString) (returned : Value) (after : State) : Prop :=
  returned = .array before.heap.length ∧
    after = {before with heap := before.heap ++ [entries.map Value.string]}

/-- Public supplied-trace contract uses indexed first-occurrence witnesses and
membership coverage, not equality to a fold/add/deduplication implementation. -/
def TraceContract (events : List JSString) (reference : Nat) (after : State) : Prop :=
  ∃ keys, after.sets[reference]? = some keys ∧ StringSet.OrderedFirstOccurrences events keys

end HonoLean.Upstream.NodeKeySet
