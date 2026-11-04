import HonoLean.Upstream.NodeLoopEntry.Correctness
import HonoLean.Upstream.NodeLiteralBranch.Correctness
import HonoLean.Upstream.MethodsLoopInitial.Uncollected
import HonoLean.Upstream.NodeFirstLiteral.Source

namespace HonoLean.Upstream.NodeFirstLiteral

open SourceSubset ECMA2025 MethodsLoopInitial

def firstPart (path : JSString) : JSString := NodeIterationSetup.selectedPart (NodeSearchSetup.producedParts path) 0

def SourceBound : Prop :=
  pinnedFullSource = NodeSearchSetup.pinnedSource ++ "\n" ++ NodeLoopEntry.pinnedOuterSource ++
    NodeIterationSetup.pinnedIterationSource ++ "\n" ++ NodeLoopEntry.pinnedInnerSource ++ NodeIterationSetup.pinnedEntrySource

theorem source_bound : SourceBound := reassembles_source

/-- Before-startup private/public reads at the actual first produced part.
There is no supplied node/part/index/collector/queue binding. -/
structure Lookup (before : State) (owner children : Nat) (path : JSString) (next : Value) : Prop where
  childrenRead : privateGet (.object owner) "children" before = .ok (.object children)
  nextRead : getProperty propertyFuel before.objects children (firstPart path) = .ok next

/-- Method storage before the collector exists. The real methods-array cell
ties rows to the target; separation from fresh h is derived later. -/
structure Storage (before : State) (closure : PrivateMethodClosure) (target stamp : Nat) where
  methods : Nat
  rows : List Value
  targetFound : ∃ object, before.objects[target]? = some object
  privateName : closure.privateNames.lookup "methods" = some stamp
  privateSlot : ∃ fields, before.privates.slots.lookup target = some fields ∧ fields.lookup stamp = some (.array methods)
  methodsFound : before.heap[methods]? = some rows
  legalLength : rows.length ≤ 4294967295

def InstalledMethod (before : State) (owner stamp handle : Nat) : Prop :=
  ∃ fields, before.privates.elements.lookup owner = some fields ∧
    fields.lookup (stamp + 5) = some (.method (.function handle))

structure Child (before : State) (owner children target stamp : Nat) (path : JSString) (old : Value) : Prop where
  lookup : Lookup before owner children path (.object target)
  writable : NodePrivateWrite.Writable before target (stamp + 4) old

structure Direct (before : State) (methods : PrivateMethodTable) (closure : PrivateMethodClosure)
    (owner target stamp handle children keyBound emptyParams : Nat) (query : JSString)
    (wildcard : Value) (records : List Record) where
  callable : NodePrivateCall.Callable before methods closure owner handle
  installed : InstalledMethod before owner stamp handle
  storage : Storage before closure target stamp
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok wildcard
  wildcardFalsy : truthy wildcard = false
  reads : Uncollected before closure.environment storage.rows query keyBound records emptyParams

structure Wildcard (before : State) (methods : PrivateMethodTable) (closure : PrivateMethodClosure)
    (owner target wildcardTarget stamp handle children keyBound emptyParams : Nat) (query : JSString)
    (records : List Record) where
  callable : NodePrivateCall.Callable before methods closure owner handle
  installed : InstalledMethod before owner stamp handle
  direct : Storage before closure target stamp
  wildcard : Storage before closure wildcardTarget stamp
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok (.object wildcardTarget)
  reads : Uncollected before closure.environment (wildcard.rows ++ direct.rows) query keyBound records emptyParams

structure Result where
  entry : NodeLoopEntry.PrefixResult
  state : State

/-- Source-entry and independent literal contracts compose without assuming
a finished entry, any generated bindings, or future helper readiness. The
entire remaining inner body and traversal remain outside this endpoint. -/
inductive Contract (before : State) (closure : PrivateMethodClosure) (owner stamp emptyParams : Nat)
    (old : Value) (path query : JSString) : Result → Prop where
  | empty (entry : NodeLoopEntry.PrefixResult)
      (provenance : NodeLoopEntry.PrefixContract before owner (stamp + 4) emptyParams old path entry)
      (skipped : entry.nodeDeclared = false) :
      Contract before closure owner stamp emptyParams old path query ⟨entry, entry.state⟩
  | branch (entry : NodeLoopEntry.PrefixResult) (after : State) (next : Value)
      (provenance : NodeLoopEntry.PrefixContract before owner (stamp + 4) emptyParams old path entry)
      (entered : entry.nodeDeclared = true)
      (initialLookup : ∃ children, Lookup before owner children path next)
      (literal : NodeLiteralBranch.BranchContract entry.state closure next owner before.heap.length
        (before.heap.length + 4) stamp query emptyParams after) :
      Contract before closure owner stamp emptyParams old path query ⟨entry, after⟩

end HonoLean.Upstream.NodeFirstLiteral
