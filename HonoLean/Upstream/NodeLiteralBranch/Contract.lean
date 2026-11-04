import HonoLean.Upstream.NodeLiteralBranch.Program
import HonoLean.Upstream.NodeLiteralBranch.Layout
import HonoLean.Upstream.NodePrivateWrite.Flow

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025

def declaredState (before : State) (next : Value) : State :=
  {before with environment := ("nextNode", next) :: before.environment}

def enqueuedState (before : State) (temp : Nat) (prior : List Value) (next : Value) : State :=
  {before with heap := before.heap.set temp (prior ++ [next])}

/-- The actual declaration's initial reads. The surrounding loop supplies
node/part/isLast; no reachability of those bindings is asserted here. -/
structure Lookup (before : State) (parent children : Nat) (part : JSString) (next : Value) : Prop where
  parentBinding : before.environment.lookup "node" = some (.object parent)
  partBinding : before.environment.lookup "part" = some (.string part)
  childrenRead : privateGet (.object parent) "children" before = .ok (.object children)
  nextRead : getProperty propertyFuel before.objects children part = .ok next

/-- Heap and binding information for a source helper target, before any helper
has run. Methods arrays may coincide; mutable handler records may repeat. -/
structure Target (before : State) (closure : PrivateMethodClosure) (target stamp collector : Nat) where
  methods : Nat
  rows : List Value
  storage : NodePrivateCall.Storage before closure target stamp methods collector rows

/-- Shared initial facts for a truthy object child. DATA kind and lexical
identity are supplied as class-installation facts; no stored-value heuristic
or expected endpoint can establish writability. -/
structure ChildEntry (before : State) (parent children target receiver stamp collector temp nodeParams : Nat)
    (part query : JSString) (last old : Value) : Prop where
  lookup : Lookup before parent children part (.object target)
  scope : before.privates.names = NodeClass.names stamp
  writable : NodePrivateWrite.Writable before target (stamp + 4) old
  parentRead : privateGet (.object parent) "params" before = .ok (.object nodeParams)
  lastBinding : before.environment.lookup "isLast" = some last
  thisValue : before.thisValue = .object receiver
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  methodBinding : before.environment.lookup "method" = some (.string query)
  tempBinding : before.environment.lookup "tempNodes" = some (.array temp)

structure DirectEntry (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target receiver stamp handle collector temp children keyBound nodeParams : Nat)
    (query : JSString) (wildcard : Value) (records : List MethodsLoopInitial.Record) (initial : List Value) where
  callable : NodePrivateCall.Callable before table closure receiver handle
  direct : Target before closure target stamp collector
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok wildcard
  wildcardFalsy : truthy wildcard = false
  tempSeparate : temp ≠ collector
  layout : MethodsLoopInitial.Layout
    (NodePrivateCall.bodyState before closure (.object receiver) collector target query nodeParams .undefined)
    direct.rows query collector keyBound records .undefined nodeParams initial

structure WildcardEntry (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target wildcardTarget receiver stamp handle collector temp children keyBound nodeParams : Nat)
    (query : JSString) (records : List MethodsLoopInitial.Record) (initial : List Value) where
  callable : NodePrivateCall.Callable before table closure receiver handle
  direct : Target before closure target stamp collector
  wildcard : Target before closure wildcardTarget stamp collector
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok (.object wildcardTarget)
  tempSeparate : temp ≠ collector
  layout : MethodsLoopInitial.Layout
    (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
    (wildcard.rows ++ direct.rows) query collector keyBound records .undefined nodeParams initial

/-- Sequential source-level result relation. It mentions independent write,
capture-loop, and append contracts; it contains no evaluator invocation. Each
helper contract starts in the preceding helper's actual resulting state. -/
inductive BranchContract (before : State) (closure : PrivateMethodClosure)
    (next : Value) (receiver collector temp stamp : Nat) (query : JSString)
    (nodeParams : Nat) : State → Prop where
  | missing (falsy : truthy next = false) :
      BranchContract before closure next receiver collector temp stamp query nodeParams (declaredState before next)
  | nonlast (target : Nat) (equal : next = .object target) (last : Value)
      (lastBinding : before.environment.lookup "isLast" = some last) (falsy : truthy last = false)
      (old : Value) (written : State)
      (write : NodePrivateWrite.WriteContract (declaredState before next) written target (stamp + 4) old (.object nodeParams) (.object nodeParams))
      (prior : List Value) (tempFound : written.heap[temp]? = some prior)
      (capacity : prior.length + 1 ≤ 4294967295) :
      BranchContract before closure next receiver collector temp stamp query nodeParams
        (enqueuedState written temp prior next)
  | direct (target : Nat) (equal : next = .object target) (last : Value)
      (lastBinding : before.environment.lookup "isLast" = some last) (lastTruthy : truthy last = true)
      (old : Value) (written : State)
      (write : NodePrivateWrite.WriteContract (declaredState before next) written target (stamp + 4) old (.object nodeParams) (.object nodeParams))
      (children : Nat) (wildcard : Value)
      (childrenRead : privateGet (.object target) "children" written = .ok (.object children))
      (wildcardRead : getProperty propertyFuel written.objects children [42] = .ok wildcard)
      (wildcardFalsy : truthy wildcard = false)
      (methods : Nat) (rows : List Value)
      (storage : NodePrivateCall.Storage written closure target stamp methods collector rows)
      (after : State)
      (call : NodePrivateCall.CallContract written
        (NodePrivateCall.bodyState written closure (.object receiver) collector target query nodeParams .undefined)
        rows query collector .undefined after)
      (tempFrame : after.heap[temp]? = before.heap[temp]?) :
      BranchContract before closure next receiver collector temp stamp query nodeParams after
  | wildcard (target wildcardTarget : Nat) (equal : next = .object target) (last : Value)
      (lastBinding : before.environment.lookup "isLast" = some last) (lastTruthy : truthy last = true)
      (old : Value) (written : State)
      (write : NodePrivateWrite.WriteContract (declaredState before next) written target (stamp + 4) old (.object nodeParams) (.object nodeParams))
      (children : Nat)
      (childrenRead : privateGet (.object target) "children" written = .ok (.object children))
      (wildcardRead : getProperty propertyFuel written.objects children [42] = .ok (.object wildcardTarget))
      (wildcardMethods literalMethods : Nat) (wildcardRows literalRows : List Value) (middle after : State)
      (wildcardStorage : NodePrivateCall.Storage written closure wildcardTarget stamp wildcardMethods collector wildcardRows)
      (directStorage : NodePrivateCall.Storage middle closure target stamp literalMethods collector literalRows)
      (wildcardCall : NodePrivateCall.CallContract written
        (NodePrivateCall.bodyState written closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
        wildcardRows query collector .undefined middle)
      (directCall : NodePrivateCall.CallContract middle
        (NodePrivateCall.bodyState middle closure (.object receiver) collector target query nodeParams .undefined)
        literalRows query collector .undefined after)
      (tempFrame : after.heap[temp]? = before.heap[temp]?) :
      BranchContract before closure next receiver collector temp stamp query nodeParams after

end HonoLean.Upstream.NodeLiteralBranch
