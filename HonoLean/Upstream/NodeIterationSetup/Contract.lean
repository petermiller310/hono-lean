import HonoLean.Upstream.NodeIterationSetup.Program

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset ECMA2025

def selectedPart (parts : List JSString) (index : Nat) : JSString := parts[index]?.getD []
def selectedNode (nodes : List Nat) (index : Nat) : Nat := nodes[index]?.getD 0
def lastValue (parts : List JSString) (index : Nat) : Value := .boolean (decide (index + 1 = parts.length))

/-- Dense input arrays and admitted supplied loop indices. Actual source
declarations produce part/node/isLast/tempNodes; none is an input binding. -/
structure Inputs (before : State) (partsRef nodesRef : Nat) (parts : List JSString)
    (nodes : List Nat) (i j : Nat) : Prop where
  partsBinding : before.environment.lookup "parts" = some (.array partsRef)
  nodesBinding : before.environment.lookup "curNodes" = some (.array nodesRef)
  partsFound : before.heap[partsRef]? = some (parts.map Value.string)
  nodesFound : before.heap[nodesRef]? = some (nodes.map Value.object)
  outerInside : i < parts.length
  innerInside : j < nodes.length
  partsBound : parts.length ≤ 4294967295
  nodesBound : nodes.length ≤ 4294967295

def lengthState (before : State) (parts : List JSString) : State :=
  {before with environment := [("partOffsets", .null), ("len", .number parts.length)] ++ before.environment}

/-- Explicit supplied activation across omitted source loop header99. -/
def outerActivation (before : State) (i : Nat) : State :=
  {before with environment := ("i", .number i) :: before.environment}

def outerState (before : State) (parts : List JSString) (i : Nat) : State :=
  {before with
    environment := [("tempNodes", .array before.heap.length), ("isLast", lastValue parts i),
      ("part", .string (selectedPart parts i))] ++ before.environment
    heap := before.heap ++ [[]]}

/-- Explicit supplied activation across omitted source loop header104. -/
def innerActivation (before : State) (j : Nat) : State :=
  {before with environment := ("j", .number j) :: before.environment}

def nodeState (before : State) (nodes : List Nat) (j : Nat) : State :=
  {before with environment := ("node", .object (selectedNode nodes j)) :: before.environment}

def branchEntry (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) : State :=
  nodeState (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j) nodes j

/-- Independent saved-length/declaration endpoint and complete state frames. -/
structure LengthContract (before after : State) (parts : List JSString) : Prop where
  environment : after.environment = [("partOffsets", .null), ("len", .number parts.length)] ++ before.environment
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

/-- Fresh queue plus actual indexed part/last value. Native dense-array and
integer bounds are initial Inputs facts, separate from the model evaluator. -/
structure OuterContract (before after : State) (parts : List JSString) (i : Nat) : Prop where
  environment : after.environment = [("tempNodes", .array before.heap.length), ("isLast", lastValue parts i),
    ("part", .string (selectedPart parts i))] ++ before.environment
  heap : after.heap = before.heap ++ [[]]
  queueFresh : before.heap[before.heap.length]? = none
  queueEmpty : after.heap[before.heap.length]? = some []
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

structure NodeContract (before after : State) (nodes : List Nat) (j : Nat) : Prop where
  environment : after.environment = ("node", .object (selectedNode nodes j)) :: before.environment
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

/-- Initial heap reads at the actual mathematically selected indices. Unlike
the older branch entry, this supplies no node/part/last/queue bindings. -/
structure InitialLookup (before : State) (parts : List JSString) (nodes : List Nat)
    (i j children : Nat) (next : Value) : Prop where
  childrenRead : privateGet (.object (selectedNode nodes j)) "children" before = .ok (.object children)
  nextRead : getProperty propertyFuel before.objects children (selectedPart parts i) = .ok next

structure InitialChild (before : State) (parts : List JSString) (nodes : List Nat)
    (i j children target receiver stamp collector nodeParams : Nat) (query : JSString) (old : Value) : Prop where
  lookup : InitialLookup before parts nodes i j children (.object target)
  scope : before.privates.names = NodeClass.names stamp
  writable : NodePrivateWrite.Writable before target (stamp + 4) old
  parentRead : privateGet (.object (selectedNode nodes j)) "params" before = .ok (.object nodeParams)
  thisValue : before.thisValue = .object receiver
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  methodBinding : before.environment.lookup "method" = some (.string query)

structure InitialDirect (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target receiver stamp handle collector children keyBound nodeParams : Nat)
    (query : JSString) (wildcard : Value) (records : List MethodsLoopInitial.Record) (initial : List Value) where
  callable : NodePrivateCall.Callable before table closure receiver handle
  direct : NodeLiteralBranch.Target before closure target stamp collector
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok wildcard
  wildcardFalsy : truthy wildcard = false
  layout : MethodsLoopInitial.Layout
    (NodePrivateCall.bodyState before closure (.object receiver) collector target query nodeParams .undefined)
    direct.rows query collector keyBound records .undefined nodeParams initial

structure InitialWildcard (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (target wildcardTarget receiver stamp handle collector children keyBound nodeParams : Nat)
    (query : JSString) (records : List MethodsLoopInitial.Record) (initial : List Value) where
  callable : NodePrivateCall.Callable before table closure receiver handle
  direct : NodeLiteralBranch.Target before closure target stamp collector
  wildcard : NodeLiteralBranch.Target before closure wildcardTarget stamp collector
  childrenRead : privateGet (.object target) "children" before = .ok (.object children)
  wildcardRead : getProperty propertyFuel before.objects children [42] = .ok (.object wildcardTarget)
  layout : MethodsLoopInitial.Layout
    (NodePrivateCall.bodyState before closure (.object receiver) collector wildcardTarget query nodeParams .undefined)
    (wildcard.rows ++ direct.rows) query collector keyBound records .undefined nodeParams initial

/-- Provenance execution of the two distinct setup windows. The supplied
outer activation appears explicitly between them. -/
def SetupSource (before : State) (parts : List JSString) (i : Nat) : Prop :=
  (parseBlock pinnedSearchSource lengthBindings).map (fun source => execute 32 defaultSplitLimit source before) =
    some (.ok (.normal (lengthState before parts))) ∧
  (parseBlock pinnedIterationSource outerBindings).map
    (fun source => execute 32 defaultSplitLimit source (outerActivation (lengthState before parts) i)) =
    some (.ok (.normal (outerState (outerActivation (lengthState before parts) i) parts i)))

/-- Independent setup endpoints, including the node declaration at the head
of the third source window. No source evaluator defines this relation. -/
def SetupContract (before : State) (parts : List JSString) (nodes : List Nat) (i j : Nat) : Prop :=
  LengthContract before (lengthState before parts) parts ∧
  OuterContract (outerActivation (lengthState before parts) i)
    (outerState (outerActivation (lengthState before parts) i) parts i) parts i ∧
  NodeContract (innerActivation (outerState (outerActivation (lengthState before parts) i) parts i) j)
    (branchEntry before parts nodes i j) nodes j

end HonoLean.Upstream.NodeIterationSetup
