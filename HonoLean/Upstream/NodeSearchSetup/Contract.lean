import HonoLean.Upstream.NodeSearchSetup.Program

namespace HonoLean.Upstream.NodeSearchSetup

open SourceSubset ECMA2025

/-- Imported function identity, captured source closure, class DATA kind and
actual search arguments. The supplied method table is the latest known table;
external definitions outside that table are an explicit linking boundary. -/
structure Inputs (before : State) (methodTable : PrivateMethodTable) (functionTable : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString) : Prop where
  thisValue : before.thisValue = .object owner
  pathBinding : before.environment.lookup "path" = some (.string path)
  emptyBinding : before.environment.lookup "emptyParams" = some (.object emptyParams)
  writable : NodePrivateWrite.Writable before owner identity old
  calleeBinding : before.environment.lookup "splitPath" = some (.function handle)
  sourceProgram : closure.program = splitPathProgram
  ordinaryBeforeMethods : before.functions.length ≤ methodTable.base
  methodsBeforeFunctions : methodTable.base + methodTable.entries.length ≤ functionTable.base
  handleBound : functionTable.base ≤ handle
  closureFound : functionTable.entries[handle - functionTable.base]? = some closure

def resultEnvironment (before : State) (owner : Nat) (parts : List JSString) : List (String × Value) :=
  [("partOffsets", .null), ("len", .number parts.length),
   ("curNodesQueue", .array (before.heap.length + 3)), ("parts", .array (before.heap.length + 2)),
   ("curNodes", .array (before.heap.length + 1)), ("curNode", .object owner),
   ("handlerSets", .array before.heap.length)] ++ before.environment

def resultState (before : State) (owner identity emptyParams : Nat) (parts : List JSString) : State :=
  {writePrivateDataState before owner identity (.object emptyParams) with
    environment := resultEnvironment before owner parts
    heap := before.heap ++ [[], [.object owner], parts.map Value.string, []]}

/-- Independent source-startup observations. Output parts satisfy the
delimiter-partition contract; all four references/fresh cells, the DATA reset,
other raw tags, old arrays and non-array state frames are stated separately.
Neither a completed startup nor function-call evaluator defines this relation. -/
structure StartupContract (before after : State) (owner identity emptyParams : Nat)
    (old : Value) (path : JSString) (parts : List JSString) : Prop where
  split : SplitPathContract defaultSplitLimit path parts
  environment : after.environment = resultEnvironment before owner parts
  heap : after.heap = before.heap ++ [[], [.object owner], parts.map Value.string, []]
  collectorFresh : before.heap[before.heap.length]? = none
  nodesFresh : before.heap[before.heap.length + 1]? = none
  partsFresh : before.heap[before.heap.length + 2]? = none
  pendingFresh : before.heap[before.heap.length + 3]? = none
  collectorEmpty : after.heap[before.heap.length]? = some []
  singletonNodes : after.heap[before.heap.length + 1]? = some [.object owner]
  partsFound : after.heap[before.heap.length + 2]? = some (parts.map Value.string)
  pendingEmpty : after.heap[before.heap.length + 3]? = some []
  allocationCount : after.heap.length = before.heap.length + 4
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  privateReset : privateGet (.object owner) "params" after = .ok (.object emptyParams)
  privateChange : NodePrivateWrite.PrivateReplacement owner identity old (.object emptyParams)
    before.privates.elements after.privates.elements
  names : after.privates.names = before.privates.names
  objects : after.objects = before.objects
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

end HonoLean.Upstream.NodeSearchSetup
