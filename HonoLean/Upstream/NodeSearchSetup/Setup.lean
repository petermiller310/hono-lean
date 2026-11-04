import HonoLean.Upstream.NodeSearchSetup.Contract

namespace HonoLean.Upstream.NodeSearchSetup

open SourceSubset ECMA2025

def producedParts (path : JSString) : List JSString :=
  dropLeadingEmpty ((path.splitOn (47 : UInt16)).take defaultSplitLimit)

def collectedState (before : State) : State :=
  {before with
    environment := ("handlerSets", .array before.heap.length) :: before.environment
    heap := before.heap ++ [[]]}

def resetState (before : State) (owner identity emptyParams : Nat) : State :=
  writePrivateDataState (collectedState before) owner identity (.object emptyParams)

def aliasState (before : State) (owner identity emptyParams : Nat) : State :=
  {resetState before owner identity emptyParams with
    environment := ("curNode", .object owner) :: (resetState before owner identity emptyParams).environment}

def nodesState (before : State) (owner identity emptyParams : Nat) : State :=
  {aliasState before owner identity emptyParams with
    environment := ("curNodes", .array (before.heap.length + 1)) :: (aliasState before owner identity emptyParams).environment
    heap := before.heap ++ [[], [.object owner]]}

/-- The parts binding is assigned the returned fresh array identity. Its
contents will be related to the actual function body execution separately. -/
def partsState (before : State) (owner identity emptyParams : Nat) (parts : List JSString) : State :=
  {nodesState before owner identity emptyParams with
    environment := ("parts", .array (before.heap.length + 2)) :: (nodesState before owner identity emptyParams).environment
    heap := before.heap ++ [[], [.object owner], parts.map Value.string]}

def pendingState (before : State) (owner identity emptyParams : Nat) (parts : List JSString) : State :=
  {partsState before owner identity emptyParams parts with
    environment := ("curNodesQueue", .array (before.heap.length + 3)) :: (partsState before owner identity emptyParams parts).environment
    heap := before.heap ++ [[], [.object owner], parts.map Value.string, []]}

theorem execute_collector (extra limit : Nat) (before : State) :
    execute (extra + 32) limit SearchEntry.collectorProgram before = .ok (.normal (collectedState before)) := by
  simp [SearchEntry.collectorProgram, execute, evalExpression, evalLiteralElements, collectedState,
    bind, Except.bind, pure, Except.pure]

theorem execute_reset (extra limit : Nat) (before : State) (owner identity emptyParams : Nat) (old : Value)
    (writable : NodePrivateWrite.Writable before owner identity old)
    (thisValue : before.thisValue = .object owner)
    (binding : before.environment.lookup "emptyParams" = some (.object emptyParams)) :
    execute (extra + 32) limit [.assign NodePrivateWrite.reset] (collectedState before) =
      .ok (.normal (resetState before owner identity emptyParams)) := by
  have writable : NodePrivateWrite.Writable (collectedState before) owner identity old :=
    ⟨writable.scope, writable.allocated, writable.data⟩
  have setter := NodePrivateWrite.setter (collectedState before) owner identity old (.object emptyParams) writable
  have currentThis : (collectedState before).thisValue = .object owner := thisValue
  have currentBinding : (collectedState before).environment.lookup "emptyParams" = some (.object emptyParams) := by
    simpa [collectedState, List.lookup] using binding
  simp [execute, executeAssignment, NodePrivateWrite.reset, evalAssignmentReference, evalExpression, lookupVariable,
    currentThis, writable.scope, currentBinding, putAssignmentReference, setter, resetState,
    bind, Except.bind, pure, Except.pure]

theorem execute_alias (extra limit : Nat) (before : State) (owner identity emptyParams : Nat)
    (thisValue : before.thisValue = .object owner) :
    execute (extra + 32) limit [.typedDeclare "curNode" nodeType .this] (resetState before owner identity emptyParams) =
      .ok (.normal (aliasState before owner identity emptyParams)) := by
  simp [execute, evalExpression, aliasState, resetState, writePrivateDataState, collectedState, thisValue,
    bind, Except.bind, pure, Except.pure]

theorem execute_nodes (extra limit : Nat) (before : State) (owner identity emptyParams : Nat) :
    execute (extra + 32) limit [.mutableDeclare "curNodes" none (.arrayLiteral [(false, .variable "curNode")])]
      (aliasState before owner identity emptyParams) = .ok (.normal (nodesState before owner identity emptyParams)) := by
  simp [execute, evalExpression, evalLiteralElements, appendLiteralElements, lookupVariable,
    aliasState, resetState, writePrivateDataState, collectedState, nodesState,
    bind, Except.bind, pure, Except.pure, List.append_assoc]

theorem execute_pending (extra limit : Nat) (before : State) (owner identity emptyParams : Nat) (parts : List JSString) :
    execute (extra + 32) limit [.typedDeclare "curNodesQueue" (.array (.array nodeType)) (.arrayLiteral [])]
      (partsState before owner identity emptyParams parts) = .ok (.normal (pendingState before owner identity emptyParams parts)) := by
  simp [execute, evalExpression, evalLiteralElements, partsState, pendingState,
    bind, Except.bind, pure, Except.pure, List.append_assoc]

theorem execute_saved_length (extra limit : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (partsRef : Nat) (parts : List JSString)
    (binding : before.environment.lookup "parts" = some (.array partsRef))
    (found : before.heap[partsRef]? = some (parts.map Value.string)) :
    executeFunctionStatements (extra + 34) limit methods functions NodeIterationSetup.lengthProgram before =
      .ok (.normal (NodeIterationSetup.lengthState before parts)) := by
  simp [NodeIterationSetup.lengthProgram, executeFunctionStatements, execute, evalExpression, lookupVariable,
    binding, readProperty, found, NodeParamLoop.lengthKey, NodeIterationSetup.lengthState,
    bind, Except.bind, pure, Except.pure]

theorem execute_parts (before : State) (methods : PrivateMethodTable) (functions : FunctionTable)
    (closure : StringFunctionClosure) (owner identity handle emptyParams : Nat) (old : Value) (path : JSString)
    (inputs : Inputs before methods functions closure owner identity handle emptyParams old path) :
    executeFunctionDeclaration 95 defaultSplitLimit methods functions splitDeclaration (nodesState before owner identity emptyParams) =
      .ok (partsState before owner identity emptyParams (producedParts path)) := by
  let current := nodesState before owner identity emptyParams
  have calleeBinding : current.environment.lookup "splitPath" = some (.function handle) := by
    simpa [current, nodesState, aliasState, resetState, writePrivateDataState, collectedState, List.lookup] using inputs.calleeBinding
  have pathBinding : current.environment.lookup "path" = some (.string path) := by
    simpa [current, nodesState, aliasState, resetState, writePrivateDataState, collectedState, List.lookup] using inputs.pathBinding
  have callee : evalExpression 95 defaultSplitLimit (.variable "splitPath") current = .ok (.function handle, current) := by
    simp [evalExpression, lookupVariable, calleeBinding, bind, Except.bind, pure, Except.pure]
  have arguments : evalArguments 95 defaultSplitLimit [.variable "path"] current = .ok ([.string path], current) := by
    simp [evalArguments, evalExpression, lookupVariable, pathBinding, bind, Except.bind, pure, Except.pure]
  have ordinaryBound : current.functions.length ≤ functions.base := by
    change before.functions.length ≤ functions.base
    have first := inputs.ordinaryBeforeMethods
    have second := inputs.methodsBeforeFunctions
    omega
  have separated : functionTableSeparated methods functions current = true := by
    simp [functionTableSeparated, ordinaryBound, inputs.methodsBeforeFunctions]
  have called : runFunctionCall 95 defaultSplitLimit methods functions (.variable "splitPath") [.variable "path"] current =
      .ok (.array current.heap.length, splitPathCallState current path defaultSplitLimit) := by
    simp only [runFunctionCall, bareFunctionCallee, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [callee]
    simp only [bind, Except.bind]
    rw [arguments]
    dsimp only
    rw [separated]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, resolveStringFunction,
      show ¬ handle < functions.base from Nat.not_lt_of_ge inputs.handleBound]
    rw [inputs.closureFound]
    dsimp only
    exact invoke_splitPath 63 defaultSplitLimit closure current path [] inputs.sourceProgram
  simp only [splitDeclaration, executeFunctionDeclaration, pure, Except.pure, bind, Except.bind]
  rw [called]
  simp [splitPathCallState, producedParts, partsState, current, nodesState,
    List.append_assoc]

theorem produced_parts_contract (path : JSString) : SplitPathContract defaultSplitLimit path (producedParts path) :=
  (contract_iff defaultSplitLimit path (producedParts path)).mpr rfl

theorem result_contract (before : State) (owner identity emptyParams : Nat) (old : Value) (path : JSString)
    (writable : NodePrivateWrite.Writable before owner identity old) :
    StartupContract before (resultState before owner identity emptyParams (producedParts path)) owner identity emptyParams old path
      (producedParts path) := by
  have replacement := (NodePrivateWrite.write_contract before owner identity old (.object emptyParams) writable).privateChange
  obtain ⟨object, allocated⟩ := writable.allocated
  obtain ⟨raw, brand, field⟩ := writable.data
  have reset := privateGet_write_same before owner identity "params" (.object emptyParams) old object raw
    writable.scope allocated brand field
  refine {
    split := produced_parts_contract path
    environment := rfl
    heap := rfl
    collectorFresh := by simp
    nodesFresh := by simp
    partsFresh := by simp
    pendingFresh := by simp
    collectorEmpty := by simp [resultState]
    singletonNodes := by simp [resultState]
    partsFound := by simp [resultState]
    pendingEmpty := by simp [resultState]
    allocationCount := by simp [resultState]
    oldArrays := ?_
    privateReset := reset
    privateChange := replacement
    names := rfl
    objects := rfl
    functions := rfl
    sets := rfl
    thisValue := rfl }
  intro reference inside
  exact List.getElem?_append_left inside

theorem length_pending_eq (before : State) (owner identity emptyParams : Nat) (parts : List JSString) :
    NodeIterationSetup.lengthState (pendingState before owner identity emptyParams parts) parts =
      resultState before owner identity emptyParams parts := by
  rfl

theorem parts_length_bound (path : JSString) (parts : List JSString)
    (split : SplitPathContract defaultSplitLimit path parts) : parts.length ≤ 4294967295 := by
  have dropBound : ∀ fields : List JSString, (dropLeadingEmpty fields).length ≤ fields.length := by
    intro fields
    cases fields with
    | nil => simp [dropLeadingEmpty]
    | cons first rest => cases first <;> simp [dropLeadingEmpty]
  rw [contract_iff] at split
  rw [split]
  have bounded : ((path.splitOn (47 : UInt16)).take defaultSplitLimit).length ≤ defaultSplitLimit := by
    simp only [List.length_take]
    exact Nat.min_le_left _ _
  exact Nat.le_trans (dropBound _) bounded

/-- Generated arrays and locals come only from the startup contract. The
singleton current-node array yields j=0; no caller-supplied parts/node binding
or successful future setup is used as an admission premise. -/
theorem derived_iteration_inputs (before after : State) (owner identity emptyParams : Nat)
    (old : Value) (path : JSString) (parts : List JSString) (i : Nat)
    (startup : StartupContract before after owner identity emptyParams old path parts)
    (inside : i < parts.length) :
    NodeIterationSetup.Inputs after (before.heap.length + 2) (before.heap.length + 1) parts [owner] i 0 := by
  refine ⟨?_, ?_, startup.partsFound, startup.singletonNodes, inside, by simp,
    parts_length_bound path parts startup.split, by simp⟩
  · simp [startup.environment, resultEnvironment, List.lookup]
  · simp [startup.environment, resultEnvironment, List.lookup]

end HonoLean.Upstream.NodeSearchSetup
