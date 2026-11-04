import HonoLean.Upstream.MethodsLoop.Generated
import HonoLean.Upstream.MethodsLoopSupport

namespace HonoLean.Upstream.MethodsLoop

open SourceSubset ECMA2025

def methodsExpression : Expr := .privateProperty (.variable "node") "methods"
def initializers : List (String × Expr) :=
  [("i", .number 0), ("len", .property methodsExpression NodeParamLoop.lengthKey)]
def condition : Expr := .compare .less (.variable "i") (.variable "len")
def body : List Stmt := SearchEntry.rowProgram ++ SearchEntry.selectionProgram ++
  [.branch (.variable "handlerSet") NodeParamLoop.program]
def program : List Stmt := [.countedFor initializers condition "i" body]
def bindings : List String :=
  ["node", "method", "METHOD_NAME_ALL", "handlerSets", "params", "nodeParams", "createNullObject", "Object"]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem parses_source : parseBlock pinnedSource bindings ["methods"] = some program := by cbv

def header (outer : List (String × Value)) (index length : Nat) : List (String × Value) :=
  NodeParamLoop.headerEnvironment outer index length

def bodyEntry (before : State) : State :=
  {before with environment := withoutBindings before.environment ["m", "handlerSet"]}

def rowState (before : State) (row : ObjectRef) : State :=
  {bodyEntry before with environment := ("m", .object row) :: (bodyEntry before).environment}

def selectedState (before : State) (row : ObjectRef) (chosen : Value) : State :=
  {rowState before row with environment := ("handlerSet", chosen) :: (rowState before row).environment}

def nextState (outer : List (String × Value)) (index length : Nat) (after : State) : State :=
  {after with environment := header outer (index + 1) length}

/-- Independent state/selection trace. Row ordering is supplied by indexed reads
of the original methods list. A falsy operand contributes no handler and changes
no heap. A truthy operand must be an admitted record, and its capture endpoint is
the independent reset/append/Captures contract, never a source execution premise.
Repeated record references are retained, so previous aliases see later resets. -/
inductive Processed (origin : State) (rows : List Value) (method : JSString)
    (collector : Nat) : Nat → State → List ObjectRef → Prop where
  | start : Processed origin rows method collector 0
      {origin with environment := header origin.environment 0 rows.length} []
  | skip {count : Nat} {before : State} {selected : List ObjectRef} {row : ObjectRef} {chosen : Value}
      (prior : Processed origin rows method collector count before selected)
      (atRow : rows[count]? = some (.object row))
      (choice : SearchEntry.Choice before row method chosen)
      (falsy : ¬ NodeParamAssignment.Truthy chosen) :
      Processed origin rows method collector (count + 1)
        (nextState origin.environment count rows.length before) selected
  | capture {count : Nat} {before after : State} {selected : List ObjectRef} {row handlerRef : ObjectRef}
      {handler : OrdinaryObject} {keysArray : Nat} {priorHandlers : List Value}
      {parameterReceiver : Value} {nodeParams : Nat} {snapshot : NodeParamLoop.Snapshot}
      (prior : Processed origin rows method collector count before selected)
      (atRow : rows[count]? = some (.object row))
      (choice : SearchEntry.Choice before row method (.object handlerRef))
      (entry : NodeParamLoop.Entry (selectedState before row (.object handlerRef)) handlerRef handler
        collector keysArray priorHandlers parameterReceiver nodeParams snapshot)
      (contract : NodeParamLoop.BlockContract (selectedState before row (.object handlerRef)) after
        handlerRef handler collector priorHandlers snapshot) :
      Processed origin rows method collector (count + 1)
        (nextState origin.environment count rows.length after) (selected ++ [handlerRef])

/-- Normal-read/capture admissibility at a mathematically described prefix.
This predicate contains only current reads and structural Entry facts. It does
not supply a successful body/loop execution, completed trace, or desired result.
Snapshots are bounded to choose one sufficient budget for all nested key loops. -/
def Ready (before : State) (row : ObjectRef) (method : JSString) (collector keyBound : Nat) : Prop :=
  SearchEntry.ChoiceDomain before row method ∧
  ∀ chosen, SearchEntry.Choice before row method chosen → NodeParamAssignment.Truthy chosen →
    ∃ handlerRef handler keysArray priorHandlers parameterReceiver nodeParams snapshot,
      chosen = .object handlerRef ∧
      NodeParamLoop.Entry (selectedState before row chosen) handlerRef handler collector keysArray
        priorHandlers parameterReceiver nodeParams snapshot ∧ snapshot.keys.length ≤ keyBound

/-- Trajectory-wide prefix-closed normal domain. Every independent prefix starts
from the inhabited start constructor. This explicitly requires structural
read/capture readiness at each such prefix, rather than deriving it from one
initial-state check. It supplies no successful source execution or desired final
endpoint. Rows may alias handlers and later lookups may change after resets. -/
def NormalPrefixes (origin : State) (rows : List Value) (method : JSString)
    (collector keyBound : Nat) : Prop :=
  ∀ count before selected, Processed origin rows method collector count before selected →
    count < rows.length → ∃ row, rows[count]? = some (.object row) ∧ Ready before row method collector keyBound

structure Inputs (origin : State) (owner stamp methods collector : Nat) (rows : List Value)
    (method : JSString) : Prop where
  nodeBinding : origin.environment.lookup "node" = some (.object owner)
  methodBinding : origin.environment.lookup "method" = some (.string method)
  ownerFound : ∃ object, origin.objects[owner]? = some object
  privateName : origin.privates.names.lookup "methods" = some stamp
  privateSlot : ∃ fields, origin.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
  methodsFound : origin.heap[methods]? = some rows
  separate : collector ≠ methods
  legalLength : rows.length ≤ 4294967295

/-- The same selected references, in stored row order, with full independent
per-handler capture endpoints. The caller's lexical environment is restored.
This is local helper-body semantics, not a source proof of its call sites. -/
def LoopContract (origin after : State) (rows : List Value) (method : JSString) (collector : Nat) : Prop :=
  ∃ completed selected, Processed origin rows method collector rows.length completed selected ∧
    after = {completed with environment := origin.environment}

theorem processed_environment {origin : State} {rows : List Value} {method : JSString} {collector count : Nat}
    {before : State} {selected : List ObjectRef}
    (trace : Processed origin rows method collector count before selected) :
    before.environment = header origin.environment count rows.length := by
  cases trace <;> rfl

theorem processed_frames {origin : State} {rows : List Value} {method : JSString} {methods collector count : Nat}
    {before : State} {selected : List ObjectRef}
    (trace : Processed origin rows method collector count before selected)
    (separate : collector ≠ methods) :
    before.privates = origin.privates ∧
    before.heap[methods]? = origin.heap[methods]? ∧
    origin.objects.length ≤ before.objects.length := by
  induction trace with
  | start => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | skip prior _ _ _ ih => exact ih
  | @capture count before after selected row handlerRef handler keysArray priorHandlers parameterReceiver nodeParams snapshot prior atRow choice entry contract ih =>
    obtain ⟨output, complete, equal⟩ := contract
    rw [equal]
    refine ⟨ih.1, ?_, ?_⟩
    · simpa [nextState, selectedState, rowState, bodyEntry, NodeParamLoop.setupState,
        NodeParamLoop.resetState, List.getElem?_set_ne separate] using ih.2.1
    · simpa [nextState, selectedState, rowState, bodyEntry, NodeParamLoop.setupState,
        NodeParamLoop.resetState] using Nat.le_trans ih.2.2 (Nat.le_succ before.objects.length)

theorem processed_collector {origin : State} {rows : List Value} {method : JSString} {collector count : Nat}
    {before : State} {selected : List ObjectRef} {initial : List Value}
    (initialFound : origin.heap[collector]? = some initial)
    (trace : Processed origin rows method collector count before selected) :
    before.heap[collector]? = some (initial ++ selected.map Value.object) := by
  induction trace with
  | start => simpa using initialFound
  | skip prior _ _ _ ih => exact ih
  | @capture count before after selected row handlerRef handler keysArray priorHandlers parameterReceiver nodeParams snapshot prior atRow choice entry contract ih =>
    obtain ⟨output, complete, equal⟩ := contract
    have found : before.heap[collector]? = some priorHandlers := entry.handlersFound
    have priorEqual := Option.some.inj (found.symm.trans ih)
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
    rw [equal]
    simp [nextState, selectedState, rowState, bodyEntry, NodeParamLoop.setupState,
      NodeParamLoop.resetState, List.getElem?_set_self inside, priorEqual, List.map_append,
      List.append_assoc]

end HonoLean.Upstream.MethodsLoop
