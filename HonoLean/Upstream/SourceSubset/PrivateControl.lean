import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.SourceSubset.PrivateCall

namespace HonoLean.Upstream.SourceSubset

mutual
/-- Lower execution retains root declarations, allowing later statements in
the containing native block to compose with the selected fragment. Each list
node consumes one syntax budget unit before its head and continuation. -/
def executePrivateControl : Nat → Nat → PrivateMethodTable → List PrivateControlStmt → State →
    Except EvalError Completion
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, [], state => .ok (.normal state)
  | fuel + 1, limit, table, head :: tail, state => do
    match ← executePrivateControlStmt fuel limit table head state with
    | .normal state => executePrivateControl fuel limit table tail state
    | .returned value state => pure (.returned value state)

/-- An explicit control node consumes another unit. Ordinary simple leaves use
execute unchanged; private-call leaves use the current State.thisValue, and an
if evaluates its condition once before selecting exactly one arm. Errors and
returns propagate without executing the sibling arm or continuation. -/
def executePrivateControlStmt : Nat → Nat → PrivateMethodTable → PrivateControlStmt → State →
    Except EvalError Completion
  | 0, _, _, _, _ => .error .exhausted
  | fuel + 1, limit, table, statement, state =>
    match statement with
    | .ordinary (.branch _ _) | .ordinary (.countedFor _ _ _ _) => .error .unsupported
    | .ordinary statement => execute fuel limit [statement] state
    | .privateCall call => do
      let (_, state) ← runPrivateMethodCall fuel limit table ⟨state.thisValue⟩ call state
      pure (.normal state)
    | .branch condition yes no => do
      let (value, state) ← evalExpression fuel limit condition state
      executePrivateControl fuel limit table (if truthy value then yes else no) state
end

/-- Standalone fragment observation restores caller bindings on normal/return,
while retaining all other modeled effects. This is an explicit projection:
the native root declaration's scope may extend beyond the selected source
window. Use executePrivateControl to retain it for subsequent composition.
Parsed programs have no nested declarations or direct lexical writes, so this
projection does not discard admitted assignments to outer lexical cells.
Except does not expose partial failure state or promise rollback. -/
def runPrivateControl (fuel limit : Nat) (table : PrivateMethodTable)
    (program : List PrivateControlStmt) (state : State) : Except EvalError Completion := do
  let outer := state.environment
  let state := {state with environment := withoutBindings outer (privateControlDeclaredNames program)}
  let completion ← executePrivateControl fuel limit table program state
  pure (restoreCompletion outer completion)

theorem executePrivateControl_nil (fuel limit : Nat) (table : PrivateMethodTable) (state : State) :
    executePrivateControl (fuel + 1) limit table [] state = .ok (.normal state) := rfl

theorem executePrivateControl_cons (fuel limit : Nat) (table : PrivateMethodTable)
    (head : PrivateControlStmt) (tail : List PrivateControlStmt) (state : State) :
    executePrivateControl (fuel + 1) limit table (head :: tail) state = (do
      match ← executePrivateControlStmt fuel limit table head state with
      | .normal state => executePrivateControl fuel limit table tail state
      | .returned value state => pure (.returned value state)) := rfl

theorem executePrivateControl_ordinary (fuel limit : Nat) (table : PrivateMethodTable)
    (statement : Stmt) (state : State)
    (simple : (match statement with | .branch _ _ | .countedFor _ _ _ _ => false | _ => true) = true) :
    executePrivateControlStmt (fuel + 1) limit table (.ordinary statement) state =
      execute fuel limit [statement] state := by
  cases statement <;> simp_all [executePrivateControlStmt]

theorem executePrivateControl_call (fuel limit : Nat) (table : PrivateMethodTable)
    (call : PrivateMethodCall) (state : State) :
    executePrivateControlStmt (fuel + 1) limit table (.privateCall call) state = (do
      let (_, state) ← runPrivateMethodCall fuel limit table ⟨state.thisValue⟩ call state
      pure (.normal state)) := rfl

theorem executePrivateControl_branch (fuel limit : Nat) (table : PrivateMethodTable)
    (condition : Expr) (yes no : List PrivateControlStmt) (state : State) :
    executePrivateControlStmt (fuel + 1) limit table (.branch condition yes no) state = (do
      let (value, state) ← evalExpression fuel limit condition state
      executePrivateControl fuel limit table (if truthy value then yes else no) state) := rfl

end HonoLean.Upstream.SourceSubset
