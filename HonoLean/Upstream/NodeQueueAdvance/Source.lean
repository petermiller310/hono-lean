import HonoLean.Upstream.NodeQueueAdvance.Generated
import HonoLean.Upstream.SourceSubset.MutableSequence

namespace HonoLean.Upstream.NodeQueueAdvance

open SourceSubset

set_option maxRecDepth 4096

def bindings : List String := ["curNodesQueue", "curNodes", "tempNodes"]
def mutableBindings : List String := ["curNodes"]

def shiftedExpression : Expr := .call (.variable "curNodesQueue") "shift" []
def nextExpression : Expr := .conditional (.variable "shifted")
  (.call (.variable "tempNodes") "concat" [.variable "shifted"])
  (.variable "tempNodes")
def program : List Stmt :=
  [.declare "shifted" shiftedExpression, .assign ⟨.variable "curNodes", nextExpression⟩]

/-- Original source209–210, including the bare lexical rebind. -/
theorem parses_source : parseMutableSequence pinnedSource bindings mutableBindings = some program := by cbv

def sourceAdvance (fuel limit : Nat) (before : State) : Option (Except EvalError Completion) := do
  let parsed ← parseMutableSequence pinnedSource bindings mutableBindings
  pure (executeMutableSequence fuel limit mutableBindings parsed before)

end HonoLean.Upstream.NodeQueueAdvance
