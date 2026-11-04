import HonoLean.Upstream.NodeQueueSchedule.Generated
import HonoLean.Upstream.SourceSubset.SparseSequence

namespace HonoLean.Upstream.NodeQueueSchedule

open SourceSubset ECMA2025

set_option maxRecDepth 4096

def bindings : List String := ["curNodesQueue", "componentCount", "child"]
def initializer : SparseInitializer := .logicalOrAssign (.variable "curNodesQueue")
  (.variable "componentCount") (.arrayLiteral [])
def program : List SparseStmt :=
  [.declare "targetCurNodes" initializer,
   .evaluate (.call (.variable "targetCurNodes") "push" [.variable "child"])]

/-- Actual source177–178. This parser retains the logical assignment instead
of replacing it with an unconditional write or a copied source expression. -/
theorem parses_source : parseSparseSequence pinnedSource bindings = some program := by cbv

def sourceSchedule (fuel : Nat) (before : IndexedState) : Option (Except EvalError IndexedState) := do
  let parsed ← parseSparseSequence pinnedSource bindings
  pure (executeSparseSequence fuel [] parsed before)

end HonoLean.Upstream.NodeQueueSchedule
