import HonoLean.Upstream.NodeComponentCount.Generated
import HonoLean.Upstream.NodeQueueSchedule.Source
import HonoLean.Upstream.SourceSubset.RegExpSequence

namespace HonoLean.Upstream.NodeComponentCount

open SourceSubset ECMA2025

set_option maxRecDepth 4096

def bindings : List String := ["m"]
def fullBindings : List String := ["m", "curNodesQueue", "child"]
def initializer : RegExpExpr := .nullish
  (.optionalLength (.stringMatch (.index (.variable "m") (.number 0)) (.literal 47))) (.number 0)
def program : List RegExpStmt := [.declare "componentCount" initializer]
def fullProgram : List RegExpStmt := program ++ NodeQueueSchedule.program.map RegExpStmt.sparse

theorem reassembles_source : pinnedFullSource = pinnedSource ++ NodeQueueSchedule.pinnedSource := by cbv
theorem parses_source : parseRegExpSequence pinnedSource bindings = some program := by cbv
theorem parses_full_source : parseRegExpSequence pinnedFullSource fullBindings = some fullProgram := by cbv

def sourceCount (fuel : Nat) (before : RegExpState) : Option (Except EvalError RegExpState) := do
  let parsed ← parseRegExpSequence pinnedSource bindings
  pure (executeRegExpSequence fuel parsed before)
def sourceSchedule (fuel : Nat) (before : RegExpState) : Option (Except EvalError RegExpState) := do
  let parsed ← parseRegExpSequence pinnedFullSource fullBindings
  pure (executeRegExpSequence fuel parsed before)

end HonoLean.Upstream.NodeComponentCount
