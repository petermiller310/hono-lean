import HonoLean.Upstream.NodeChildEnumeration.Generated
import HonoLean.Upstream.NodeComponentCount.Composition
import HonoLean.Upstream.NodePrivateWrite.Correctness
import HonoLean.Upstream.SourceSubset.ForInSequence

namespace HonoLean.Upstream.NodeChildEnumeration

open SourceSubset ECMA2025

set_option maxRecDepth 32768

def bindings : List String := ["child", "params", "m", "curNodesQueue"]
def privateNames : List String := ["children", "params"]
def collection : Expr := .privateProperty (.variable "child") "children"
def body : List ForInStmt := [.privateWrite NodePrivateWrite.parameter] ++
  NodeComponentCount.fullProgram.map ForInStmt.regexp ++ [.breakLoop]
def program : List ForInStmt := [.forIn "_" collection body]

theorem reassembles_source : pinnedSource = pinnedPrefix ++ NodeComponentCount.pinnedFullSource ++ pinnedSuffix := by cbv
set_option maxHeartbeats 2000000 in
theorem parses_source : parseForInSequence pinnedSource bindings privateNames = some program := by cbv

def sourceLoop (fuel : Nat) (before : ForInState) : Option (Except EvalError ForInCompletion) := do
  let parsed ← parseForInSequence pinnedSource bindings privateNames
  pure (executeForInSequence fuel parsed before)

end HonoLean.Upstream.NodeChildEnumeration
