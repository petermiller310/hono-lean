import HonoLean.Upstream.NodeCaptureGuard.Generated
import HonoLean.Upstream.SourceSubset.HasOwn
import HonoLean.Upstream.SourceSubset.Parser

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureGuard
open SourceSubset ECMA2025

def bindings : List String := ["params", "name", "m"]
def condition : Expr := .logicalNot (.call (.variable "Object") "hasOwn" [.variable "params", .variable "name"])
def assignment : Assignment := ⟨.index (.variable "params") (.variable "name"), .index (.variable "m") (.number 0)⟩
def program : List Stmt := [.branch condition [.assign assignment]]

theorem reassembles_source : pinnedSource = pinnedGuard ++ pinnedAssignment ++ pinnedClose := by cbv
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_source : parseBlock pinnedSource bindings = some program := by cbv

def sourceGuard (fuel : Nat) (before : State) : Option (Except EvalError Completion) :=
  (parseBlock pinnedSource bindings).map (fun source => execute fuel defaultSplitLimit source before)

end HonoLean.Upstream.NodeCaptureGuard
