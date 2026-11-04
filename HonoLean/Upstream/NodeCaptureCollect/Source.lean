import HonoLean.Upstream.NodeCaptureCollect.Generated
import HonoLean.Upstream.NodeCaptureGuard.Source
import HonoLean.Upstream.SourceSubset.PrivateControl
import HonoLean.Upstream.NodePrivateCall.Correctness

set_option autoImplicit false
namespace HonoLean.Upstream.NodeCaptureCollect
open SourceSubset ECMA2025

def bindings : List String := ["handlerSets", "child", "method", "node", "params", "name", "m"]
def call : PrivateMethodCall := ⟨.this, "pushHandlerSets",
  [.variable "handlerSets", .variable "child", .variable "method",
   .privateProperty (.variable "node") "params", .variable "params"]⟩
def guardProgram : List PrivateControlStmt :=
  [.branch NodeCaptureGuard.condition [.ordinary (.assign NodeCaptureGuard.assignment)] []]
def program : List PrivateControlStmt := guardProgram ++ [.privateCall call]

theorem reassembles_source : pinnedSource = pinnedGuard ++ pinnedCall := by cbv
theorem guard_is_existing_source : pinnedGuard = NodeCaptureGuard.pinnedSource := by cbv
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_call : parsePrivateMethodCall pinnedCall bindings NodePrivateCall.classPrivateNames = some call := by cbv
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_source : parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames = some program := by cbv

def sourceCall (fuel : Nat) (table : PrivateMethodTable) (before : State) : Option (Except EvalError (Value × State)) :=
  (parsePrivateMethodCall pinnedCall bindings NodePrivateCall.classPrivateNames).map
    (fun source => runPrivateMethodCall fuel defaultSplitLimit table ⟨before.thisValue⟩ source before)
def sourceCollect (fuel : Nat) (table : PrivateMethodTable) (before : State) : Option (Except EvalError Completion) :=
  (parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames).map
    (fun source => executePrivateControl fuel defaultSplitLimit table source before)

end HonoLean.Upstream.NodeCaptureCollect
