import HonoLean.Upstream.NodeParamsInit.Generated
import HonoLean.Upstream.SourceSubset.ObjectInit
import HonoLean.Upstream.NodePrivateWrite.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeParamsInit
open SourceSubset ECMA2025

def bindings : List String := ["node", "emptyParams"]
def privateNames : List String := NodePrivateCall.classPrivateNames
def paramsRead : Expr := .privateProperty (.variable "node") "params"
def condition : Expr := .strictEqual paramsRead (.variable "emptyParams")
def initializer : ObjectInitExpr := .conditional condition (.objectLiteral []) (.objectLiteral [.spread paramsRead])
def program : ObjectInitDecl := ⟨"params", initializer⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_source : parseObjectInitDeclaration pinnedSource bindings privateNames = some program := by cbv

def sourceInit (fuel : Nat) (before : State) : Option (Except EvalError State) :=
  (parseObjectInitDeclaration pinnedSource bindings privateNames).map
    (fun source => executeObjectInitDeclaration fuel defaultSplitLimit source before)

end HonoLean.Upstream.NodeParamsInit
