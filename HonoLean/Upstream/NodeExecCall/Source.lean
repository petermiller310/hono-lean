import HonoLean.Upstream.NodeExecCall.Generated
import HonoLean.Upstream.SourceSubset.MemberCall

set_option autoImplicit false
namespace HonoLean.Upstream.NodeExecCall
open SourceSubset ECMA2025

def bindings : List String := ["matcher", "restPathString"]
def receiver : Expr := .variable "matcher"
def arguments : List Expr := [.variable "restPathString"]
def program : Stmt := .declare "m" (.call receiver "exec" arguments)
def guardCondition : Expr := .variable "m"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_source : parseMemberDeclaration pinnedSource bindings [] = some program := by cbv

/-- Only the actual if-header tokens are bound. No invented body is appended
and no execution or reachability of the enclosing conditional is claimed. -/
theorem guard_header_tokens : tokenizePrivateControl pinnedGuardHeader =
    some [.name "if", .punctuation "(", .name "m", .punctuation ")", .punctuation "{", .lineBreak] := by cbv

def sourceExec (fuel : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (before : State) : Option (Except EvalError State) :=
  (parseMemberDeclaration pinnedSource bindings []).map
    (fun source => executeMemberDeclaration fuel defaultSplitLimit methods functions members source before)

end HonoLean.Upstream.NodeExecCall
