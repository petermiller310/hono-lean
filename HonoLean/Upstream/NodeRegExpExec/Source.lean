import HonoLean.Upstream.NodeRegExpExec.Generated
import HonoLean.Upstream.NodeExecCall.Source
import HonoLean.Upstream.SourceSubset.RegExpCall

set_option autoImplicit false
namespace HonoLean.Upstream.NodeRegExpExec
open SourceSubset ECMA2025

def bindings : List String := NodeExecCall.bindings
def program : Stmt := NodeExecCall.program
def guardCondition : Expr := NodeExecCall.guardCondition

theorem same_source : pinnedSource = NodeExecCall.pinnedSource := by cbv
theorem same_header : pinnedGuardHeader = NodeExecCall.pinnedGuardHeader := by cbv
theorem parses_source : parseMemberDeclaration pinnedSource bindings [] = some program := by
  rw [same_source]
  exact NodeExecCall.parses_source
theorem guard_header_tokens : tokenizePrivateControl pinnedGuardHeader =
    some [.name "if", .punctuation "(", .name "m", .punctuation ")", .punctuation "{", .lineBreak] := by
  rw [same_header]
  exact NodeExecCall.guard_header_tokens

def sourceExec (fuel : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (before : RegExpCallState) : Option (Except RegExpCallError RegExpCallState) :=
  (parseMemberDeclaration pinnedSource bindings []).map
    (fun source => executeRegExpDeclaration fuel defaultSplitLimit methods functions members builtins source before)

end HonoLean.Upstream.NodeRegExpExec
