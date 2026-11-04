import HonoLean.Upstream.SourceSubset.MethodSyntax

namespace HonoLean.Upstream.SourceSubset

/-- An explicit outer control extension. Ordinary leaves reuse Stmt; only this
entry can dispatch a private method call or a nested two-arm conditional.
Admission restricts ordinary leaves to simple statements, fresh declarations
to the root, and expressions to ones without direct lexical writes. -/
inductive PrivateControlStmt where
  | ordinary (statement : Stmt)
  | privateCall (call : PrivateMethodCall)
  | branch (condition : Expr) (yes no : List PrivateControlStmt)
  deriving Repr

/-- Only direct root declarations belong to the standalone fragment scope.
The parser rejects declarations inside branches. -/
def privateControlDeclaredNames (program : List PrivateControlStmt) : List String :=
  program.filterMap fun statement => match statement with
    | .ordinary (.declare name _) | .ordinary (.typedDeclare name _ _)
    | .ordinary (.mutableDeclare name _ _) => some name
    | _ => none

end HonoLean.Upstream.SourceSubset
