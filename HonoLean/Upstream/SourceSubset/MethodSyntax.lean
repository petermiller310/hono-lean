import HonoLean.Upstream.SourceSubset.Syntax

namespace HonoLean.Upstream.SourceSubset

/-- Retained TypeScript parameter metadata. Optional does not change runtime
argument binding: every missing formal receives undefined. -/
structure MethodParameter where
  name : String
  optional : Bool := false
  annotation : TypeSyntax
  deriving Repr

/-- A supported ordinary strict private method, without defaults, rest,
destructuring, async/generator/accessor syntax or super. Dynamic method-body
this is represented explicitly. -/
structure PrivateMethod where
  name : String
  parameters : List MethodParameter
  result : TypeSyntax
  body : List Stmt
  deriving Repr

/-- this is a receiver expression, not an ordinary lexical identifier. -/
inductive MethodReceiver where
  | this
  | expression (value : Expr)
  deriving Repr

/-- An added top-level call-entry syntax. Nested private-method invocation
remains outside the older expression/statement evaluator. -/
structure PrivateMethodCall where
  receiver : MethodReceiver
  spelling : String
  arguments : List Expr
  deriving Repr

end HonoLean.Upstream.SourceSubset
