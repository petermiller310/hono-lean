import Std

namespace HonoLean.Upstream.SourceSubset

/-- JavaScript string contents are UTF-16 code units, including lone surrogates. -/
abbrev JSString := List UInt16

inductive NumericComparison where
  | less | lessEqual
  deriving Repr

/-- The only checked TypeScript constructor type argument in this subset.
Its presence is retained in the AST, rather than silently stripping text. -/
inductive ConstructorType where
  | string
  deriving Repr

/-- Retained grammar metadata, not a runtime type test or resolved TS type.
constAssertion is admitted only in the assertion context by the parser. -/
inductive TypeSyntax where
  | named (name : String)
  | application (base : TypeSyntax) (arguments : List TypeSyntax)
  | array (element : TypeSyntax)
  | union (left right : TypeSyntax)
  | constAssertion
  deriving Repr

inductive Expr where
  | variable (name : String)
  | this
  | string (contents : JSString)
  | number (value : Int)
  | index (receiver key : Expr)
  | call (receiver : Expr) (method : String) (arguments : List Expr)
  | strictEqual (left right : Expr)
  | compare (operation : NumericComparison) (left right : Expr)
  | subtract (left right : Expr)
  | conditional (test yes no : Expr)
  | null
  | boolean (value : Bool)
  | property (receiver : Expr) (key : JSString)
  | optionalIndex (receiver key : Expr)
  | logicalNot (value : Expr)
  | logicalAnd (left right : Expr)
  | nullish (left right : Expr)
  | invoke (callee : Expr) (arguments : List Expr)
  | construct (callee : Expr) (typeArgument : Option ConstructorType) (arguments : List Expr)
  | arrayLiteral (elements : List (Bool × Expr))
  | objectLiteral (fields : List (Expr × Expr))
  | preIncrement (name : String)
  | privateProperty (receiver : Expr) (spelling : String)
  | logicalOr (left right : Expr)
  | typeAssertion (value : Expr) (type : TypeSyntax)
  deriving Repr

/-- Property assignment with reference evaluation before the right-hand value. -/
structure Assignment where
  target : Expr
  value : Expr
  deriving Repr

inductive Stmt where
  | declare (name : String) (initializer : Expr)
  | typedDeclare (name : String) (type : TypeSyntax) (initializer : Expr)
  | mutableDeclare (name : String) (annotation : Option TypeSyntax) (initializer : Expr)
  | evaluate (expression : Expr)
  | branch (condition : Expr) (body : List Stmt)
  | ret (expression : Expr)
  | assign (assignment : Assignment)
  | countedFor (initializers : List (String × Expr)) (condition : Expr)
      (incrementName : String) (body : List Stmt)
  deriving Repr

/-- Direct block-local const names; nested counted-for scopes own their names. -/
def declaredNames (statements : List Stmt) : List String :=
  statements.filterMap (fun statement => match statement with
    | .declare name _ => some name
    | .typedDeclare name _ _ => some name
    | .mutableDeclare name _ _ => some name
    | _ => none)

/-- Both supported source entry points check a string parameter; each checks
its own string or string[] result annotation before producing this syntax. -/
structure Function where
  name : String
  parameter : String
  body : List Stmt
  deriving Repr

/-- Zero-parameter, expression-bodied declaration using the shared expressions.
This records actual syntax rather than inventing a dummy parameter binding. -/
structure NoArgFunction where
  name : String
  body : Expr
  deriving Repr

/-- A supported private data-field declaration. Optional/type syntax is retained
as grammar metadata; it performs no runtime check. An absent initializer adds
an own private slot whose value is undefined. -/
structure PrivateField where
  name : String
  optional : Bool := false
  annotation : Option TypeSyntax := none
  initializer : Option Expr := none
  deriving Repr

end HonoLean.Upstream.SourceSubset
