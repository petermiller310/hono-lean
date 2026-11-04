import HonoLean.Upstream.GetPatternBody.Source

set_option autoImplicit false
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025 GetPatternBody

abbrev CellRef := Nat
abbrev EnvironmentRef := Nat

inductive BindingKind where
  | constant | parameter | mutable
  deriving Repr, DecidableEq

/-- `none` denotes the temporal dead zone, not the value `undefined`. -/
structure Cell where
  kind : BindingKind
  value : Option Value
  deriving Repr, DecidableEq

/-- A frame maps names to identities. Reading a nearer uninitialized cell
does not continue into the parent. Fuel makes malformed cycles explicit. -/
structure Environment where
  bindings : List (String × CellRef) := []
  parent : Option EnvironmentRef := none
  deriving Repr, DecidableEq

/-- A separate callable identity avoids aliasing legacy intrinsic handles.
The closure record supplies its authoritative ordinary-object identity. -/
structure ArrowHandle where
  index : Nat
  deriving Repr, DecidableEq

structure ArrowClosure where
  program : ExportedArrow
  environment : EnvironmentRef
  lexicalThis : Value
  objectReference : Nat
  deriving Repr

structure Runtime where
  data : LabelMatchState
  cells : List Cell := []
  environments : List Environment := []
  closures : List ArrowClosure := []
  current : EnvironmentRef := 0
  thisValue : Value := .undefined
  deriving Repr

inductive LexicalError where
  | missingBinding | invalidCell | invalidEnvironment | temporalDeadZone
  | immutableBinding | alreadyInitialized | invalidCallable | notConstructible
  | invalidFunctionPrototype | exhausted | unsupported
  deriving Repr, DecidableEq

inductive Error where
  | lexical (error : LexicalError)
  | body (error : PatternCacheError)
  deriving Repr, DecidableEq

/-- Legacy body errors do not retain partial state. This case explicitly
withholds an error-state/rollback claim; it is not a native throw completion. -/
inductive Outcome where
  | returned (value : Value) (after : Runtime)
  | outsideModel (error : Error)
  deriving Repr

structure Caller where
  environment : EnvironmentRef
  thisValue : Value
  legacyEnvironment : List (String × Value)
  legacyThis : Value
  deriving Repr

inductive Completion where
  | normal (after : Runtime)
  | returned (value : Value) (after : Runtime)
  deriving Repr

end HonoLean.Upstream.LexicalArrow
