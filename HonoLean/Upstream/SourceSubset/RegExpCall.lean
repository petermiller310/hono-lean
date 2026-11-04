import HonoLean.Upstream.SourceSubset.MemberCall
import HonoLean.Upstream.ECMA2025.RangeRegExp
import HonoLean.Upstream.ECMA2025.RegExpResult

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Internal state, keyed by the receiver identity. The public source/flags
properties are not the internal original source/flags or compiled matcher.
There is NO cached lastIndex value here: that is an ordinary property Get. -/
structure RangeRegExpRecord where
  originalSource : JSString
  originalFlags : JSString := []
  compiled : List RangeRegExp.Instruction
  deriving Repr, DecidableEq

/-- The ambient state is retained exactly. Result metadata projects just five
observed array properties; normal Array/prototype/descriptor adequacy is open. -/
structure RegExpCallState where
  ambient : State
  brands : List (Nat × RangeRegExpRecord) := []
  results : List (Nat × RegExpMatchView) := []
  deriving Repr

inductive RegExpBuiltin where
  | regexpExec
  deriving Repr, DecidableEq
structure RegExpBuiltinTable where
  base : Nat
  entries : List RegExpBuiltin
  deriving Repr, DecidableEq
inductive RegExpCallTarget where
  | ordinary (closure : MemberClosure)
  | builtin (kind : RegExpBuiltin)
  deriving Repr

/-- Only unbrandedReceiver identifies the builtin's native brand TypeError.
All unsupported inputs/flags/numbers/tables are explicit MODEL boundaries;
Except retains neither partial error states nor rollback/engine guarantees. -/
inductive RegExpCallError where
  | evaluation (error : EvalError)
  | unbrandedReceiver
  | unsupportedCoercion
  | unsupportedNumber
  | unsupportedFlags
  | representation
  | exhausted
  deriving Repr, DecidableEq

def lastIndexKey : JSString := [108, 97, 115, 116, 73, 110, 100, 101, 120]
def maximumSafeInteger : Nat := 9007199254740991

/-- Exact integer-number ToLength specialization. Negative integers become0;
fractional values, infinities/NaN and distinguishable -0 are not represented. -/
def numericToLength : Value → Except RegExpCallError Nat
  | .number value => if value.natAbs ≤ maximumSafeInteger then .ok value.toNat else .error .unsupportedNumber
  | _ => .error .unsupportedNumber

def builtinAt (table : RegExpBuiltinTable) (callee : Value) : Option RegExpBuiltin :=
  match callee with
  | .function reference => if table.base ≤ reference then table.entries[reference - table.base]? else none
  | _ => none

def resolveRegExpTarget (members : MemberTable) (builtins : RegExpBuiltinTable) (callee : Value) : Except RegExpCallError RegExpCallTarget :=
  match builtinAt builtins callee with
  | some builtin => .ok (.builtin builtin)
  | none => (resolveMemberClosure members callee).mapError .evaluation |>.map RegExpCallTarget.ordinary

def regExpTablesSeparated (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (state : State) : Bool :=
  memberTableSeparated methods functions members state &&
  (builtins.entries.isEmpty || decide (state.functions.length ≤ builtins.base)) &&
  (builtins.entries.isEmpty || methods.entries.isEmpty || decide (builtins.base + builtins.entries.length ≤ methods.base) ||
    decide (methods.base + methods.entries.length ≤ builtins.base)) &&
  (builtins.entries.isEmpty || functions.entries.isEmpty || decide (builtins.base + builtins.entries.length ≤ functions.base) ||
    decide (functions.base + functions.entries.length ≤ builtins.base)) &&
  (builtins.entries.isEmpty || members.entries.isEmpty || decide (builtins.base + builtins.entries.length ≤ members.base) ||
    decide (members.base + members.entries.length ≤ builtins.base))

def materializeRegExpMatch (before : RegExpCallState) (input : JSString) (matched : RangeRegExp.Match) : Value × RegExpCallState :=
  (.array before.ambient.heap.length,
    {before with
      ambient := {before.ambient with heap := before.ambient.heap ++ [[.string ((input.drop matched.start).take (matched.stop - matched.start))]]}
      results := (before.ambient.heap.length, ⟨matched.start, input⟩) :: before.results})

/-- Closed builtin implementation: brand BEFORE primitive string coercion,
then real lastIndex Get/ToLength, internal flags and actual compiled execution.
The nonglobal local start is0; no Set(lastIndex) occurs on either outcome.
No arbitrary callback, given match result, global@@match or exec-name rule. -/
def invokeRegExpExec (receiver : Value) (arguments : List Value) (before : RegExpCallState) : Except RegExpCallError (Value × RegExpCallState) := do
  let (reference, record) ← match receiver with
    | .object reference => match before.brands.lookup reference with
      | some record => pure (reference, record)
      | none => throw .unbrandedReceiver
    | _ => throw .unbrandedReceiver
  let input ← match arguments.headD .undefined with
    | .string input => pure input
    | _ => throw .unsupportedCoercion
  let last ← (getProperty propertyFuel before.ambient.objects reference lastIndexKey).mapError (RegExpCallError.evaluation ∘ EvalError.objectError)
  let _ ← numericToLength last
  if !record.originalFlags.isEmpty then throw .unsupportedFlags else do
  match RangeRegExp.execute record.compiled input with
  | .exhausted => throw .exhausted
  | .noMatch => pure (.null, before)
  | .matched matched =>
    if matched.captures.isEmpty && decide (matched.start ≤ matched.stop ∧ matched.stop ≤ input.length) then
      pure (materializeRegExpMatch before input matched)
    else throw .representation

/-- Ordinary closures reuse the frozen actual body interpreter and restore its
caller. Metadata/brands are framed; numeric array observations still read the
returned CURRENT ambient heap rather than a stale sidecar length. -/
def invokeRegExpTarget (fuel limit : Nat) (target : RegExpCallTarget) (receiver : Value)
    (arguments : List Value) (before : RegExpCallState) : Except RegExpCallError (Value × RegExpCallState) :=
  match target with
  | .ordinary closure =>
    ((invokeMemberClosure fuel limit closure receiver arguments before.ambient).mapError .evaluation).map
      (fun (returned, after) => (returned, {before with ambient := after}))
  | .builtin .regexpExec => invokeRegExpExec receiver arguments before

/-- The current Get is saved BEFORE arguments; range checking and closed
identity resolution occur AFTER all arguments. The spelling selects only Get's
property key. A copied builtin identity under another spelling is still builtin;
a replaced exec ordinary closure retains arbitrary actual return values. -/
def runRegExpCall (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (receiver : Expr) (method : String) (arguments : List Expr)
    (before : RegExpCallState) : Except RegExpCallError (Value × RegExpCallState) := do
  let (receiver, receiverState) ← (evalExpression fuel limit receiver before.ambient).mapError .evaluation
  let saved ← (prepareMethod receiver method receiverState).mapError .evaluation
  let (arguments, afterArguments) ← (evalArguments fuel limit arguments receiverState).mapError .evaluation
  if !regExpTablesSeparated methods functions members builtins afterArguments then throw .representation else do
  match saved with
  | .member receiver callee =>
    let target ← resolveRegExpTarget members builtins callee
    invokeRegExpTarget fuel limit target receiver arguments {before with ambient := afterArguments}
  | .standard _ _ => throw (.evaluation .unsupported)

def executeRegExpDeclaration (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (declaration : Stmt) (before : RegExpCallState) : Except RegExpCallError RegExpCallState := do
  match declaration with
  | .declare name (.call receiver method [argument]) =>
    let (returned, after) ← runRegExpCall fuel limit methods functions members builtins receiver method [argument] before
    pure {after with ambient := {after.ambient with environment := (name, returned) :: after.ambient.environment}}
  | _ => throw (.evaluation .unsupported)

def observeRegExpResult (state : RegExpCallState) (reference : Nat) (property : RegExpMatchProperty) : Option PropertyDescriptor := do
  let view ← state.results.lookup reference
  observeRegExpMatch state.ambient.heap reference view property

end HonoLean.Upstream.SourceSubset
