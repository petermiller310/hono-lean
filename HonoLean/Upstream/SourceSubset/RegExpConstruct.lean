import HonoLean.Upstream.SourceSubset.RegExpConstructSyntax
import HonoLean.Upstream.SourceSubset.RegExpCallRules

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Closed standard constructor interpretation. Native realm/prototype and
newTarget adequacy are explicit: the selected standard constructor is also
newTarget and its declared standard prototype is this allocated ordinary cell.
This is NOT a callback that supplies the desired compiled record. -/
structure RegExpConstructor where
  prototype : Nat
  deriving Repr, DecidableEq
structure RegExpConstructorTable where
  base : Nat
  entries : List RegExpConstructor
  deriving Repr, DecidableEq
structure RegExpConstructContext where
  methods : PrivateMethodTable
  functions : FunctionTable
  members : MemberTable
  builtins : RegExpBuiltinTable
  constructors : RegExpConstructorTable
  deriving Repr

inductive RegExpConstructError where
  | evaluation (error : EvalError)
  | constructorDomain
  | prototypeDomain
  | coercionDomain
  | grammarDomain
  | representation
  | exhausted
  deriving Repr, DecidableEq

/-- Only the new constructor identity interval is checked here. Existing
contexts must have their own valid interpretation; no old closure is invoked
or accidentally interpreted as a constructor. These are model-domain checks,
not a claim that every other JS constructor would throw. -/
def constructorTablesSeparated (context : RegExpConstructContext) (state : State) : Bool :=
  let table := context.constructors
  let apart := fun (base length : Nat) => length == 0 || table.entries.isEmpty ||
    decide (table.base + table.entries.length ≤ base) || decide (base + length ≤ table.base)
  (table.entries.isEmpty || decide (state.functions.length ≤ table.base)) &&
    apart context.methods.base context.methods.entries.length &&
    apart context.functions.base context.functions.entries.length &&
    apart context.members.base context.members.entries.length &&
    apart context.builtins.base context.builtins.entries.length

def constructorAt (table : RegExpConstructorTable) : Value → Option RegExpConstructor
  | .function reference => if table.base ≤ reference then table.entries[reference - table.base]? else none
  | _ => none

/-- Primitive STRING substitution only. All UTF16 units of the operand are
preserved exactly. Numeric/other ToString, object coercion, tagged templates,
escapes and general constructor grammar remain explicit frontiers. -/
def constructTemplateValue (head : JSString) (value : Value) (tail : JSString) : Except RegExpConstructError Value :=
  match value with
  | .string body => .ok (.string (head ++ body ++ tail))
  | _ => .error .coercionDomain

def uninitializedRegExpObject (prototype : Nat) : OrdinaryObject :=
  ⟨[(lastIndexKey, .data .undefined true false false)], some prototype, true⟩
def initializedRegExpObject (prototype : Nat) : OrdinaryObject :=
  ⟨[(lastIndexKey, .data (.number 0) true false false)], some prototype, true⟩

def regExpAllocatedState (before : RegExpCallState) (prototype : Nat) : RegExpCallState :=
  {before with ambient := {before.ambient with objects := before.ambient.objects ++ [uninitializedRegExpObject prototype]}}

def regExpConstructedState (before : RegExpCallState) (prototype : Nat) (record : RangeRegExpRecord) : RegExpCallState :=
  {before with
    ambient := {before.ambient with objects := before.ambient.objects ++ [initializedRegExpObject prototype]}
    brands := (before.ambient.objects.length, record) :: before.brands}

/-- RegExpAllocate precedes RegExpInitialize: first an ordinary object with
own lastIndex=undefined; then the actual parser/compiler; then ordinary Set+0.
The brands map stores INITIALIZED compiled records. It deliberately omits
the transient undefined internal-slot contents installed by native allocation;
it is not an intermediate native brand/slot-absence observation claim.
An Except failure exposes no intermediate state, rollback or native throwtrace.
No global@@match accumulator or result metadata is created by construction. -/
def initializeAllocatedRegExp (reference : Nat) (source : JSString) (before : RegExpCallState) :
    Except RegExpConstructError (Value × RegExpCallState) := do
  let record ← match initializeRangeRecord source [] with
    | some record => .ok record
    | none => .error .grammarDomain
  let objects ← (setProperty propertyFuel before.ambient.objects reference lastIndexKey (.number 0)).mapError
    (RegExpConstructError.evaluation ∘ EvalError.objectError)
  pure (.object reference, {before with
    ambient := {before.ambient with objects}
    brands := (reference, record) :: before.brands})

def invokeRegExpConstructor (context : RegExpConstructContext) (callee argument : Value) (before : RegExpCallState) :
    Except RegExpConstructError (Value × RegExpCallState) := do
  if !constructorTablesSeparated context before.ambient then throw .representation else do
  let constructor ← match constructorAt context.constructors callee with
    | some constructor => .ok constructor
    | none => .error .constructorDomain
  let _ ← match before.ambient.objects[constructor.prototype]? with
    | some object => .ok object
    | none => .error .prototypeDomain
  let allocated := regExpAllocatedState before constructor.prototype
  -- Primitive string is the admitted RegExpInitialize source specialization.
  -- The allocation above precedes source initialization/coercion admission.
  let source ← match argument with
    | .string source => .ok source
    | _ => .error .coercionDomain
  initializeAllocatedRegExp before.ambient.objects.length source allocated

def constructArrayState (before : RegExpCallState) : RegExpCallState :=
  {before with ambient := {before.ambient with heap := before.ambient.heap ++ [[]]}}

def appendConstructElement (reference : Nat) (value : Value) (before : RegExpCallState) : Except RegExpConstructError RegExpCallState :=
  ((appendLiteralElements reference [value] before.ambient).mapError .evaluation).map
    (fun after => {before with ambient := after})

mutual
  /-- A real array literal allocates [] before the first element. A real new
  expression saves its callee before evaluating its template argument; identity
  and constructor-domain checks happen only AFTER argument evaluation. -/
  def evalRegExpConstruct : Nat → Nat → RegExpConstructContext → RegExpConstructExpr → RegExpCallState →
      Except RegExpConstructError (Value × RegExpCallState)
    | 0, _, _, _, _ => .error .exhausted
    | fuel + 1, limit, context, expression, before => do
      match expression with
      | .ordinary expression =>
        ((evalExpression fuel limit expression before.ambient).mapError .evaluation).map
          (fun (value, after) => (value, {before with ambient := after}))
      | .template head operand tail =>
        let (value, after) ← (evalExpression fuel limit operand before.ambient).mapError .evaluation
        let value ← constructTemplateValue head value tail
        pure (value, {before with ambient := after})
      | .construct callee argument =>
        let (saved, afterCallee) ← (evalExpression fuel limit callee before.ambient).mapError .evaluation
        let (argument, afterArgument) ← evalRegExpConstruct fuel limit context argument {before with ambient := afterCallee}
        invokeRegExpConstructor context saved argument afterArgument
      | .arrayLiteral elements =>
        let reference := before.ambient.heap.length
        let after ← evalRegExpConstructElements fuel limit context reference elements (constructArrayState before)
        pure (.array reference, after)

  def evalRegExpConstructElements : Nat → Nat → RegExpConstructContext → Nat → List RegExpConstructExpr → RegExpCallState →
      Except RegExpConstructError RegExpCallState
    | 0, _, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, _, [], before => .ok before
    | fuel + 1, limit, context, reference, head :: tail, before => do
      let (value, after) ← evalRegExpConstruct fuel limit context head before
      let after ← appendConstructElement reference value after
      evalRegExpConstructElements fuel limit context reference tail after
end

end HonoLean.Upstream.SourceSubset
