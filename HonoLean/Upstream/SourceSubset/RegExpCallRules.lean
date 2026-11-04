import HonoLean.Upstream.SourceSubset.RegExpCall

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Pure parser/compiler initialization, not a proof of native constructor,
getPattern/cache/tuple allocation or an arbitrary callable matcher oracle. -/
def initializeRangeRecord (source flags : JSString) : Option RangeRegExpRecord := do
  if !flags.isEmpty then none else do
  let ast ← RangeRegExp.parse source
  let compiled ← RangeRegExp.compile ast
  pure ⟨source, flags, compiled⟩

def digitsPattern : JSString := [94, 91, 48, 45, 57, 93, 43, 36]
def digitsRecord : RangeRegExpRecord := ⟨digitsPattern, [], RangeRegExp.code 48 57⟩
theorem initialize_digits : initializeRangeRecord digitsPattern [] = some digitsRecord := rfl

theorem numericToLength_int (value : Int) (safe : value.natAbs ≤ maximumSafeInteger) :
    numericToLength (.number value) = .ok value.toNat := by simp [numericToLength, safe]

def rangeExecValue (lower upper : UInt16) (before : RegExpCallState) (input : JSString) : Value :=
  if RangeRegExp.Accepted lower upper input then .array before.ambient.heap.length else .null

def rangeExecState (lower upper : UInt16) (before : RegExpCallState) (input : JSString) : RegExpCallState :=
  if RangeRegExp.Accepted lower upper input then
    {before with
      ambient := {before.ambient with heap := before.ambient.heap ++ [[.string input]]}
      results := (before.ambient.heap.length, ⟨0, input⟩) :: before.results}
  else before

/-- Numeric lastIndex is read/ToLength-converted from its actual ordinary DATA
descriptor. The value is NOT an internal record cache; negative/large-for-input
or readonly values survive unchanged because this branch is nonglobal. -/
theorem invokeRegExpExec_range (before : RegExpCallState) (receiver : Nat) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (input : JSString) (rest : List Value) (last : Int) (writable : Bool) (lower upper : UInt16)
    (brand : before.brands.lookup receiver = some record) (found : before.ambient.objects[receiver]? = some object)
    (lastIndex : object.own.lookup lastIndexKey = some (.data (.number last) writable false false))
    (safe : last.natAbs ≤ maximumSafeInteger) (flags : record.originalFlags = []) (compiled : record.compiled = RangeRegExp.code lower upper) :
    invokeRegExpExec (.object receiver) (.string input :: rest) before =
      .ok (rangeExecValue lower upper before input, rangeExecState lower upper before input) := by
  have lastRead : getProperty propertyFuel before.ambient.objects receiver lastIndexKey = .ok (.number last) :=
    getProperty_data _ receiver (propertyFuel - 1) lastIndexKey object (.number last) writable false false found lastIndex
  simp only [invokeRegExpExec, brand, bind, Except.bind, pure, Except.pure, List.headD_cons]
  rw [lastRead]
  simp only [Except.mapError, numericToLength_int last safe, flags, List.isEmpty_nil, Bool.not_true]
  rw [compiled, RangeRegExp.execute_anchoredPlus]
  by_cases accepted : RangeRegExp.Accepted lower upper input
  · simp [accepted, rangeExecValue, rangeExecState, materializeRegExpMatch]
  · simp [accepted, rangeExecValue, rangeExecState]

/-- Brand failure happens before any unsupported argument coercion. This is
the native brand TypeError case, unlike excluded numeric/coercion/table inputs. -/
theorem invokeRegExpExec_unbranded (before : RegExpCallState) (receiver : Nat) (arguments : List Value)
    (missing : before.brands.lookup receiver = none) :
    invokeRegExpExec (.object receiver) arguments before = .error .unbrandedReceiver := by
  simp [invokeRegExpExec, missing, bind, Except.bind]
  rfl

theorem runRegExpCall_builtin (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (receiver : Expr) (method : String) (arguments : List Expr)
    (before : RegExpCallState) (receiverState argumentState : State) (receiverValue : Value) (callee : Value) (values : List Value)
    (evaluatedReceiver : evalExpression fuel limit receiver before.ambient = .ok (receiverValue, receiverState))
    (prepared : prepareMethod receiverValue method receiverState = .ok (.member receiverValue callee))
    (evaluatedArguments : evalArguments fuel limit arguments receiverState = .ok (values, argumentState))
    (separated : regExpTablesSeparated methods functions members builtins argumentState = true)
    (identity : builtinAt builtins callee = some .regexpExec) :
    runRegExpCall fuel limit methods functions members builtins receiver method arguments before =
      invokeRegExpExec receiverValue values {before with ambient := argumentState} := by
  simp only [runRegExpCall, evaluatedReceiver, Except.mapError, bind, Except.bind]
  rw [prepared]
  dsimp only
  rw [evaluatedArguments]
  dsimp only
  rw [separated]
  simp only [Bool.not_true]
  rw [resolveRegExpTarget, identity]
  rfl

/-- Frozen ordinary dispatch is preserved with the SAVED callee and effects.
No operand is rerun, no result restriction is imposed, and the source body is
not replaced by a trusted callback. Premises describe the primitive call phases,
not a successful body execution. -/
theorem runRegExpCall_ordinary_reduction (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (receiver : Expr) (method : String) (arguments : List Expr)
    (before : RegExpCallState) (receiverState argumentState : State) (receiverValue : Value) (reference : Nat) (values : List Value) (closure : MemberClosure)
    (evaluatedReceiver : evalExpression fuel limit receiver before.ambient = .ok (receiverValue, receiverState))
    (prepared : prepareMethod receiverValue method receiverState = .ok (.member receiverValue (.function reference)))
    (evaluatedArguments : evalArguments fuel limit arguments receiverState = .ok (values, argumentState))
    (separated : regExpTablesSeparated methods functions members builtins argumentState = true)
    (oldSeparated : memberTableSeparated methods functions members argumentState = true)
    (notBuiltin : builtinAt builtins (.function reference) = none)
    (bound : members.base ≤ reference) (found : members.entries[reference - members.base]? = some closure) :
    runRegExpCall fuel limit methods functions members builtins receiver method arguments before =
      ((runMemberCall fuel limit methods functions members receiver method arguments before.ambient).mapError RegExpCallError.evaluation).map
        (fun (returned, after) => (returned, {before with ambient := after})) := by
  have old := runMemberCall_resolved fuel limit methods functions members receiver method arguments before.ambient receiverState argumentState receiverValue reference values closure
    evaluatedReceiver prepared evaluatedArguments oldSeparated bound found
  rw [old]
  simp only [runRegExpCall, evaluatedReceiver, Except.mapError, bind, Except.bind]
  rw [prepared]
  dsimp only
  rw [evaluatedArguments]
  dsimp only
  rw [separated]
  simp only [Bool.not_true]
  rw [resolveRegExpTarget, notBuiltin]
  simp only [resolveMemberClosure, Nat.not_lt.mpr bound, found, Except.mapError, Except.map,
    invokeRegExpTarget]
  rfl

theorem executeRegExpDeclaration_call (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (name method : String) (receiver argument : Expr) (before after : RegExpCallState) (returned : Value)
    (called : runRegExpCall fuel limit methods functions members builtins receiver method [argument] before = .ok (returned, after)) :
    executeRegExpDeclaration fuel limit methods functions members builtins (.declare name (.call receiver method [argument])) before =
      .ok {after with ambient := {after.ambient with environment := (name, returned) :: after.ambient.environment}} := by
  simp [executeRegExpDeclaration, called, bind, Except.bind, pure, Except.pure]

end HonoLean.Upstream.SourceSubset
