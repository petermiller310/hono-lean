import HonoLean.Upstream.PatternConstruct.Source

set_option autoImplicit false
namespace HonoLean.Upstream.PatternConstruct
open SourceSubset ECMA2025

def rawBody (lower upper : UInt16) : JSString := [91, lower, 45, upper, 93, 43]
def assembledSource (lower upper : UInt16) : JSString := [94] ++ rawBody lower upper ++ [36]

/-- BEFORE the selected46B expression: actual primitive inputs/dense array,
CURRENT closed standard constructor identity and allocated declared intrinsic
prototype/newTarget interpretation. No brand, compiled program, desired tuple
or successful constructor evaluation is supplied. The earlier label regexp,
cache state/selection and native constructor interpretation remain open. -/
structure Inputs (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor)
    (prototypeObject : OrdinaryObject) : Prop where
  labelBinding : before.ambient.environment.lookup "label" = some (.string label)
  matchBinding : before.ambient.environment.lookup "match" = some (.array matched)
  matchedFound : before.ambient.heap[matched]? = some values
  nameFound : values[1]? = some (.string name)
  bodyFound : values[2]? = some (.string (rawBody lower upper))
  lengthBound : values.length ≤ 4294967295
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  constructorBinding : before.ambient.environment.lookup "RegExp" = some (.function handle)
  noArgBefore : before.ambient.functions.length ≤ context.constructors.base
  methodsBefore : context.methods.base + context.methods.entries.length ≤ context.constructors.base
  functionsBefore : context.functions.base + context.functions.entries.length ≤ context.constructors.base
  membersBefore : context.members.base + context.members.entries.length ≤ context.constructors.base
  builtinsBefore : context.builtins.base + context.builtins.entries.length ≤ context.constructors.base
  handleBound : context.constructors.base ≤ handle
  identity : context.constructors.entries[handle - context.constructors.base]? = some constructor
  prototypeFound : before.ambient.objects[constructor.prototype]? = some prototypeObject

/-- Pure intermediate literal cells. The actual evaluator below derives these
states from the initial array's allocated bound, not from a future table input. -/
def tupleStage (before : RegExpCallState) (contents : List Value) : RegExpCallState :=
  {before with ambient := {before.ambient with heap := before.ambient.heap ++ [contents]}}
def tupleValues (before : RegExpCallState) (label name : JSString) : List Value :=
  [.string label, .string name, .object before.ambient.objects.length]
def resultState (before : RegExpCallState) (prototype : Nat) (lower upper : UInt16) (label name : JSString) : RegExpCallState :=
  regExpConstructedState (tupleStage before (tupleValues before label name)) prototype (constructedRangeRecord lower upper)

/-- Explicit observable allocation/operand phases; this relation is independent
of the whole-expression runner. Callee/template are evaluated after label/name,
and the uninitialized lastIndex descriptor precedes real parsing/initialization.
All these phase equations are OUTPUT evidence, never public entry assumptions. -/
structure ConstructionPhases (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext)
    (label name : JSString) (handle : Nat) (lower upper : UInt16) (prototype : Nat) : Prop where
  tupleReserved : constructArrayState before = tupleStage before []
  labelRead : evalExpression (extra + 13) defaultSplitLimit labelExpr (tupleStage before []).ambient = .ok (.string label, (tupleStage before []).ambient)
  nameRead : evalExpression (extra + 12) defaultSplitLimit nameExpr (tupleStage before [.string label]).ambient = .ok (.string name, (tupleStage before [.string label]).ambient)
  savedCallee : evalExpression (extra + 11) defaultSplitLimit (.variable "RegExp") (tupleStage before [.string label, .string name]).ambient =
    .ok (.function handle, (tupleStage before [.string label, .string name]).ambient)
  templateRead : evalRegExpConstruct (extra + 11) defaultSplitLimit context templateExpr (tupleStage before [.string label, .string name]) =
    .ok (.string (assembledSource lower upper), tupleStage before [.string label, .string name])
  allocated : (regExpAllocatedState (tupleStage before [.string label, .string name]) prototype).ambient.objects[before.ambient.objects.length]? =
    some (uninitializedRegExpObject prototype)
  initialized : initializeAllocatedRegExp before.ambient.objects.length (assembledSource lower upper)
      (regExpAllocatedState (tupleStage before [.string label, .string name]) prototype) =
    .ok (.object before.ambient.objects.length, regExpConstructedState (tupleStage before [.string label, .string name]) prototype (constructedRangeRecord lower upper))

/-- Independent shallow tuple, fresh initialized ordinary object, real internal
source/code and old component frames. This is the selected expression only;
no full conditional/cache/tuple-destructuring/native adequacy claim follows. -/
structure Contract (before after : RegExpCallState) (returned : Value) (label name : JSString)
    (prototype : Nat) (lower upper : UInt16) : Prop where
  tupleFresh : returned = .array before.ambient.heap.length
  tupleContents : after.ambient.heap[before.ambient.heap.length]? = some (tupleValues before label name)
  tupleCount : after.ambient.heap.length = before.ambient.heap.length + 1
  regexFound : after.ambient.objects[before.ambient.objects.length]? = some (initializedRegExpObject prototype)
  regexCount : after.ambient.objects.length = before.ambient.objects.length + 1
  prototypeKept : (initializedRegExpObject prototype).prototype = some prototype
  lastIndex : (initializedRegExpObject prototype).own.lookup lastIndexKey = some (.data (.number 0) true false false)
  internal : after.brands.lookup before.ambient.objects.length = some (constructedRangeRecord lower upper)
  source : (constructedRangeRecord lower upper).originalSource = assembledSource lower upper
  flags : (constructedRangeRecord lower upper).originalFlags = []
  compiled : (constructedRangeRecord lower upper).compiled = RangeRegExp.code lower upper
  oldArrays : ∀ reference, reference < before.ambient.heap.length → after.ambient.heap[reference]? = before.ambient.heap[reference]?
  oldObjects : ∀ reference, reference < before.ambient.objects.length → after.ambient.objects[reference]? = before.ambient.objects[reference]?
  otherBrands : ∀ reference, reference ≠ before.ambient.objects.length → after.brands.lookup reference = before.brands.lookup reference
  environment : after.ambient.environment = before.ambient.environment
  thisValue : after.ambient.thisValue = before.ambient.thisValue
  functions : after.ambient.functions = before.ambient.functions
  sets : after.ambient.sets = before.ambient.sets
  privates : after.ambient.privates = before.ambient.privates
  results : after.results = before.results

end HonoLean.Upstream.PatternConstruct
