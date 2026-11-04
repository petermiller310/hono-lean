import HonoLean.Upstream.NodeRegExpExec.Source
import HonoLean.Upstream.SourceSubset.RegExpCallRules
import HonoLean.Upstream.NodeCaptureGuard.Composition
import HonoLean.Upstream.NodeExecCall.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodeRegExpExec
open SourceSubset ECMA2025

def DigitsLanguage (input : JSString) : Prop :=
  input ≠ [] ∧ ∀ unit ∈ input, 48 ≤ unit.toNat ∧ unit.toNat ≤ 57
instance (input : JSString) : Decidable (DigitsLanguage input) := inferInstanceAs (Decidable (_ ∧ ∀ unit ∈ input, _))

/-- CURRENT saved builtin identity and initialized receiver, not an exec-name
specialcase or a supplied match. Original source/flags are internal record facts;
public source/flags can be shadowed independently. lastIndex is ONLY the actual
ordinary own numeric descriptor. Known older tables are separate from the new
builtin interval; native constructor/getPattern/cache provenance is still open. -/
structure Inputs (before : RegExpCallState) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (builtins : RegExpBuiltinTable) (matcher handle : Nat) (input : JSString) (record : RangeRegExpRecord)
    (object : OrdinaryObject) (last : Int) (writable : Bool) : Prop where
  matcherBinding : before.ambient.environment.lookup "matcher" = some (.object matcher)
  inputBinding : before.ambient.environment.lookup "restPathString" = some (.string input)
  current : ∃ write enumerable configurable depth,
    NodeCaptureGuard.DescriptorPath before.ambient.objects NodeExecCall.execKey matcher (some (.data (.function handle) write enumerable configurable)) depth ∧ depth ≤ propertyFuel
  noArgBeforeMember : before.ambient.functions.length ≤ members.base
  privateBeforeMember : methods.base + methods.entries.length ≤ members.base
  functionsBeforeMember : functions.base + functions.entries.length ≤ members.base
  membersBeforeBuiltin : members.base + members.entries.length ≤ builtins.base
  handleBound : builtins.base ≤ handle
  identity : builtins.entries[handle - builtins.base]? = some .regexpExec
  brand : before.brands.lookup matcher = some record
  initialized : initializeRangeRecord digitsPattern [] = some record
  objectFound : before.ambient.objects[matcher]? = some object
  lastIndex : object.own.lookup lastIndexKey = some (.data (.number last) writable false false)
  numericBound : last.natAbs ≤ SourceSubset.maximumSafeInteger

def returnedValue (before : RegExpCallState) (input : JSString) : Value := rangeExecValue 48 57 before input
def callState (before : RegExpCallState) (input : JSString) : RegExpCallState := rangeExecState 48 57 before input
def resultState (before : RegExpCallState) (input : JSString) : RegExpCallState :=
  {callState before input with ambient := {(callState before input).ambient with environment := ("m", returnedValue before input) :: before.ambient.environment}}

/-- Operational call-order evidence, independent of the declaration runner.
No expected body result occurs in the headline's INPUTS: compiled execution
below derives this evidence from initial source/internal/descriptor facts. -/
structure CallPhases (fuel : Nat) (before : RegExpCallState) (matcher handle : Nat) (input : JSString) : Prop where
  receiverFirst : evalExpression fuel defaultSplitLimit NodeExecCall.receiver before.ambient = .ok (.object matcher, before.ambient)
  currentGet : prepareMethod (.object matcher) "exec" before.ambient = .ok (.member (.object matcher) (.function handle))
  argumentNext : evalArguments fuel defaultSplitLimit NodeExecCall.arguments before.ambient = .ok ([.string input], before.ambient)
  builtinExecuted : invokeRegExpExec (.object matcher) [.string input] before = .ok (returnedValue before input, callState before input)

/-- Independent digit-language result and observable descriptor/frame facts.
Success has ONE new match array, groups is OWN undefined, and null failure has
no new array/global-match accumulator. Observers are explicitly the five-field
result projection, not full native Array/execution/frontend adequacy. -/
structure Contract (fuel : Nat) (before after : RegExpCallState) (matcher handle : Nat) (input : JSString)
    (object : OrdinaryObject) (last : Int) (writable : Bool) : Prop where
  phases : CallPhases fuel before matcher handle input
  mBinding : after.ambient.environment.lookup "m" = some (returnedValue before input)
  environment : after.ambient.environment = ("m", returnedValue before input) :: before.ambient.environment
  language : (returnedValue before input = .array before.ambient.heap.length ↔ DigitsLanguage input)
  success : DigitsLanguage input → after.ambient.heap = before.ambient.heap ++ [[.string input]] ∧
    after.results = (before.ambient.heap.length, ⟨0, input⟩) :: before.results ∧
    observeRegExpResult after before.ambient.heap.length .zero = some (.data (.string input) true true true) ∧
    observeRegExpResult after before.ambient.heap.length .length = some (.data (.number 1) true false false) ∧
    observeRegExpResult after before.ambient.heap.length .index = some (.data (.number 0) true true true) ∧
    observeRegExpResult after before.ambient.heap.length .input = some (.data (.string input) true true true) ∧
    observeRegExpResult after before.ambient.heap.length .groups = some (.data .undefined true true true)
  failure : ¬ DigitsLanguage input → returnedValue before input = .null ∧ after.ambient.heap = before.ambient.heap ∧ after.results = before.results
  oldArrays : ∀ reference, reference < before.ambient.heap.length → after.ambient.heap[reference]? = before.ambient.heap[reference]?
  objects : after.ambient.objects = before.ambient.objects
  lastIndex : after.ambient.objects[matcher]? = some object ∧ object.own.lookup lastIndexKey = some (.data (.number last) writable false false)
  functions : after.ambient.functions = before.ambient.functions
  privates : after.ambient.privates = before.ambient.privates
  sets : after.ambient.sets = before.ambient.sets
  thisValue : after.ambient.thisValue = before.ambient.thisValue
  brands : after.brands = before.brands

end HonoLean.Upstream.NodeRegExpExec
