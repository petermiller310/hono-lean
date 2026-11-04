import HonoLean.Upstream.GetPatternInvocation.Source
import HonoLean.Upstream.LexicalArrow.Syntax

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternInvocation
open SourceSubset hiding pinnedSource
open ECMA2025
open LexicalArrow

/-- Already evaluated arguments. Evaluation of argument expressions belongs to
the caller boundary; arbitrary additional values remain in this list. -/
def argument (arguments : List Value) (index : Nat) : Value :=
  (arguments[index]?).getD .undefined

/-- The actual two typed parameters erase to ordinary positional JavaScript
parameters. An omitted second argument has the same value as explicit undefined.
Neither a prebound activation nor a desired result is an input. -/
structure Arguments (arguments : List Value) (input : JSString) (next : Option JSString) : Prop where
  label : argument arguments 0 = .string input
  next : argument arguments 1 = PatternCache.nextValue next

def nameKey : JSString := [110,97,109,101]
def lengthKey : JSString := [108,101,110,103,116,104]
def prototypeKey : JSString := [112,114,111,116,111,116,121,112,101]

/-- Creation-time own metadata, independent of the evaluator result. The typed
optional marker is erased, so this source has two formal parameters. A caller
may later mutate these configurable properties; no persistence is assumed. -/
structure FunctionObjectContract (object : OrdinaryObject) : Prop where
  name : object.own.lookup nameKey = some (.data (.string [103,101,116,80,97,116,116,101,114,110]) false false true)
  length : object.own.lookup lengthKey = some (.data (.number 2) false false true)
  noOwnPrototype : object.own.lookup prototypeKey = none

/-- An independent finite environment path. These are initial frame/cell facts,
not a successful GetBindingValue execution or a prepared body environment. -/
inductive BindingPath (environments : List Environment) (name : String) : Nat → Nat → Nat → Prop where
  | here {environment cell : Nat} {frame : Environment} :
      environments[environment]? = some frame → frame.bindings.lookup name = some cell →
      BindingPath environments name environment cell 0
  | parent {environment parent cell depth : Nat} {frame : Environment} :
      environments[environment]? = some frame → frame.bindings.lookup name = none → frame.parent = some parent →
      BindingPath environments name parent cell depth → BindingPath environments name environment cell (depth + 1)

def CellValue (before : Runtime) (environment : Nat) (name : String) (value : Value) : Prop :=
  ∃ cell kind depth, BindingPath before.environments name environment cell depth ∧
    depth < before.environments.length + 1 ∧ before.cells[cell]? = some ⟨kind, some value⟩

/-- Callable identity comes from the closure registry, with its actual parsed
program and environment reference. Mutable object metadata is not call readiness. -/
structure CallableInputs (before : Runtime) (handle : ArrowHandle) (closure : ArrowClosure) : Prop where
  found : before.closures[handle.index]? = some closure
  program : closure.program = GetPatternBody.declaration

structure WildcardInputs (before : Runtime) (handle : ArrowHandle) (closure : ArrowClosure) (arguments : List Value) : Prop
    extends CallableInputs before handle closure where
  label : argument arguments 0 = GetPatternBody.star

structure MissInputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input : JSString) : Prop
    extends CallableInputs before handle closure where
  label : argument arguments 0 = .string input
  realm : LabelRealm before.data context.label
  nonstar : input ≠ [42]
  absent : ¬ ∃ name body, LabelRegExp.Label input name body

/-- Only profiles which actually reach cache access require its initialized
lexical cell. `next` is derived from supplied argument values, including omission.
No copied/canonical environment and no future cache result is supplied. -/
structure HeaderInputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop
    extends CallableInputs before handle closure where
  arguments : Arguments arguments input next
  realm : LabelRealm before.data context.label
  label : LabelRegExp.Label input name body
  cacheCell : CellValue before closure.environment "patternCache" (.object cache)
  cacheFound : before.data.base.regexp.ambient.objects[cache]? = some object
  path : NodeCaptureGuard.DescriptorPath before.data.base.regexp.ambient.objects (PatternCache.key input next) cache descriptor depth
  pathBound : depth ≤ propertyFuel

structure PlainInputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop
    extends HeaderInputs before context handle closure arguments input name none next cache object descriptor depth where
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  writable : PatternCache.WritableData object (PatternCache.key input next) descriptor

structure WarmInputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (input name : JSString) (body : Option JSString) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (value : Value) (writable enumerable configurable : Bool) (depth : Nat) : Prop
    extends HeaderInputs before context handle closure arguments input name body next cache object
      (some (.data value writable enumerable configurable)) depth where
  truthy : SourceSubset.truthy value = true

structure TerminalInputs (before : Runtime) (context : PatternCacheContext) (handle : ArrowHandle) (closure : ArrowClosure)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (cache : Nat) (object : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop
    extends HeaderInputs before context handle closure arguments (LabelMatch.safeRangeLabel name lower upper) name
      (some (PatternConstruct.rawBody lower upper)) next cache object descriptor depth where
  terminal : PatternCacheTerminal.TerminalNext next
  validName : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  writable : PatternCache.WritableData object (PatternCache.key (LabelMatch.safeRangeLabel name lower upper) next) descriptor
  constructorCell : CellValue before closure.environment "RegExp" (.function constructorHandle)
  handleBound : context.label.iterators.constructors.constructors.base ≤ constructorHandle
  identity : context.label.iterators.constructors.constructors.entries[constructorHandle - context.label.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.data.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

/-- Call completion restores the actual caller and preserves all pre-existing
lexical storage. New activation/local cells may be appended by evaluation. -/
structure CallFrame (before after : Runtime) : Prop where
  caller : after.current = before.current
  thisValue : after.thisValue = before.thisValue
  legacyEnvironment : after.data.base.regexp.ambient.environment = before.data.base.regexp.ambient.environment
  legacyThis : after.data.base.regexp.ambient.thisValue = before.data.base.regexp.ambient.thisValue
  oldCells : ∀ reference, reference < before.cells.length → after.cells[reference]? = before.cells[reference]?
  oldEnvironments : ∀ reference, reference < before.environments.length → after.environments[reference]? = before.environments[reference]?
  environmentLength : before.environments.length ≤ after.environments.length
  closures : after.closures = before.closures

structure WildcardContract (before after : Runtime) (returned : Value) : Prop where
  returned : returned = GetPatternBody.star
  data : after.data = before.data
  caller : CallFrame before after

/-- The existing independent data/heap contracts are now paired with the
actual call's lexical/caller frame. They mention initial/final states and
returned values, and contain no interpreter execution as a field. -/
structure PlainContract (before after : Runtime) (context : PatternCacheContext) (input name : JSString)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (returned : Value) : Prop where
  data : PatternCache.PlainContract before.data after.data context input name next cache object returned
  caller : CallFrame before after

structure WarmContract (before after : Runtime) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (cache : Nat) (retained returned : Value) : Prop where
  data : PatternCache.WarmContract before.data after.data context input name body cache retained returned
  caller : CallFrame before after

structure MissContract (before after : Runtime) (context : PatternCacheContext) (input : JSString) (returned : Value) : Prop where
  data : PatternCache.MissContract before.data after.data context input returned
  caller : CallFrame before after

structure TerminalContract (before after : Runtime) (context : PatternCacheContext) (name : JSString) (lower upper : UInt16)
    (next : Option JSString) (cache : Nat) (object : OrdinaryObject) (prototype : Nat) (returned : Value) : Prop where
  data : PatternCacheTerminal.Contract before.data after.data context name lower upper next cache object prototype returned
  caller : CallFrame before after

structure SetupInputs (before : Runtime) (functionPrototype : Nat) (root functionRoot : OrdinaryObject) : Prop where
  objectPrototype : before.data.base.regexp.ambient.objects[ordinaryObjectPrototype]? = some root
  functionPrototype : before.data.base.regexp.ambient.objects[functionPrototype]? = some functionRoot
  closuresAllocated : ∀ closure ∈ before.closures, closure.objectReference < before.data.base.regexp.ambient.objects.length

/-- Independent creation result: the cache and exported callable occupy two
new ordinary objects, and two lexical const cells share their identities. No
global RegExp value is read or captured during this operation. -/
structure SetupContract (before after : Runtime) (functionPrototype : Nat) (handle : ArrowHandle) : Prop where
  handle : handle.index = before.closures.length
  cells : after.cells = before.cells ++
    [⟨.constant, some (.object before.data.base.regexp.ambient.objects.length)⟩,
     ⟨.constant, some (.object (before.data.base.regexp.ambient.objects.length + 1))⟩]
  environments : after.environments = before.environments ++
    [⟨[("patternCache", before.cells.length)], some before.current⟩,
     ⟨[("getPattern", before.cells.length + 1)], some before.environments.length⟩]
  current : after.current = before.environments.length + 1
  objects : after.data.base.regexp.ambient.objects = before.data.base.regexp.ambient.objects ++
    [emptyLiteralObject, arrowObject GetPatternBody.declaration functionPrototype]
  closures : after.closures = before.closures ++
    [⟨GetPatternBody.declaration, before.environments.length + 1, before.thisValue,
      before.data.base.regexp.ambient.objects.length + 1⟩]
  thisValue : after.thisValue = before.thisValue
  arrays : after.data.base.regexp.ambient.heap = before.data.base.regexp.ambient.heap
  exportCell : CellValue after after.current "getPattern" (.object (before.data.base.regexp.ambient.objects.length + 1))
  cacheCell : CellValue after after.current "patternCache" (.object before.data.base.regexp.ambient.objects.length)
  metadata : FunctionObjectContract (arrowObject GetPatternBody.declaration functionPrototype)

/-- Creation-to-first-call inputs are stated before either source operation.
The prototype path controls inherited cache reads of the freshly allocated {}. -/
structure InitialPlainInputs (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (input name : JSString) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop where
  setup : SetupInputs before functionPrototype root functionRoot
  arguments : Arguments arguments input next
  realm : LabelRealm before.data context.label
  label : LabelRegExp.Label input name none
  rootPath : NodeCaptureGuard.DescriptorPath before.data.base.regexp.ambient.objects
    (PatternCache.key input next) ordinaryObjectPrototype descriptor depth
  pathBound : depth + 1 ≤ propertyFuel
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  dataWritable : descriptor = none ∨ ∃ value enumerable configurable, descriptor = some (.data value true enumerable configurable)

structure InitialTerminalInputs (before : Runtime) (context : PatternCacheContext) (functionPrototype : Nat)
    (arguments : List Value) (name : JSString) (lower upper : UInt16) (next : Option JSString)
    (root functionRoot : OrdinaryObject) (descriptor : Option PropertyDescriptor) (depth constructorHandle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop where
  setup : SetupInputs before functionPrototype root functionRoot
  arguments : Arguments arguments (LabelMatch.safeRangeLabel name lower upper) next
  realm : LabelRealm before.data context.label
  validName : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  terminal : PatternCacheTerminal.TerminalNext next
  rootPath : NodeCaptureGuard.DescriptorPath before.data.base.regexp.ambient.objects
    (PatternCache.key (LabelMatch.safeRangeLabel name lower upper) next) ordinaryObjectPrototype descriptor depth
  pathBound : depth + 1 ≤ propertyFuel
  falsy : IteratorPureRead descriptor .undefined ∨ ∃ value writable enumerable configurable,
    descriptor = some (.data value writable enumerable configurable) ∧ SourceSubset.truthy value = false
  dataWritable : descriptor = none ∨ ∃ value enumerable configurable, descriptor = some (.data value true enumerable configurable)
  constructorCell : CellValue before before.current "RegExp" (.function constructorHandle)
  handleBound : context.label.iterators.constructors.constructors.base ≤ constructorHandle
  identity : context.label.iterators.constructors.constructors.entries[constructorHandle - context.label.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.data.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

theorem explicit_arguments (input : JSString) (next : Option JSString) (extra : List Value) :
    Arguments (.string input :: PatternCache.nextValue next :: extra) input next := by
  exact ⟨rfl, rfl⟩

theorem omitted_next (input : JSString) : Arguments [.string input] input none := by
  exact ⟨rfl, rfl⟩

theorem argument_ignores_extras (input : JSString) (next : Option JSString) (left right : List Value) :
    argument (.string input :: PatternCache.nextValue next :: left) 0 =
      argument (.string input :: PatternCache.nextValue next :: right) 0 ∧
    argument (.string input :: PatternCache.nextValue next :: left) 1 =
      argument (.string input :: PatternCache.nextValue next :: right) 1 := by
  exact ⟨rfl, rfl⟩

end HonoLean.Upstream.GetPatternInvocation
