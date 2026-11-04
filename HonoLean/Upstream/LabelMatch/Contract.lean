import HonoLean.Upstream.LabelMatch.Source
import HonoLean.Upstream.ECMA2025.DenseArray

set_option autoImplicit false
namespace HonoLean.Upstream.LabelMatch
open SourceSubset ECMA2025

structure Inputs (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) : Prop
    extends LabelRealm before context where
  labelBinding : before.base.regexp.ambient.environment.lookup "label" = some (.string input)

/-- Independent language output array, including OWN undefined for a missing
optional capture. It contains no parser, VM, method call or desired eval output. -/
def captures (input name : JSString) (body : Option JSString) : List Value :=
  [.string input, .string name, match body with | none => .undefined | some body => .string body]

def sourceEvents (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) : List LabelEvent :=
  [.receiver (.string input), .get (.string input) (.string labelMatchKey) context.stringPrototype (.function context.builtins.base),
    .literalAllocated before.base.regexp.ambient.objects.length,
    .initialized before.base.regexp.ambient.objects.length labelActualLiteral.source []] ++ labelStringMatchEvents before context input

def resultState (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) : LabelMatchState :=
  let after := labelEngineState before context input (before.trace ++ sourceEvents before context input)
  {after with base := {after.base with regexp := {after.base.regexp with ambient := {after.base.regexp.ambient with
    environment := ("match", labelEngineValue before input) :: before.base.regexp.ambient.environment}}}}

/-- Selected ECMA2025 normal-realm source producer. The projected accessor
identities/old realm are supplied; no native engine internaltrace/lexical-cell
adequacy or general regex/profile claim follows. In particular Node22 and Bun1.4
have a documented flags-protocol edition difference outside this normal realm. -/
structure Contract (before after : LabelMatchState) (context : LabelMatchContext) (input : JSString) : Prop where
  environment : ∃ returned, after.base.regexp.ambient.environment = ("match", returned) :: before.base.regexp.ambient.environment
  success : ∀ name body, LabelRegExp.Label input name body →
    after.base.regexp.ambient.environment = ("match", .array before.base.regexp.ambient.heap.length) :: before.base.regexp.ambient.environment ∧
    after.base.regexp.ambient.heap = before.base.regexp.ambient.heap ++ [captures input name body] ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .zero = some (.data (.string input) true true true) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .one = some (.data (.string name) true true true) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .two = some (.data (match body with | none => .undefined | some body => .string body) true true true) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .length = some (.data (.number 3) true false false) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .index = some (.data (.number 0) true true true) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .input = some (.data (.string input) true true true) ∧
    observeLabelResult after before.base.regexp.ambient.heap.length .groups = some (.data .undefined true true true)
  failure : (¬ ∃ name body, LabelRegExp.Label input name body) →
    after.base.regexp.ambient.environment = ("match", .null) :: before.base.regexp.ambient.environment ∧ after.base.regexp.ambient.heap = before.base.regexp.ambient.heap ∧ after.results = before.results
  objects : after.base.regexp.ambient.objects = before.base.regexp.ambient.objects ++ [initializedRegExpObject context.regexpPrototype]
  internal : after.brands.lookup before.base.regexp.ambient.objects.length = some labelLiteralRecord
  oldObjects : ∀ reference, reference < before.base.regexp.ambient.objects.length → after.base.regexp.ambient.objects[reference]? = before.base.regexp.ambient.objects[reference]?
  oldLabelBrands : ∀ reference, reference ≠ before.base.regexp.ambient.objects.length → after.brands.lookup reference = before.brands.lookup reference
  oldLabelResults : ∀ reference, reference ≠ before.base.regexp.ambient.heap.length → after.results.lookup reference = before.results.lookup reference
  oldArrays : ∀ reference, reference < before.base.regexp.ambient.heap.length → after.base.regexp.ambient.heap[reference]? = before.base.regexp.ambient.heap[reference]?
  functions : after.base.regexp.ambient.functions = before.base.regexp.ambient.functions
  privates : after.base.regexp.ambient.privates = before.base.regexp.ambient.privates
  sets : after.base.regexp.ambient.sets = before.base.regexp.ambient.sets
  thisValue : after.base.regexp.ambient.thisValue = before.base.regexp.ambient.thisValue
  rangeBrands : after.base.regexp.brands = before.base.regexp.brands
  rangeResults : after.base.regexp.results = before.base.regexp.results
  iteratorSymbols : after.base.symbols = before.base.symbols
  iterators : after.base.iterators = before.base.iterators
  iteratorTrace : after.base.trace = before.base.trace
  symbols : after.symbols = before.symbols
  accessors : after.accessors = before.accessors
  orderedProtocol : after.trace = before.trace ++ sourceEvents before context input

end HonoLean.Upstream.LabelMatch
