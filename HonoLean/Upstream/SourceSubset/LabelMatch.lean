import HonoLean.Upstream.SourceSubset.LabelMatchSyntax
import HonoLean.Upstream.ECMA2025.LabelRegExp

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

structure LabelRegExpRecord where
  source : JSString
  flags : JSString
  compiled : LabelRegExp.Code
  deriving Repr
structure LabelCaptureView where
  index : Nat
  input : JSString
  deriving Repr, DecidableEq
inductive LabelEvent where
  | receiver (value : Value)
  | get (receiver : Value) (key : LabelPropertyKey) (holder : Nat) (value : Value)
  | getter (callee receiver : Value)
  | literalAllocated (reference : Nat)
  | initialized (reference : Nat) (source flags : JSString)
  | call (callee receiver : Value)
  | toString (value : Value)
  | lastIndex (value : Value) (length : Nat)
  | executed (reference : Nat)
  deriving Repr, DecidableEq

/-- Accessor slots refine current unsupported-accessor placeholders with a
closed intrinsic callable identity; they never cache getter results. The normal
realm is unchanged. Native accessor identity/replacement correspondence is an
explicit projection boundary, not inferred from a property spelling. -/
structure LabelMatchState where
  base : ArrayBindingState
  brands : List (Nat × LabelRegExpRecord) := []
  results : List (Nat × LabelCaptureView) := []
  symbols : List (Nat × List (LabelSymbol × PropertyDescriptor)) := []
  accessors : List LabelAccessorSlot := []
  trace : List LabelEvent := []
  deriving Repr
inductive LabelMatchError where
  | evaluation (error : EvalError)
  | object (error : ObjectError)
  | literalSyntax | methodDomain | getterDomain | coercion | brand | flagsDomain | representation | exhausted
  deriving Repr, DecidableEq

def labelBuiltinAt (table : LabelBuiltinTable) : Value → Option LabelBuiltin
  | .function handle => if table.base ≤ handle then table.entries[handle - table.base]? else none
  | _ => none

def labelTablesSeparated (context : LabelMatchContext) (before : State) : Bool :=
  let old := context.iterators.constructors
  let table := context.builtins
  let apart := fun (base length : Nat) => length == 0 || table.entries.isEmpty ||
    decide (table.base + table.entries.length ≤ base) || decide (base + length ≤ table.base)
  (table.entries.isEmpty || decide (before.functions.length ≤ table.base)) &&
    apart old.methods.base old.methods.entries.length && apart old.functions.base old.functions.entries.length &&
    apart old.members.base old.members.entries.length && apart old.builtins.base old.builtins.entries.length &&
    apart old.constructors.base old.constructors.entries.length && apart context.iterators.builtins.base context.iterators.builtins.entries.length

def labelOwn (before : LabelMatchState) (holder : Nat) (object : OrdinaryObject) : LabelPropertyKey → Option PropertyDescriptor
  | .string key => object.own.lookup key
  | .symbol key => (before.symbols.lookup holder).bind (fun fields => fields.lookup key)

def resolveLabelProperty : Nat → LabelMatchState → Nat → LabelPropertyKey → Except LabelMatchError (Option (Nat × PropertyDescriptor))
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, before, holder, key => do
    let object ← match before.base.regexp.ambient.objects[holder]? with
      | some object => .ok object | none => .error (.evaluation .invalidReference)
    match labelOwn before holder object key with
    | some descriptor => pure (some (holder, descriptor))
    | none => match object.prototype with
      | none => pure none
      | some parent => resolveLabelProperty fuel before parent key

def labelAccessorAt (before : LabelMatchState) (holder : Nat) (key : LabelPropertyKey) : Option Value :=
  (before.accessors.find? (fun slot => slot.holder == holder && slot.key == key)).map LabelAccessorSlot.callee

mutual
  def getLabelProperty : Nat → LabelMatchContext → Value → Nat → LabelPropertyKey → LabelMatchState →
      Except LabelMatchError (Value × LabelMatchState)
    | 0, _, _, _, _, _ => .error .exhausted
    | fuel + 1, context, receiver, reference, key, before => do
      let resolved ← resolveLabelProperty propertyFuel before reference key
      let (holder, value, after) ← match resolved with
        | none => pure (reference, .undefined, before)
        | some (holder, .data value _ _ _) => pure (holder, value, before)
        | some (holder, .accessor .missing _ _ _) => pure (holder, .undefined, before)
        | some (holder, .accessor .prototype _ _ _) => do
          let reference ← match receiver with | .object reference => .ok reference | _ => .error .getterDomain
          let value ← (callGetter .prototype before.base.regexp.ambient.objects reference).mapError .object
          pure (holder, value, before)
        | some (holder, .accessor .unsupported _ _ _) => do
          let callee ← match labelAccessorAt before holder key with | some callee => .ok callee | none => .error .getterDomain
          let (value, after) ← invokeLabelGetter fuel context callee receiver before
          pure (holder, value, after)
      pure (value, {after with trace := after.trace ++ [.get receiver key holder value]})
  def invokeLabelGetter : Nat → LabelMatchContext → Value → Value → LabelMatchState → Except LabelMatchError (Value × LabelMatchState)
    | 0, _, _, _, _ => .error .exhausted
    | fuel + 1, context, callee, receiver, before => do
      if !labelTablesSeparated context before.base.regexp.ambient then throw .representation else do
      let before := {before with trace := before.trace ++ [.getter callee receiver]}
      match labelBuiltinAt context.builtins callee with
      | some .flagsGetter =>
        let reference ← match receiver with | .object reference => .ok reference | _ => .error .getterDomain
        let (flags, after) ← getLabelFlags fuel context reference labelFlags before
        pure (.string flags, after)
      | some (.flagGetter flag) =>
        let reference ← match receiver with | .object reference => .ok reference | _ => .error .brand
        match before.brands.lookup reference with
        | some record => pure (.boolean (record.flags.contains (labelFlagUnit flag)), before)
        | none => match before.base.regexp.brands.lookup reference with
          | some record => pure (.boolean (record.originalFlags.contains (labelFlagUnit flag)), before)
          | none => if reference == context.regexpPrototype then pure (.undefined, before) else .error .brand
      | _ => .error .getterDomain
  def getLabelFlags : Nat → LabelMatchContext → Nat → List LabelFlag → LabelMatchState → Except LabelMatchError (JSString × LabelMatchState)
    | 0, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, [], before => .ok ([], before)
    | fuel + 1, context, reference, flag :: flags, before => do
      let (value, after) ← getLabelProperty fuel context (.object reference) reference (.string (labelFlagKey flag)) before
      let (rest, after) ← getLabelFlags fuel context reference flags after
      pure ((if truthy value then [labelFlagUnit flag] else []) ++ rest, after)
end

def initializeLabelRecord (literal : LabelRegExpLiteral) : Option LabelRegExpRecord := do
  if !literal.flags.isEmpty then none else
  let ast ← LabelRegExp.parseLiteral (47 :: literal.source ++ [47])
  if !labelStartAnchored ast then none else
  some ⟨literal.source, literal.flags, LabelRegExp.compile ast⟩

def labelLiteralAllocated (before : LabelMatchState) (prototype : Nat) : LabelMatchState :=
  {before with
    base := {before.base with regexp := {before.base.regexp with ambient := {before.base.regexp.ambient with
    objects := before.base.regexp.ambient.objects ++ [uninitializedRegExpObject prototype]}}}
    trace := before.trace ++ [.literalAllocated before.base.regexp.ambient.objects.length]}

def allocateLabelLiteral (context : LabelMatchContext) (literal : LabelRegExpLiteral) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  let _ ← match before.base.regexp.ambient.objects[context.regexpPrototype]? with
    | some object => .ok object | none => .error (.evaluation .invalidReference)
  let reference := before.base.regexp.ambient.objects.length
  let allocated := labelLiteralAllocated before context.regexpPrototype
  let record ← match initializeLabelRecord literal with | some record => .ok record | none => .error .literalSyntax
  let objects ← (setProperty propertyFuel allocated.base.regexp.ambient.objects reference lastIndexKey (.number 0)).mapError .object
  pure (.object reference, {allocated with
    base := {allocated.base with regexp := {allocated.base.regexp with ambient := {allocated.base.regexp.ambient with objects}}}
    brands := (reference, record) :: allocated.brands
    trace := allocated.trace ++ [.initialized reference literal.source literal.flags]})

def labelCaptureValue (input : JSString) : Option (Nat × Nat) → Value
  | none => .undefined
  | some (first, last) => .string ((input.drop first).take (last - first))
def labelMatchValues (input : JSString) (matched : LabelRegExp.Match) : List Value :=
  .string ((input.drop matched.start).take (matched.stop - matched.start)) :: matched.captures.map (labelCaptureValue input)

def invokeLabelExec (fuel : Nat) (context : LabelMatchContext) (receiver input : Value) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  let reference ← match receiver with | .object reference => .ok reference | _ => .error .brand
  let record ← match before.brands.lookup reference with | some record => .ok record | none => .error .brand
  -- RegExp builtin brand check precedes argument ToString.
  let text ← match input with | .string input => .ok input | _ => .error .coercion
  let before := {before with trace := before.trace ++ [.toString input]}
  let (lastIndex, after) ← getLabelProperty fuel context receiver reference (.string lastIndexKey) before
  let number ← match lastIndex with | .number number => .ok number | _ => .error .coercion
  let length ← (numericToLength (.number number)).mapError (fun _ => LabelMatchError.coercion)
  if !record.flags.isEmpty then throw .flagsDomain else do
  let after := {after with trace := after.trace ++ [.lastIndex lastIndex length, .executed reference]}
  -- Nonglobal local start=0 does not write the actual lastIndex descriptor.
  match LabelRegExp.execute record.compiled text with
  | .exhausted => .error .exhausted
  | .noMatch => pure (.null, after)
  | .matched matched =>
    let array := after.base.regexp.ambient.heap.length
    pure (.array array, {after with
      base := {after.base with regexp := {after.base.regexp with ambient := {after.base.regexp.ambient with
        heap := after.base.regexp.ambient.heap ++ [labelMatchValues text matched]}}}
      results := (array, ⟨matched.start, text⟩) :: after.results})

def invokeLabelRegExpMatch (fuel : Nat) (context : LabelMatchContext) (receiver input : Value) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  let reference ← match receiver with | .object reference => .ok reference | _ => .error .brand
  let text ← match input with | .string text => .ok text | _ => .error .coercion
  let before := {before with trace := before.trace ++ [.toString input]}
  let (flags, after) ← getLabelProperty fuel context receiver reference (.string labelFlagsKey) before
  let flagsText ← match flags with | .string flags => .ok flags | _ => .error .coercion
  let after := {after with trace := after.trace ++ [.toString flags]}
  if flagsText.contains 103 then throw .flagsDomain else do
  let (callee, after) ← getLabelProperty fuel context receiver reference (.string labelExecKey) after
  if builtinAt context.iterators.constructors.builtins callee != some .regexpExec then throw .methodDomain else do
  invokeLabelExec fuel context receiver (.string text) {after with trace := after.trace ++ [.call callee receiver]}

def invokeLabelStringMatch (fuel : Nat) (context : LabelMatchContext) (callee receiver argument : Value) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  if !labelTablesSeparated context before.base.regexp.ambient then throw .representation else do
  if labelBuiltinAt context.builtins callee != some .stringMatch then throw .methodDomain else do
  let reference ← match argument with | .object reference => .ok reference | _ => .error .methodDomain
  let before := {before with trace := before.trace ++ [.call callee receiver]}
  let (method, after) ← getLabelProperty fuel context argument reference (.symbol .match) before
  -- Existing @@match receives O unchanged. Its own ToString precedes flags Get.
  if labelBuiltinAt context.builtins method != some .regexpMatch then throw .methodDomain else do
  invokeLabelRegExpMatch fuel context argument receiver {after with trace := after.trace ++ [.call method argument]}

/-- Saved CURRENT String.match callee, then intrinsic regex-literal allocation,
then typed Symbol.match/flags/current exec dispatch. No exec-name primitive. -/
def runLabelMatch (fuel limit : Nat) (context : LabelMatchContext) (declaration : LabelMatchDecl) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  let (receiver, ambient) ← (evalExpression fuel limit declaration.receiver before.base.regexp.ambient).mapError .evaluation
  let before := {before with
    base := {before.base with regexp := {before.base.regexp with ambient}}
    trace := before.trace ++ [.receiver receiver]}
  let _ ← match receiver with | .string _ => .ok () | _ => .error .methodDomain
  let (callee, after) ← getLabelProperty fuel context receiver context.stringPrototype (.string (declaration.method.toList.map (fun c => UInt16.ofNat c.toNat))) before
  let (argument, after) ← allocateLabelLiteral context declaration.argument after
  invokeLabelStringMatch fuel context callee receiver argument after

def executeLabelMatch (fuel limit : Nat) (context : LabelMatchContext) (declaration : LabelMatchDecl) (before : LabelMatchState) :
    Except LabelMatchError LabelMatchState := do
  let (value, after) ← runLabelMatch fuel limit context declaration before
  pure {after with base := {after.base with regexp := {after.base.regexp with ambient := {after.base.regexp.ambient with
    environment := (declaration.name, value) :: after.base.regexp.ambient.environment}}}}

inductive LabelResultField where | zero | one | two | length | index | input | groups
  deriving Repr, DecidableEq
def observeLabelResult (state : LabelMatchState) (reference : Nat) (field : LabelResultField) : Option PropertyDescriptor := do
  let view ← state.results.lookup reference
  let values ← state.base.regexp.ambient.heap[reference]?
  match field with
  | .zero => values[0]?.map (fun value => .data value true true true)
  | .one => values[1]?.map (fun value => .data value true true true)
  | .two => values[2]?.map (fun value => .data value true true true)
  | .length => some (.data (.number values.length) true false false)
  | .index => some (.data (.number view.index) true true true)
  | .input => some (.data (.string view.input) true true true)
  | .groups => some (.data .undefined true true true)

end HonoLean.Upstream.SourceSubset
