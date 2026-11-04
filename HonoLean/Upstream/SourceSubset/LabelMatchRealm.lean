import HonoLean.Upstream.SourceSubset.LabelMatch

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

def labelFlagIndex : LabelFlag → Nat
  | .hasIndices => 0 | .global => 1 | .ignoreCase => 2 | .multiline => 3
  | .dotAll => 4 | .unicode => 5 | .unicodeSets => 6 | .sticky => 7

def standardLabelBuiltins : List LabelBuiltin :=
  [.stringMatch, .regexpMatch, .flagsGetter,
   .flagGetter .hasIndices, .flagGetter .global, .flagGetter .ignoreCase, .flagGetter .multiline,
   .flagGetter .dotAll, .flagGetter .unicode, .flagGetter .unicodeSets, .flagGetter .sticky]

def standardLabelRegExpOwn (_base execHandle : Nat) : List (JSString × PropertyDescriptor) :=
  [(labelExecKey, .data (.function execHandle) true false true),
   (labelFlagsKey, .accessor .unsupported .missing false true)] ++
  labelFlags.map (fun flag => (labelFlagKey flag, .accessor .unsupported .missing false true))

def standardLabelAccessors (holder base : Nat) : List LabelAccessorSlot :=
  ⟨holder, .string labelFlagsKey, .function (base + 2)⟩ ::
    labelFlags.map (fun flag => ⟨holder, .string (labelFlagKey flag), .function (base + 3 + labelFlagIndex flag)⟩)

/-- BEFORE source60: allocated OLD realm cells and current projected accessor
identities. Standard getter outputs are not premises: every bit is read from
current properties and internal OriginalFlags. Native identity coherence of the
placeholder/sidecar representation is deliberately an interpretation boundary. -/
structure LabelRealm (before : LabelMatchState) (context : LabelMatchContext) : Prop where
  builtinEntries : context.builtins.entries = standardLabelBuiltins
  regexpIdentity : context.iterators.constructors.builtins.entries[0]? = some .regexpExec
  noArgBefore : before.base.regexp.ambient.functions.length ≤ context.builtins.base
  methodsBefore : context.iterators.constructors.methods.base + context.iterators.constructors.methods.entries.length ≤ context.builtins.base
  functionsBefore : context.iterators.constructors.functions.base + context.iterators.constructors.functions.entries.length ≤ context.builtins.base
  membersBefore : context.iterators.constructors.members.base + context.iterators.constructors.members.entries.length ≤ context.builtins.base
  regexpBefore : context.iterators.constructors.builtins.base + context.iterators.constructors.builtins.entries.length ≤ context.builtins.base
  constructorsBefore : context.iterators.constructors.constructors.base + context.iterators.constructors.constructors.entries.length ≤ context.builtins.base
  iteratorsBefore : context.iterators.builtins.base + context.iterators.builtins.entries.length ≤ context.builtins.base
  stringFound : ∃ object, before.base.regexp.ambient.objects[context.stringPrototype]? = some object ∧
    object.own.lookup labelMatchKey = some (.data (.function context.builtins.base) true false true)
  regexpFound : ∃ object, before.base.regexp.ambient.objects[context.regexpPrototype]? = some object ∧
    object.own = standardLabelRegExpOwn context.builtins.base context.iterators.constructors.builtins.base
  symbol : (before.symbols.lookup context.regexpPrototype).bind (fun fields => fields.lookup .match) =
    some (.data (.function (context.builtins.base + 1)) true false true)
  accessors : before.accessors = standardLabelAccessors context.regexpPrototype context.builtins.base
  symbolOwners : ∀ entry ∈ before.symbols, entry.1 < before.base.regexp.ambient.objects.length
  oldNoArg : before.base.regexp.ambient.functions.length ≤ context.iterators.constructors.methods.base
  oldMethods : context.iterators.constructors.methods.base + context.iterators.constructors.methods.entries.length ≤ context.iterators.constructors.functions.base
  oldFunctions : context.iterators.constructors.functions.base + context.iterators.constructors.functions.entries.length ≤ context.iterators.constructors.members.base
  oldMembers : context.iterators.constructors.members.base + context.iterators.constructors.members.entries.length ≤ context.iterators.constructors.builtins.base
  oldRegExp : context.iterators.constructors.builtins.base + context.iterators.constructors.builtins.entries.length ≤ context.iterators.constructors.constructors.base
  oldConstructors : context.iterators.constructors.constructors.base + context.iterators.constructors.constructors.entries.length ≤ context.iterators.builtins.base

theorem labelRealm_trace (before : LabelMatchState) (context : LabelMatchContext) (events : List LabelEvent)
    (realm : LabelRealm before context) : LabelRealm {before with trace := events} context := by
  cases realm
  constructor <;> assumption

def labelStandardOldContext : RegExpConstructContext :=
  ⟨⟨1, [⟨⟨"old", [], .named "void", []⟩, [], []⟩]⟩,
   ⟨2, [⟨⟨"old", "input", []⟩, [], []⟩]⟩,
   ⟨3, [⟨⟨"echo", "input", [.ret (.variable "input")]⟩, [], []⟩,
        ⟨⟨"other", "input", [.ret .null]⟩, [], []⟩]⟩,
   ⟨5, [.regexpExec]⟩, ⟨6, [⟨2⟩]⟩⟩
def labelStandardContext : LabelMatchContext :=
  ⟨⟨labelStandardOldContext, ⟨7, [.arrayValues, .arrayNext]⟩, 3, 4, 0⟩,
    ⟨9, standardLabelBuiltins⟩, 1, 2⟩
def labelPrior : JSString := [112,114,105,111,114]
def labelStandardAmbient (input : JSString) : State :=
  {
      environment := [("label", .string input), ("match", .array 0), ("RegExp", .number 17)]
      heap := [[.string labelPrior]]
      objects := [objectPrototypeProjection,
        ⟨[(labelMatchKey, .data (.function 9) true false true)], some 0, true⟩,
        ⟨standardLabelRegExpOwn 9 5, some 0, true⟩,
        ⟨[], some 0, true⟩,
        ⟨[(iteratorNextKey, .data (.function 8) true false true)], some 0, true⟩,
        ⟨[([99,97,110,97,114,121], .data (.number 23) false false false)], none, false⟩,
        ⟨[(lastIndexKey, .data (.number 17) false false false)], some 2, false⟩]
      functions := [⟨⟨"old", .number 0⟩, []⟩]
      thisValue := .object 5
      privates := .ofData [("old", 19)] [(5, [(19, .number 17)])]
      sets := [[labelPrior]]}

def labelStandardState (input : JSString) : LabelMatchState :=
  { base := {regexp := ⟨labelStandardAmbient input, [(6, digitsRecord)], [(0, ⟨0, labelPrior⟩)]⟩}
    symbols := [(2, [(.match, .data (.function 10) true false true)])]
    accessors := standardLabelAccessors 2 9}

end HonoLean.Upstream.SourceSubset
