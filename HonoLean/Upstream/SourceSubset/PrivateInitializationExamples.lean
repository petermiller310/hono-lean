import HonoLean.Upstream.SourceSubset.PrivateInitialization

namespace HonoLean.Upstream.SourceSubset

open ECMA2025
set_option maxRecDepth 32768

example : parsePrivateFields "#cache: Record<string, Box<T>>[] = []\n#unset?: Pattern | string\n" [] =
    some [⟨"cache", false, some (.array (.application (.named "Record")
      [.named "string", .application (.named "Box") [.named "T"]])), some (.arrayLiteral [])⟩,
      ⟨"unset", true, some (.union (.named "Pattern") (.named "string")), none⟩] := by cbv

example : parsePrivateFields "#name = shared; #optional?; #same: T | U[];" ["shared"] =
    some [⟨"name", false, none, some (.variable "shared")⟩, ⟨"optional", true, none, none⟩,
      ⟨"same", false, some (.union (.named "T") (.array (.named "U"))), none⟩] := by cbv

example : parseBlock "let order = 0\nlet named: T | U = order\n" [] =
    some [.mutableDeclare "order" none (.number 0),
      .mutableDeclare "named" (some (.union (.named "T") (.named "U"))) (.variable "order")] := by cbv

example : parsePrivateFields "#same = []; #same = []" [] = none := by cbv
example : parsePrivateFields "#constructor = []" [] = none := by cbv
example : parsePrivateFields "publicName = []" [] = none := by cbv
example : parsePrivateFields "static #name = []" [] = none := by cbv
example : parsePrivateFields "#name() {}" [] = none := by cbv
example : parsePrivateFields "get #name() {}" [] = none := by cbv
example : parsePrivateFields "#name!: T" [] = none := by cbv
example : parsePrivateFields "#name?!: T" [] = none := by cbv
example : parsePrivateFields "#name = this" [] = none := by cbv
example : parsePrivateFields "#name = super" [] = none := by cbv
example : parsePrivateFields "#name = other.#name" ["other"] = none := by cbv
example : parsePrivateFields "#name = ++order" ["order"] = none := by cbv
example : parsePrivateFields "#name = [] #other = []" [] = none := by cbv
example : parsePrivateFields "#name: (T | U)[] = []" [] = none := by cbv
example : parseExpression "a | b" ["a", "b"] = none := by cbv

private def fields : List PrivateField :=
  [⟨"items", false, some (.array (.named "T")), some (.arrayLiteral [])⟩,
   ⟨"shared", false, none, some (.variable "shared")⟩,
   ⟨"unset", true, some (.named "T"), none⟩]
private def before : State :=
  {environment := [("shared", .object 0), ("caller", .number 7)]
   objects := [emptyNullObject]
   privates := PrivateStore.ofData ([("old", 12)]) ([(0, [(31, .number 9)])])}
private def firstClass : DataClass := ⟨fields, 32, before.environment⟩
private def nextClass : DataClass := ⟨fields, 35, before.environment⟩

-- Reserve two definitions before either has an instance. Active names alone
-- cannot account for the first definition's reserved identities.
example : defineDataClass fields before (initialPrivateWorld before) =
    some (firstClass, ⟨35⟩) := by cbv
example : defineDataClass fields before ⟨35⟩ = some (nextClass, ⟨38⟩) := by cbv
example : firstClass.names = [("items", 32), ("shared", 33), ("unset", 34)] := by cbv
example : nextClass.names = [("items", 35), ("shared", 36), ("unset", 37)] := by cbv

private def instanceObservations : Except EvalError (List (List Value) × List Value × List Value × Bool × Bool) := do
  let (first, one) ← instantiateDataClass 32 defaultSplitLimit firstClass (some 0) before
  let (second, two) ← instantiateDataClass 32 defaultSplitLimit firstClass (some 0) one
  let lexical := {two with privates := {two.privates with names := firstClass.names}}
  let a ← privateGet (.object first) "items" lexical
  let b ← privateGet (.object second) "items" lexical
  let sharedA ← privateGet (.object first) "shared" lexical
  let sharedB ← privateGet (.object second) "shared" lexical
  let unsetA ← privateGet (.object first) "unset" lexical
  let unsetB ← privateGet (.object second) "unset" lexical
  pure (two.heap, [a, b], [sharedA, sharedB, unsetA, unsetB],
    decide (two.environment = before.environment), decide (two.privates.names = before.privates.names))

example : instanceObservations = .ok ([[], []], [.array 0, .array 1],
    [.object 0, .object 0, .undefined, .undefined], true, true) := by cbv

-- Private addition does not consult ordinary extensibility or setters.
example : privateAdd {objects := [{extensible := false}]} 0 3 .null =
    .ok (addedPrivateState {objects := [{extensible := false}]} 0 3 .null []) := by cbv

-- A dangling old private slot at the next object reference is rejected.
example : beginInstance firstClass none {before with privates := PrivateStore.ofData ([]) ([(1, [])])} =
    .error .privateBrand := by cbv

-- On an already branded receiver, evaluate before checking duplicate addition.
-- The failing initializer takes precedence; errors carry no partial state.
example : initializeField 32 defaultSplitLimit
    ⟨"old", false, none, some (.variable "missing")⟩ 0
      {before with privates := PrivateStore.ofData ([("old", 31)]) (before.privates.slots)} = .error .missingVariable := by cbv
example : initializeField 32 defaultSplitLimit
    ⟨"old", false, none, none⟩ 0 {before with privates := PrivateStore.ofData ([("old", 31)]) (before.privates.slots)} =
      .error .privateBrand := by cbv

private def partialState : State :=
  {objects := [emptyNullObject], privates := PrivateStore.ofData ([("first", 1), ("later", 2)]) ([(0, [])])}
private def firstField : PrivateField := ⟨"first", false, none, some (.number 7)⟩
private def firstAdded : State := addedPrivateState partialState 0 1 (.number 7) []

example : initializeField 32 defaultSplitLimit firstField 0 partialState = .ok firstAdded := by cbv
example : privateGet (.object 0) "first" firstAdded = .ok (.number 7) := by cbv
example : privateGet (.object 0) "later" firstAdded = .error .privateBrand := by cbv
example : initializeField 32 defaultSplitLimit ⟨"later", true, none, none⟩ 0 firstAdded =
    .ok (addedPrivateState firstAdded 0 2 .undefined [(1, .data (.number 7))]) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.initialPrivateWorld_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initialPrivateWorld_fresh

end HonoLean.Upstream.SourceSubset
