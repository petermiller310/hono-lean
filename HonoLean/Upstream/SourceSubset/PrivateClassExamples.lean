import HonoLean.Upstream.SourceSubset.PrivateClass

namespace HonoLean.Upstream.SourceSubset.PrivateClassChecks

open ECMA2025
set_option maxRecDepth 32768

private def method : PrivateMethod :=
  ⟨"run", [⟨"value", false, .named "string"⟩], .named "void", [.ret (.variable "value")]⟩

private def fields : List PrivateField :=
  [⟨"items", false, none, some (.arrayLiteral [])⟩,
   ⟨"shared", false, none, some (.variable "shared")⟩,
   ⟨"unset", true, some (.named "T"), none⟩]

private def before : State :=
  {environment := [("shared", .object 0), ("caller", .number 7)]
   objects := [emptyNullObject]
   functions := [⟨⟨"prior", .number 5⟩, []⟩]
   privates := PrivateStore.ofData ([("old", 12)]) ([(0, [(31, .number 9)])])}

private def emptyTable : PrivateMethodTable := ⟨1, []⟩
private def firstClass : SelectedPrivateClass := ⟨fields, [method], 32, before.environment, 1⟩
private def firstTable : PrivateMethodTable := ⟨1, firstClass.closures⟩
private def secondClass : SelectedPrivateClass := ⟨fields, [method], 36, before.environment, 2⟩
private def secondTable : PrivateMethodTable := ⟨1, firstClass.closures ++ secondClass.closures⟩

example : parsePrivateMethod "#run(value: string): void { return value }" [] [] = some method := by cbv

/-- Both definitions reserve identities and function handles before any instance
exists. The second table retains the first closure at its original handle. -/
theorem definitions_without_instances :
    definePrivateClass fields [method] before (initialPrivateWorld before) emptyTable =
      some (firstClass, ⟨36⟩, firstTable) ∧
    definePrivateClass fields [method] before ⟨36⟩ firstTable =
      some (secondClass, ⟨40⟩, secondTable) ∧
    firstClass.names = [("items", 32), ("shared", 33), ("unset", 34), ("run", 35)] ∧
    secondClass.names = [("items", 36), ("shared", 37), ("unset", 38), ("run", 39)] ∧
    firstClass.firstHandle = 1 ∧ secondClass.firstHandle = 2 ∧
    (resolvePrivateMethod secondTable (.function 1)).map PrivateMethodClosure.privateNames = .ok firstClass.names := by cbv

/-- The joint seed sees names held only by old method closures, including a
definition that has not created any instance. It also retains old State IDs. -/
theorem seed_includes_retained_closure_names :
    initialPrivateClassWorld before firstTable = ⟨36⟩ ∧
    initialPrivateClassWorld before ⟨1, [⟨method, [], [("uninstantiated", 1000)]⟩]⟩ = ⟨1001⟩ ∧
    initialPrivateClassWorld before emptyTable = initialPrivateWorld before := by cbv

example : definePrivateClass fields [⟨"items", [], .named "void", []⟩] before ⟨32⟩ emptyTable = none := by cbv
example : definePrivateClass fields [method, method] before ⟨32⟩ emptyTable = none := by cbv
example : definePrivateClass [⟨"constructor", false, none, none⟩] [method] before ⟨32⟩ emptyTable = none := by cbv
example : definePrivateClass fields [method] before ⟨32⟩ ⟨0, []⟩ = none := by cbv

private def beforeFields : Except EvalError State := do
  let (owner, started) ← beginPrivateClassInstance firstClass (some 0) before
  installPrivateMethodBindings firstClass.methodBindings owner started

/-- The method is available while every data field is still absent. This
observes the explicit pre-field stage, not unsupported field-body this syntax. -/
theorem method_installed_before_data :
    (beforeFields.bind fun state => privateGet (.object 1) "run" state) = .ok (.function 1) ∧
    (beforeFields.bind fun state => privateGet (.object 1) "items" state) = .error .privateBrand ∧
    (beforeFields.map fun state => state.heap) = .ok [] := by cbv

private def observations : Except EvalError (List (List Value) × List Value × List Value × Bool × Bool × Bool) := do
  let (first, one) ← instantiatePrivateClass 32 defaultSplitLimit firstClass (some 0) before
  let (second, two) ← instantiatePrivateClass 32 defaultSplitLimit firstClass (some 0) one
  let lexical := {two with privates := {two.privates with names := firstClass.names}}
  let methodA ← privateGet (.object first) "run" lexical
  let methodB ← privateGet (.object second) "run" lexical
  let arrayA ← privateGet (.object first) "items" lexical
  let arrayB ← privateGet (.object second) "items" lexical
  let sharedA ← privateGet (.object first) "shared" lexical
  let sharedB ← privateGet (.object second) "shared" lexical
  let foreign := privateGet (.object first) "run" {two with privates := {two.privates with names := secondClass.names}}
  pure (two.heap, [methodA, methodB, arrayA, arrayB], [sharedA, sharedB],
    decide (two.environment = before.environment), decide (two.privates.names = before.privates.names),
    match foreign with | .error .privateBrand => true | _ => false)

theorem shared_method_and_isolated_fields :
    observations = .ok ([[], []], [.function 1, .function 1, .array 0, .array 1],
      [.object 0, .object 0], true, true, true) := by cbv

private def called : Except EvalError (Value × State) := do
  let (owner, state) ← instantiatePrivateClass 32 defaultSplitLimit firstClass (some 0) before
  let caller := {state with privates := {state.privates with names := firstClass.names}}
  runPrivateMethodCall 32 defaultSplitLimit firstTable ⟨.object owner⟩
    ⟨.this, "run", [.number 17]⟩ caller

theorem derived_method_handle_calls_source_body :
    (called.map Prod.fst) = .ok (.number 17) ∧
    (called.map fun (_, state) => state.environment) = .ok before.environment := by cbv

-- Method addition rejects duplicates before the later field stage can fail.
-- The missing-variable error would win if the field initializer ran first.
private def methodOwner : State :=
  {objects := [emptyNullObject], environment := [],
   privates := PrivateStore.ofData ([("run", 3), ("field", 4)]) ([(0, [(3, .function 0)])])}

private def duplicateBeforeField : Except EvalError State := do
  let state ← installPrivateMethodBindings [(3, .function 0)] 0 methodOwner
  initializeFields 32 defaultSplitLimit [⟨"field", false, none, some (.variable "missing")⟩] 0 state

theorem duplicate_method_precedes_field_error : duplicateBeforeField = .error .privateBrand := by cbv

example : beginPrivateClassInstance firstClass none
    {before with privates := PrivateStore.ofData ([]) ([(1, [])])} = .error .privateBrand := by cbv

example : installPrivateMethodBindings [(3, .function 0)] 0 {objects := [{extensible := false}]} =
    .ok (addedPrivateElementState {objects := [{extensible := false}]} 0 3 (.method (.function 0)) []) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.successive_private_classes_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successive_private_classes_disjoint

/-- info: 'HonoLean.Upstream.SourceSubset.successive_method_handles_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms successive_method_handles_disjoint

end HonoLean.Upstream.SourceSubset.PrivateClassChecks
