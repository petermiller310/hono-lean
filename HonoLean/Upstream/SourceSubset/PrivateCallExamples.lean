import HonoLean.Upstream.SourceSubset.PrivateCall

namespace HonoLean.Upstream.SourceSubset.PrivateCallChecks

open ECMA2025

private def stringType : TypeSyntax := .named "string"
private def program : PrivateMethod :=
  ⟨"f", [⟨"x", false, stringType⟩, ⟨"y", true, .named "number"⟩], .named "void",
    [.ret (.variable "x")]⟩
private def closure : PrivateMethodClosure :=
  ⟨program, [("x", .number 99), ("captured", .number 7)], [("capturedBrand", 42)]⟩
private def table : PrivateMethodTable := ⟨1, [closure]⟩
private def before : State :=
  {environment := [("counter", .number 0), ("callee", .object 1), ("bad", .object 9)],
   objects := [objectPrototypeProjection [], {}],
   functions := [⟨⟨"helper", .number 8⟩, []⟩],
   privates := PrivateStore.ofData ([("f", 10)]) ([(1, [(10, .function 1)])])}
private def call (arguments : List Expr) : PrivateMethodCall := ⟨.this, "f", arguments⟩
private def changedCounter : State := {before with environment := [("counter", .number 3), ("callee", .object 1), ("bad", .object 9)]}

example : parsePrivateMethod "#f(x: string, y?: number): void { return x }" [] [] = some program := by cbv
example : (parsePrivateMethod "#f(x: string, y?: number): void { return x }" [] []).isSome = true := by cbv
example : (parsePrivateMethod "#f(x?: string, y: number): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(x: string, x: string): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(x: string = 1): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(...x: string[]): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(): void { return this }" [] []).isSome = true := by cbv
example : (parsePrivateMethod "#constructor(): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "async #f(): void {}" [] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(): void { ++captured }" ["captured"] []).isNone = true := by cbv
example : (parsePrivateMethod "#f(captured: number): void { ++captured }" ["captured"] []).isSome = true := by cbv
example : (parsePrivateMethod "#f(): void { for (let i = 0; i < 2; i++) {} }" [] []).isSome = true := by cbv
example : (parsePrivateMethod "#f(): void { for (let i = 0; i < 2; i++) {} }" ["i"] []).isNone = true := by cbv

example : parsePrivateMethodCall "this.#f(++counter, ++counter, ++counter)" ["counter"] ["f"] =
    some (call [.preIncrement "counter", .preIncrement "counter", .preIncrement "counter"]) := by cbv
example : (parseExpression "this.#f()" [] ["f"]).isNone = true := by cbv
example : (parsePrivateMethodCall "this.#f(this)" [] ["f"]).isNone = true := by cbv
example : (parsePrivateMethodCall "this.f()" [] ["f"]).isNone = true := by cbv
example : (parsePrivateMethodCall "this.#f()" [] []).isNone = true := by cbv

-- All extras run left to right before binding/discard. Formal x receives1,
-- y receives2, the third effect persists in the restored caller environment.
theorem extras_evaluated_and_formals_shadow :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.object 1⟩
      (call [.preIncrement "counter", .preIncrement "counter", .preIncrement "counter"]) before =
      .ok (.number 1, changedCounter) := by cbv

-- Optionality and declared string/void types do not impose runtime validation.
theorem missing_required_is_undefined :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.object 1⟩ (call []) before =
      .ok (.undefined, before) := by cbv

theorem explicit_return_ignores_void_metadata :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.object 1⟩ (call [.number 12]) before =
      .ok (.number 12, before) := by cbv

-- A bad brand wins before the invalid argument dereference. A noncallable
-- private value is rejected only after that argument's error.
theorem private_get_precedes_arguments :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.object 0⟩
      (call [.property (.variable "bad") []]) before = .error .privateBrand := by cbv

theorem arguments_precede_callable_check :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.object 1⟩
      (call [.property (.variable "bad") []])
      {before with privates := PrivateStore.ofData ([("f", 10)]) ([(1, [(10, .number 0)])])} =
        .error (.objectError .invalidReference) := by cbv

theorem existing_function_ids_cannot_alias :
    runPrivateMethodCall 32 defaultSplitLimit ⟨0, [closure]⟩ ⟨.object 1⟩ (call []) before =
      .error .unsupported := by cbv

-- A strict method receives the exact dynamic receiver separately from the
-- value environment; caller-scope guesses cannot supply its captured brand.
example : (methodActivation closure .null [] before).thisValue = .null := rfl
example : (methodActivation closure (.object 1) [] before).state.privates.names = [("capturedBrand", 42)] := rfl
example : (methodActivation closure (.object 1) [] before).state.environment.lookup "captured" = some (.number 7) := by cbv

private def secretClosure : PrivateMethodClosure :=
  ⟨⟨"f", [], .named "void", [.ret (.privateProperty (.variable "target") "secret")]⟩,
    [("target", .object 2)], [("secret", 42)]⟩
private def secretState : State :=
  {before with
    objects := before.objects ++ [{}]
    privates := PrivateStore.ofData ([("f", 10), ("secret", 11)]) ([(1, [(10, .function 1)]), (2, [(42, .number 9), (11, .number 99)])])}

theorem closure_private_context_and_caller_restoration :
    runPrivateMethodCall 32 defaultSplitLimit ⟨1, [secretClosure]⟩ ⟨.object 1⟩ (call []) secretState =
      .ok (.number 9, secretState) := by cbv

private def heapClosure : PrivateMethodClosure :=
  {closure with
    program := {program with body := [.evaluate (.call (.variable "out") "push" [.variable "x"])]}
    environment := [("out", .array 0)]}
private def heapState : State := {before with heap := [[]]}

theorem normal_completion_keeps_heap_effects :
    runPrivateMethodCall 32 defaultSplitLimit ⟨1, [heapClosure]⟩ ⟨.object 1⟩
      (call [.number 5]) heapState = .ok (.undefined, {heapState with heap := [[.number 5]]}) := by cbv

private def movingReceiver : State :=
  {before with
    environment := ("values", .array 0) :: before.environment
    heap := [[.object 1, .number 7]]}

theorem receiver_effects_precede_argument_effects :
    runPrivateMethodCall 32 defaultSplitLimit table ⟨.undefined⟩
      ⟨.expression (.call (.variable "values") "shift" []), "f", [.call (.variable "values") "shift" []]⟩
      movingReceiver = .ok (.number 7, {movingReceiver with heap := [[]]}) := by cbv

end HonoLean.Upstream.SourceSubset.PrivateCallChecks
