import HonoLean.Upstream.CreateNullObject.Correctness

namespace HonoLean.Upstream.CreateNullObject

open SourceSubset

set_option maxRecDepth 32768

private def seed : State :=
  {environment := [("keep", .string [107])], heap := [[.number 1]],
   objects := [ECMA2025.emptyNullObject]}

example : runNoArg createProgram seed =
    .ok (.object 1, {seed with objects := [ECMA2025.emptyNullObject, ECMA2025.emptyNullObject]}) := by cbv

example : (parseNoArg pinnedSource).map (fun program => runNoArg program {}) =
    some (.ok (.object 0, {objects := [ECMA2025.emptyNullObject]})) := by cbv

private def twice (state : State) : Except EvalError ((Value × Value) × State) := do
  let (first, next) ← runNoArg createProgram state
  let (second, final) ← runNoArg createProgram next
  return ((first, second), final)

-- Equal contents do not collapse object identities across calls.
example : twice {} =
    .ok ((.object 0, .object 1), {objects := [ECMA2025.emptyNullObject, ECMA2025.emptyNullObject]}) := by cbv

-- Lexical shadowing is respected and excludes the standard-builtin premise.
example : runNoArg createProgram {environment := [("Object", .string [])]} =
    .error .unsupported := by cbv
example : ¬ StandardObjectBinding {environment := [("Object", .string [])]} := by
  simp [StandardObjectBinding]
example : runNoArg createProgram {environment := [("Object", .objectConstructor)]} =
    .ok (.object 0, {environment := [("Object", .objectConstructor)], objects := [ECMA2025.emptyNullObject]}) := by cbv

def rejectedSources : List String := [
  "export const createNullObject = (x) => Object.create(null)",
  "export const Object = () => Object.create(null)",
  "export const createNullObject = () => Object.create(null) evil()",
  "export const createNullObject = () => Object.create(null)\n*1",
  "export const createNullObject = () => Object.create(null, null)",
  "export const createNullObject = () => Object.create(unbound)",
  "export const createNullObject = () => { return Object.create(null) }",
  "export const createNullObject = () => /* comment */ Object.create(null)"]

example : rejectedSources.all (fun source => (parseNoArg source).isNone) = true := by cbv

-- A newline can continue the new subtraction expression. The complete source
-- parses; the numeric-only model rejects its object operand at execution.
def newlineSubtractionSource : String :=
  "export const createNullObject = () => Object.create(null)\n-1"

example : (parseNoArg newlineSubtractionSource).isSome = true := by cbv
example : (parseNoArg newlineSubtractionSource).map (fun program => runNoArg program {}) =
    some (.error .unsupported) := by cbv

-- General expression parsing: names and bodies can vary, and the conditional
-- uses the existing precedence and lazy execution, rather than a fixed snippet.
def conditionalSource : String :=
  "export const otherName = () => null === null ? Object.create(null) : Object.create('bad')"

example : (parseNoArg conditionalSource).map (fun program => runNoArg program {}) =
    some (.ok (.object 0, {objects := [ECMA2025.emptyNullObject]})) := by cbv

def returnNullSource : String := "export const createNullObject = () => null"
def returnBuiltinSource : String := "export const createNullObject = () => Object"

def SourceHasContract (source : String) : Prop :=
  ∀ before, StandardObjectBinding before → ∀ value after,
    (parseNoArg source).map (fun program => runNoArg program before) =
      some (.ok (value, after)) ↔ NullObjectContract before value after

theorem returnNullSource_not_correct : ¬ SourceHasContract returnNullSource := by
  intro claimed
  have actual : (parseNoArg returnNullSource).map (fun program => runNoArg program {}) =
      some (.ok (.null, {})) := by cbv
  have standard : StandardObjectBinding {} := by exact Or.inl rfl
  have invalid : ¬ NullObjectContract {} .null {} := by
    rw [contract_iff]
    simp
  exact invalid ((claimed {} standard .null {}).mp actual)

theorem returnBuiltinSource_not_correct : ¬ SourceHasContract returnBuiltinSource := by
  intro claimed
  have actual : (parseNoArg returnBuiltinSource).map (fun program => runNoArg program {}) =
      some (.ok (.objectConstructor, {})) := by cbv
  have standard : StandardObjectBinding {} := by exact Or.inl rfl
  have invalid : ¬ NullObjectContract {} .objectConstructor {} := by
    rw [contract_iff]
    simp
  exact invalid ((claimed {} standard .objectConstructor {}).mp actual)

end HonoLean.Upstream.CreateNullObject
