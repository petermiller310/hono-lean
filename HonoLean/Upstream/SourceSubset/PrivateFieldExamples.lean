import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.PrivateChecks

open ECMA2025

set_option maxRecDepth 65536

private def publicKey : JSString := [35,109,101,116,104,111,100,115]
private def pushKey : JSString := [112,117,115,104]
private def scoreKey : JSString := [115,99,111,114,101]

private def initial : State :=
  {environment := [("curNode", .object 1), ("order", .number 0)],
   heap := [[]], objects := [objectPrototypeProjection [], emptyLiteralObject],
   privates := PrivateStore.ofData [("methods", 17)] [(1, [(17, .array 0)])]}

example : parseExpression "curNode.#methods" ["curNode"] = none := by cbv
example : parseExpression "curNode.#methods" ["curNode"] ["other"] = none := by cbv
example : parseExpression "curNode.#methods" ["curNode"] ["methods"] =
    some (.privateProperty (.variable "curNode") "methods") := by cbv
example : (parseExpression "curNode.# methods" ["curNode"] ["methods"]).isNone = true := by cbv
example : (parseAssignment "curNode.#methods = 1" ["curNode"] ["methods"]).isSome = true := by cbv
example : (parseNoArg "export const f = () => Object.#methods").isNone = true := by cbv

-- The private array is read before the object argument; the actual resulting
-- outer record reference is appended exactly once, with score's env effect.
example : (parseExpression "curNode.#methods.push({score: ++order})" ["curNode", "order"] ["methods"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression initial) =
      some (.ok (.number 1,
        {initial with
          environment := [("curNode", .object 1), ("order", .number 1)],
          heap := [[.object 2]],
          objects := initial.objects ++ [newDataObject emptyLiteralObject scoreKey (.number 1)]})) := by cbv

-- Capture the array identity, not its old contents/length: the inner push or
-- shift completes first, and outer push appends to that current array.
example : (parseExpression "curNode.#methods.push(curNode.#methods.push(1))" ["curNode"] ["methods"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression initial) =
      some (.ok (.number 2, {initial with heap := [[.number 1, .number 1]]})) := by cbv
example : (parseExpression "curNode.#methods.push(curNode.#methods.shift())" ["curNode"] ["methods"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression {initial with heap := [[.number 1, .number 2]]}) =
      some (.ok (.number 2, {initial with heap := [[.number 2, .number 1]]})) := by cbv

-- An own public property with the same spelling is a separate namespace.
private def publicShadow : State :=
  {initial with
    objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject publicKey (.array 1)],
    heap := [[], [.number 7]]}

example : privateGet (.object 1) "methods" publicShadow = .ok (.array 0) := by cbv
example : readProperty (.object 1) (.string publicKey) publicShadow = .ok (.array 1) := by cbv
example : privateGet (.object 1) "methods" {publicShadow with privates := {names := [("methods", 17)]}} =
    .error .privateBrand := by cbv

-- Lexical identity, not spelling or prototype inheritance, supplies the brand.
example : privateGet (.object 1) "methods"
    {initial with privates := {initial.privates with names := [("methods", 18)]}} =
      .error .privateBrand := by cbv
example : privateGet (.object 1) "methods" {initial with privates := {initial.privates with names := []}} =
    .error .privateScope := by cbv
example : privateGet (.object 2) "methods" {initial with objects := initial.objects ++ [⟨[], some 1, true⟩]} =
    .error .privateBrand := by cbv

private def badArgument : State :=
  {initial with environment := ("bad", .object 9) :: initial.environment}

-- Error-priority checks establish evaluation order, not error-state rollback.
-- A nullish member base fails before evaluating the argument's failing read.
example : (parseExpression "curNode.#methods.push(bad.x)" ["curNode", "bad"] ["methods"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression
      {badArgument with privates := {initial.privates with elements := [(1, [(17, .data .null)])]}}) =
        some (.error .unsupported) := by cbv

-- Ordinary member Get occurs before arguments, but a missing/noncallable value
-- is rejected only after them. The argument read error therefore wins here.
example : (parseExpression "curNode.push(bad.x)" ["curNode", "bad"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression badArgument) =
      some (.error (.objectError .invalidReference)) := by cbv
example : (parseExpression "curNode.push(bad.x)" ["curNode", "bad"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression
      {badArgument with objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject pushKey (.number 0)]}) =
        some (.error (.objectError .invalidReference)) := by cbv
example : (parseExpression "curNode.push(bad.x)" ["curNode", "bad"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression
      {badArgument with objects := [objectPrototypeProjection [],
        ⟨[(pushKey, .accessor .unsupported .missing true true)], some 0, true⟩]}) =
          some (.error (.objectError .unsupported)) := by cbv

-- Captured ordinary function members use the existing zero-arg/no-this subset.
example : (parseExpression "curNode.push()" ["curNode"]).map
    (fun expression => evalExpression 34 defaultSplitLimit expression
      {initial with
        objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject pushKey (.function 0)],
        functions := [⟨⟨"f", .number 9⟩, []⟩]}) =
          some (.ok (.number 9,
            {initial with
              objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject pushKey (.function 0)],
              functions := [⟨⟨"f", .number 9⟩, []⟩]})) := by cbv

end HonoLean.Upstream.SourceSubset.PrivateChecks
