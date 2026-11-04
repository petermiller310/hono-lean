import HonoLean.Upstream.LexicalArrow.Rules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025 GetPatternBody

/-- A separate projected Function.prototype cell. The current RegExp binding is
TDZ; wildcard evaluation has no reason to inspect it. -/
def exampleSeed : Runtime :=
  {data := cacheWithAmbient (labelStandardState [])
      {(labelStandardState []).base.regexp.ambient with
        objects := (labelStandardState []).base.regexp.ambient.objects ++ [⟨[], some 0, true⟩]}
   cells := [⟨.mutable, none⟩]
   environments := [⟨[("RegExp", 0)], none⟩]
   current := 0
   thisValue := .number 73}

def exampleCreated : Runtime :=
  (((initializeModule PatternCache.initProgram GetPatternBody.declaration 7 exampleSeed).toOption).map Prod.snd).getD exampleSeed

def wildcardAfter : Runtime :=
  {exampleCreated with
    cells := exampleCreated.cells ++ [⟨.parameter, some GetPatternBody.star⟩, ⟨.parameter, some .undefined⟩]
    environments := exampleCreated.environments ++ [⟨[("label", exampleCreated.cells.length), ("next", exampleCreated.cells.length + 1)], some exampleCreated.current⟩]}

theorem example_setup_created :
    initializeModule PatternCache.initProgram GetPatternBody.declaration 7 exampleSeed = .ok (⟨0⟩, exampleCreated) := by cbv

theorem example_export_is_callable :
    getBindingValue 8 exampleCreated exampleCreated.current "getPattern" = .ok (.object 9) ∧
    resolveArrowValue exampleCreated (.object 9) = .ok ⟨0⟩ := by cbv

theorem example_capture_uses_export_environment :
    (exampleCreated.closures[0]?).map ArrowClosure.environment = some 2 := by cbv

theorem example_unused_global_still_tdz :
    getBindingValue 8 exampleCreated exampleCreated.current "RegExp" = .error .temporalDeadZone := by cbv

theorem example_wildcard_with_tdz_global :
    invokeBinding 16 defaultSplitLimit ⟨labelStandardContext⟩ exampleCreated.current "getPattern"
      [GetPatternBody.star] exampleCreated = .returned GetPatternBody.star wildcardAfter := by cbv

def shadowSeed : Runtime :=
  {exampleSeed with
    cells := [⟨.mutable, some (.number 42)⟩, ⟨.constant, none⟩]
    environments := [⟨[("x", 0)], none⟩, ⟨[("x", 1)], some 0⟩]
    current := 1}

theorem example_tdz_shadows_outer :
    getBindingValue 8 shadowSeed 1 "x" = .error .temporalDeadZone ∧
    (readyEnvironment 8 shadowSeed 1).lookup "x" = none := by cbv

def mutableCreated : Runtime :=
  {exampleCreated with cells := exampleCreated.cells.set 0 ⟨.mutable, some (.function 6)⟩}

def changedGlobal : Runtime :=
  ((setBindingValue 8 mutableCreated mutableCreated.current "RegExp" (.function 999)).toOption).getD mutableCreated

theorem example_current_global_after_update :
    getBindingValue 8 changedGlobal changedGlobal.current "RegExp" = .ok (.function 999) ∧
    (changedGlobal.closures[0]?).map ArrowClosure.environment = some 2 := by cbv

theorem example_arrow_metadata :
    getProperty propertyFuel exampleCreated.data.base.regexp.ambient.objects 9 (cacheAscii "name") = .ok (.string (cacheAscii "getPattern")) ∧
    getProperty propertyFuel exampleCreated.data.base.regexp.ambient.objects 9 (cacheAscii "length") = .ok (.number 2) ∧
    hasOwn exampleCreated.data.base.regexp.ambient.objects 9 (cacheAscii "prototype") = .ok false ∧
    constructArrow exampleCreated ⟨0⟩ = .error .notConstructible := by cbv; exact ⟨rfl, trivial⟩

def withOwnPrototype : Runtime :=
  withAmbient exampleCreated {exampleCreated.data.base.regexp.ambient with
    objects := exampleCreated.data.base.regexp.ambient.objects.set 9
      ⟨[(cacheAscii "prototype", .data .null true true true)], some 7, true⟩}

theorem example_adding_prototype_does_not_make_constructor :
    constructArrow withOwnPrototype ⟨0⟩ = .error .notConstructible := by cbv

end HonoLean.Upstream.LexicalArrow
