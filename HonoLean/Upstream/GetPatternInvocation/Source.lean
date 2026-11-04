import HonoLean.Upstream.GetPatternInvocation.Generated
import HonoLean.Upstream.GetPatternBody.Composition
import HonoLean.Upstream.LexicalArrow.Runtime

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternInvocation
open SourceSubset hiding pinnedSource

/-- The admitted setup grammar retains the first, single-line typed cache
initializer and parses the remaining exported arrow, including its real body.
The exact combined upstream excerpt, rather than a supplied AST, is the entry. -/
structure ParsedSetup where
  initializer : PatternCacheInit
  arrow : GetPatternBody.ExportedArrow
  deriving Repr

def setupParts (text : String) : Option (String × String) := do
  let characters := text.toList
  let first := characters.takeWhile (· != '\n')
  let '\n' :: remaining := characters.drop first.length | none
  pure (String.ofList (first ++ ['\n']), String.ofList remaining)

def parseSetup (text : String) : Option ParsedSetup := do
  let (initializerSource, arrowSource) ← setupParts text
  let initializer ← parsePatternCacheInit initializerSource
  let arrow ← GetPatternBody.parseExportedArrow arrowSource [initializer.name, "RegExp"]
  pure ⟨initializer, arrow⟩

def setup : ParsedSetup := ⟨PatternCache.initProgram, GetPatternBody.declaration⟩

theorem setup_reassembles : GetPatternInvocation.pinnedSetup =
    GetPatternInvocation.pinnedInit ++ GetPatternInvocation.pinnedDeclaration := by cbv

theorem setup_parts : setupParts GetPatternInvocation.pinnedSetup = some (PatternCache.pinnedInit, GetPatternBody.pinnedDeclaration) := by cbv

theorem parses_setup : parseSetup pinnedSetup = some setup := by
  rw [parseSetup, setup_parts]
  dsimp only [bind, Option.bind]
  rw [PatternCache.parses_init]
  dsimp only [bind, Option.bind]
  rw [show [PatternCache.initProgram.name, "RegExp"] = GetPatternBody.ambientBindings from rfl,
    GetPatternBody.parses_declaration]
  rfl

theorem parsed_initializer : (parseSetup pinnedSetup).map ParsedSetup.initializer = some PatternCache.initProgram := by
  rw [parses_setup]
  rfl

theorem parsed_arrow : (parseSetup pinnedSetup).map ParsedSetup.arrow = some GetPatternBody.declaration := by
  rw [parses_setup]
  rfl

theorem parsed_body : (parseSetup pinnedSetup).map (fun parsed => parsed.arrow.body) = some GetPatternBody.program := by
  rw [parses_setup]
  rfl

/-- Actual combined source executes cache initialization and creates/exports
the parsed arrow. This is the admitted source fragment, not a native TS loader. -/
def sourceSetup (functionPrototype : Nat) (before : LexicalArrow.Runtime) :
    Option (Except LexicalArrow.Error (LexicalArrow.ArrowHandle × LexicalArrow.Runtime)) :=
  (parseSetup pinnedSetup).map (fun parsed =>
    LexicalArrow.initializeModule parsed.initializer parsed.arrow functionPrototype before)

theorem source_setup_runtime (functionPrototype : Nat) (before : LexicalArrow.Runtime) :
    sourceSetup functionPrototype before = some (LexicalArrow.initializeModule PatternCache.initProgram GetPatternBody.declaration functionPrototype before) := by
  rw [sourceSetup, parses_setup]
  rfl

end HonoLean.Upstream.GetPatternInvocation
