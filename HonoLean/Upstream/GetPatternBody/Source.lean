import HonoLean.Upstream.GetPatternBody.Generated
import HonoLean.Upstream.GetPatternBody.Syntax
import HonoLean.Upstream.PatternCache.Composition

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternBody
open SourceSubset hiding pinnedSource
open ECMA2025

def ambientBindings : List String := ["patternCache", "RegExp"]
def star : Value := .string [42]
def guardExpr : PatternCacheExpr := .strictEqual PatternCache.labelExpr (.ordinary (.string [42]))
def guardProgram : List PatternCacheStmt := [.branch guardExpr [.ret (.ordinary (.string [42]))] []]
def program : List PatternCacheStmt := guardProgram ++ PatternCache.program
def declaration : ExportedArrow :=
  ⟨"getPattern", [⟨"label", false, .named "string"⟩, ⟨"next", true, .named "string"⟩],
    .union (.named "Pattern") (.named "null"), "\n" ++ pinnedLeadingComments ++ pinnedBody, program⟩

theorem parses_guard : parsePatternCacheBody pinnedGuard PatternCache.bindings = some guardProgram := by cbv
theorem parses_body : parsePatternCacheBody pinnedBody PatternCache.bindings = some program := by cbv
theorem parses_declaration : parseExportedArrow pinnedDeclaration ambientBindings = some declaration := by cbv
theorem reassembles_body : pinnedBody = pinnedGuard ++ "\n" ++ PatternCache.pinnedSource := by rfl
theorem reassembles_declaration : pinnedDeclaration = pinnedHeader ++ pinnedLeadingComments ++ pinnedBody ++ "}\n\n" := by rfl

def sourceBody (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) : Option (Except PatternCacheError (Value × LabelMatchState)) :=
  (parsePatternCacheBody pinnedBody PatternCache.bindings).map (fun body => runPatternCache fuel defaultSplitLimit context body before)

/-- Execute only the parsed body projection. This does NOT create or invoke a
function object, bind its parameters, or instantiate an export/module closure. -/
def declarationBody (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) : Option (Except PatternCacheError (Value × LabelMatchState)) :=
  (parseExportedArrow pinnedDeclaration ambientBindings).map (fun arrow => runPatternCache fuel defaultSplitLimit context arrow.body before)

theorem declaration_body_source (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) :
    declarationBody fuel context before = sourceBody fuel context before := by
  rw [declarationBody, sourceBody, parses_declaration, parses_body]
  rfl

end HonoLean.Upstream.GetPatternBody
