import HonoLean.Upstream.GetPatternLookahead.Generated
import HonoLean.Upstream.GetPatternBody.Source

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternLookahead
open SourceSubset

/-- Actual nodes projected from the complete parsed source. These selected
operations do not execute ancestor conditions or prove branch reachability. -/
structure SelectedNodes where
  labelDeclaration : PatternCacheStmt
  keyDeclaration : PatternCacheStmt
  positiveTuple : PatternCacheExpr
  positiveConstructor : PatternCacheExpr
  deriving Repr

def branchThen : PatternCacheStmt → Option (List PatternCacheStmt)
  | .branch _ yes _ => some yes
  | _ => none

def assignmentValue : PatternCacheStmt → Option PatternCacheExpr
  | .assign _ value => some value
  | _ => none

def conditionalThen : PatternCacheExpr → Option PatternCacheExpr
  | .conditional _ yes _ => some yes
  | _ => none

def tupleConstructor : PatternCacheExpr → Option PatternCacheExpr
  | .arrayLiteral [_, _, constructor] => some constructor
  | _ => none

/-- Structural path through the actual wildcard/match/cache/m2/next AST.
No method-name search or source-string equality oracle supplies a node. -/
def selectNodes (body : List PatternCacheStmt) : Option SelectedNodes := do
  let label ← body[1]?
  let block ← body[2]? >>= branchThen
  let key ← block[0]?
  let cold ← block[1]? >>= branchThen
  let regex ← cold[0]? >>= branchThen
  let conditional ← regex[0]? >>= assignmentValue
  let tuple ← conditionalThen conditional
  let constructor ← tupleConstructor tuple
  pure ⟨label, key, tuple, constructor⟩

def labelDeclaration : PatternCacheStmt :=
  .declare "match" (.labelMatch (.variable "label") "match" labelActualLiteral)

def keyDeclaration : PatternCacheStmt := .declare "cacheKey" PatternCache.keyTemplate
def positiveTuple : PatternCacheExpr := PatternCache.lookaheadTuple
def positiveConstructor : PatternCacheExpr := .construct (.variable "RegExp") PatternCache.lookaheadTemplate
def nodes : SelectedNodes := ⟨labelDeclaration, keyDeclaration, positiveTuple, positiveConstructor⟩

theorem selects_actual_body : selectNodes GetPatternBody.program = some nodes := by rfl

/-- The kernel connection consumes the complete retained 576-byte source;
the selected constructor is its actual positive conditional branch. -/
theorem parses_source_body_nodes :
    (parsePatternCacheBody pinnedBody PatternCache.bindings).bind selectNodes = some nodes := by
  rw [pinnedBody, GetPatternBody.parses_body]
  exact selects_actual_body

def parsedNodes : Option SelectedNodes :=
  (parsePatternCacheBody pinnedBody PatternCache.bindings).bind selectNodes

theorem parses_nodes : parsedNodes = some nodes := parses_source_body_nodes

theorem parsed_label_declaration : parsedNodes.map SelectedNodes.labelDeclaration = some labelDeclaration := by
  rw [parses_nodes]
  rfl

theorem parsed_key_declaration : parsedNodes.map SelectedNodes.keyDeclaration = some keyDeclaration := by
  rw [parses_nodes]
  rfl

theorem parsed_positive_tuple : parsedNodes.map SelectedNodes.positiveTuple = some positiveTuple := by
  rw [parses_nodes]
  rfl

theorem parsed_positive_constructor : parsedNodes.map SelectedNodes.positiveConstructor = some positiveConstructor := by
  rw [parses_nodes]
  rfl

end HonoLean.Upstream.GetPatternLookahead
