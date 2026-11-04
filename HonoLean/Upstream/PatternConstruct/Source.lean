import HonoLean.Upstream.PatternConstruct.Generated
import HonoLean.Upstream.SourceSubset.RegExpConstructRules

set_option autoImplicit false
namespace HonoLean.Upstream.PatternConstruct
open SourceSubset ECMA2025

def bindings : List String := ["label", "match", "RegExp"]
def labelExpr : Expr := .variable "label"
def nameExpr : Expr := .index (.variable "match") (.number 1)
def bodyExpr : Expr := .index (.variable "match") (.number 2)
def templateExpr : RegExpConstructExpr := .template [94] bodyExpr [36]
def constructorExpr : RegExpConstructExpr := .construct (.variable "RegExp") templateExpr
def program : RegExpConstructExpr := .arrayLiteral [.ordinary labelExpr, .ordinary nameExpr, constructorExpr]

theorem reassembles_expression : pinnedSource = "[label, match[1], " ++ pinnedConstructor ++ "]" := by cbv
/-- The colon belongs to the omitted conditional; it is bound as context,
not parsed as a fabricated standalone statement or complete cache branch. -/
theorem expression_is_original_line : pinnedLine = "            : " ++ pinnedSource ++ "\n" := by cbv
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_source : parseRegExpConstruct pinnedSource bindings [] = some program := by cbv
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem parses_constructor : parseRegExpConstruct pinnedConstructor bindings [] = some constructorExpr := by cbv

def sourceConstruct (fuel : Nat) (context : RegExpConstructContext) (before : RegExpCallState) : Option (Except RegExpConstructError (Value × RegExpCallState)) :=
  (parseRegExpConstruct pinnedSource bindings []).map
    (fun parsed => evalRegExpConstruct fuel defaultSplitLimit context parsed before)

def sourceConstructor (fuel : Nat) (context : RegExpConstructContext) (before : RegExpCallState) : Option (Except RegExpConstructError (Value × RegExpCallState)) :=
  (parseRegExpConstruct pinnedConstructor bindings []).map
    (fun parsed => evalRegExpConstruct fuel defaultSplitLimit context parsed before)

end HonoLean.Upstream.PatternConstruct
