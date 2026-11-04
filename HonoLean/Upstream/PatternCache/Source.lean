import HonoLean.Upstream.PatternCache.Generated
import HonoLean.Upstream.SourceSubset.PatternCacheRules
import HonoLean.Upstream.LabelMatch.Correctness

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.PatternCache
open SourceSubset ECMA2025

def bindings : List String := ["label", "next", "patternCache", "RegExp"]
def labelExpr : PatternCacheExpr := .ordinary (.variable "label")
def nextExpr : PatternCacheExpr := .ordinary (.variable "next")
def matchExpr : PatternCacheExpr := .ordinary (.variable "match")
def nameExpr : PatternCacheExpr := .index matchExpr (.ordinary (.number 1))
def bodyExpr : PatternCacheExpr := .index matchExpr (.ordinary (.number 2))
def keyExpr : PatternCacheExpr := .ordinary (.variable "cacheKey")
def cacheExpr : PatternCacheExpr := .index (.ordinary (.variable "patternCache")) keyExpr

def keyTemplate : PatternCacheExpr := .template [] [(.variable "label", [35]), (.variable "next", [])]
def plainTuple : PatternCacheExpr := .arrayLiteral [labelExpr, nameExpr, .ordinary (.boolean true)]
def terminalTemplate : PatternCacheExpr := .template [94] [(.index (.variable "match") (.number 2), [36])]
def lookaheadTemplate : PatternCacheExpr := .template [94]
  [(.index (.variable "match") (.number 2), [40,63,61,47]), (.variable "next", [41])]
def nextCondition : PatternCacheExpr :=
  .logicalAnd (.logicalAnd nextExpr (.strictNotEqual (.index nextExpr (.ordinary (.number 0))) (.ordinary (.string [58]))))
    (.strictNotEqual (.index nextExpr (.ordinary (.number 0))) (.ordinary (.string [42])))
def terminalTuple : PatternCacheExpr := .arrayLiteral [labelExpr, nameExpr, .construct (.variable "RegExp") terminalTemplate]
def lookaheadTuple : PatternCacheExpr := .arrayLiteral [keyExpr, nameExpr, .construct (.variable "RegExp") lookaheadTemplate]
def regexTuple : PatternCacheExpr := .conditional nextCondition lookaheadTuple terminalTuple

def coldProgram : List PatternCacheStmt := [.branch bodyExpr [.assign cacheExpr regexTuple] [.assign cacheExpr plainTuple]]
def block : List PatternCacheStmt :=
  [.declare "cacheKey" keyTemplate, .branch (.logicalNot cacheExpr) coldProgram [], .ret cacheExpr]
def program : List PatternCacheStmt :=
  [.declare "match" (.labelMatch (.variable "label") "match" labelActualLiteral), .branch matchExpr block [], .ret (.ordinary .null)]
def initProgram : PatternCacheInit := ⟨"patternCache", "key", .named "string", .named "Pattern", .emptyObject⟩

theorem parses_source : parsePatternCacheBody pinnedSource bindings = some program := by cbv
theorem parses_block : parsePatternCacheBlock pinnedBlock ("match" :: bindings) = some block := by cbv
theorem parses_init : parsePatternCacheInit pinnedInit = some initProgram := by cbv
theorem parses_plain : parsePatternCacheBody pinnedPlain ("cacheKey" :: "match" :: bindings) = some [.assign cacheExpr plainTuple] := by cbv

def sourceCall (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) : Option (Except PatternCacheError (Value × LabelMatchState)) :=
  (parsePatternCacheBody pinnedSource bindings).map (fun body => runPatternCache fuel defaultSplitLimit context body before)
def sourceBlock (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) : Option (Except PatternCacheError (Value × LabelMatchState)) :=
  (parsePatternCacheBlock pinnedBlock ("match" :: bindings)).map (fun body => runPatternCache fuel defaultSplitLimit context body before)

def sourceInit (fuel : Nat) (context : PatternCacheContext) (before : LabelMatchState) : Option (Except PatternCacheError LabelMatchState) :=
  (parsePatternCacheInit pinnedInit).map (fun declaration => initializePatternCache fuel defaultSplitLimit context declaration before)

end HonoLean.Upstream.PatternCache
