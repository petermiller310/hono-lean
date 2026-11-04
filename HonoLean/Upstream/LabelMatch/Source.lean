import HonoLean.Upstream.LabelMatch.Generated
import HonoLean.Upstream.SourceSubset.LabelMatchRules

set_option autoImplicit false
namespace HonoLean.Upstream.LabelMatch
open SourceSubset ECMA2025

def bindings : List String := ["label"]
def program : LabelMatchDecl := ⟨"match", .variable "label", "match", labelActualLiteral⟩
theorem parses_source : parseLabelMatch pinnedSource bindings = some program := by cbv
theorem reassembles_source : pinnedSource = "  const match = " ++ pinnedCall ++ "\n" ∧
    pinnedCall = "label.match(" ++ pinnedLiteral ++ ")" ∧ pinnedLiteral = "/" ++ pinnedPattern ++ "/" := by decide

def sourceMatch (fuel : Nat) (context : LabelMatchContext) (before : LabelMatchState) : Option (Except LabelMatchError LabelMatchState) :=
  (parseLabelMatch pinnedSource bindings).map (fun declaration => executeLabelMatch fuel defaultSplitLimit context declaration before)

end HonoLean.Upstream.LabelMatch
