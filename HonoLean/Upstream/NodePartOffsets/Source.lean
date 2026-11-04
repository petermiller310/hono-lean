import HonoLean.Upstream.NodePartOffsets.Generated
import HonoLean.Upstream.SourceSubset.OffsetRules

namespace HonoLean.Upstream.NodePartOffsets

open SourceSubset ECMA2025

set_option maxRecDepth 32768

def bindings : List String := ["partOffsets", "path", "parts", "len", "i"]
def mutableBindings : List String := ["partOffsets"]
def startExpression : OffsetExpr := .conditional
  (.strictEqual (.index (.ordinary (.variable "path")) (.ordinary (.number 0))) (.ordinary (.string [47])))
  (.ordinary (.number 1)) (.ordinary (.number 0))
def stepExpression : OffsetExpr := .add
  (.property (.index (.ordinary (.variable "parts")) (.ordinary (.variable "p"))) [108, 101, 110, 103, 116, 104])
  (.ordinary (.number 1))
def loopHeader : ForHeader := ⟨[("p", .number 0)], .compare .less (.variable "p") (.variable "len"), "p"⟩
def loopBody : List OffsetStmt :=
  [.assign (.index (.ordinary (.variable "partOffsets")) (.ordinary (.variable "p"))) (.ordinary (.variable "offset")),
   .addAssign "offset" stepExpression]
def branchBody : List OffsetStmt :=
  [.assign (.ordinary (.variable "partOffsets")) (.ordinary (.arrayLiteral [])),
   .declare true "offset" startExpression,
   .countedFor loopHeader loopBody]
def prepareProgram : List OffsetStmt := [.branch (.logicalNot (.ordinary (.variable "partOffsets"))) branchBody]
def sliceExpression : OffsetExpr := .call (.ordinary (.variable "path")) "slice"
  [.index (.ordinary (.variable "partOffsets")) (.ordinary (.variable "i"))]
def sliceProgram : List OffsetStmt := [.declare false "restPathString" sliceExpression]
def program : List OffsetStmt := prepareProgram ++ sliceProgram

theorem reassembles_source : pinnedSource = pinnedPrepare ++ pinnedSlice := by cbv
set_option maxHeartbeats 2000000 in
theorem parses_prepare : parseOffsetSequence pinnedPrepare bindings mutableBindings = some prepareProgram := by cbv
set_option maxHeartbeats 2000000 in
theorem parses_slice : parseOffsetSequence pinnedSlice bindings mutableBindings = some sliceProgram := by cbv
set_option maxHeartbeats 2000000 in
theorem parses_source : parseOffsetSequence pinnedSource bindings mutableBindings = some program := by cbv

def sourcePrepare (fuel : Nat) (before : State) : Option (Except EvalError State) := do
  let parsed ← parseOffsetSequence pinnedPrepare bindings mutableBindings
  pure (executeOffsetSequence fuel defaultSplitLimit mutableBindings parsed before)
def sourceOffsets (fuel : Nat) (before : State) : Option (Except EvalError State) := do
  let parsed ← parseOffsetSequence pinnedSource bindings mutableBindings
  pure (executeOffsetSequence fuel defaultSplitLimit mutableBindings parsed before)

end HonoLean.Upstream.NodePartOffsets
