import HonoLean.Upstream.NodeIterationSetup.Generated
import HonoLean.Upstream.NodeLiteralBranch.Correctness

namespace HonoLean.Upstream.NodeIterationSetup

open SourceSubset

def lengthBindings : List String := ["parts"]
def outerBindings : List String := ["parts", "i", "len"]
def nodeBranchBindings : List String := ["curNodes", "j", "part", "isLast", "tempNodes", "handlerSets", "method"]

def lengthProgram : List Stmt :=
  [.declare "len" (.property (.variable "parts") NodeParamLoop.lengthKey),
   .mutableDeclare "partOffsets" (some (.union (.array (.named "number")) (.named "null"))) .null]

def lastExpression : Expr := .strictEqual (.variable "i") (.subtract (.variable "len") (.number 1))

def outerProgram : List Stmt :=
  [.typedDeclare "part" (.named "string") (.index (.variable "parts") (.variable "i")),
   .declare "isLast" lastExpression,
   .typedDeclare "tempNodes" (.array (.application (.named "Node") [.named "T"])) (.arrayLiteral [])]

def nodeDeclaration : Stmt := .declare "node" (.index (.variable "curNodes") (.variable "j"))
def nodeBranchProgram : List PrivateControlStmt := .ordinary nodeDeclaration :: NodeLiteralBranch.program

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem parses_length : parseBlock pinnedSearchSource lengthBindings = some lengthProgram := by cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem parses_outer : parseBlock pinnedIterationSource outerBindings = some outerProgram := by cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem parses_node_branch : parsePrivateControl pinnedEntrySource nodeBranchBindings NodePrivateCall.classPrivateNames =
    some nodeBranchProgram := by cbv

end HonoLean.Upstream.NodeIterationSetup
