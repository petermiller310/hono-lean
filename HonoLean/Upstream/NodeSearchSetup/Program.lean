import HonoLean.Upstream.NodeSearchSetup.Generated
import HonoLean.Upstream.NodeIterationSetup.Correctness
import HonoLean.Upstream.SourceSubset.FunctionCall
import HonoLean.Upstream.SourceSubset.SplitPath
import HonoLean.Upstream.SearchEntry.Collector

namespace HonoLean.Upstream.NodeSearchSetup

open SourceSubset

def bindings : List String := ["splitPath", "path", "emptyParams", "method"]
def nodeType : TypeSyntax := .application (.named "Node") [.named "T"]
def splitDeclaration : Stmt := .declare "parts" (.invoke (.variable "splitPath") [.variable "path"])

def program : List Stmt :=
  SearchEntry.collectorProgram ++
  [.assign NodePrivateWrite.reset,
   .typedDeclare "curNode" nodeType .this,
   .mutableDeclare "curNodes" none (.arrayLiteral [(false, .variable "curNode")]),
   splitDeclaration,
   .typedDeclare "curNodesQueue" (.array (.array nodeType)) (.arrayLiteral [])] ++
  NodeIterationSetup.lengthProgram

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem parses_source : parseFunctionStatements pinnedSource bindings NodePrivateCall.classPrivateNames true = some program := by cbv

end HonoLean.Upstream.NodeSearchSetup
