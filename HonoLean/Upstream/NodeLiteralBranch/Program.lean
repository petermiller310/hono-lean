import HonoLean.Upstream.NodeLiteralBranch.Generated
import HonoLean.Upstream.NodePrivateWrite.Program
import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.SourceSubset.PrivateControl

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset

def bindings : List String := ["node", "part", "isLast", "handlerSets", "method", "tempNodes"]

def nextLookup : Expr := .index (.privateProperty (.variable "node") "children") (.variable "part")
def wildcardLookup : Expr := .index (.privateProperty (.variable "nextNode") "children") (.string [42])

def wildcardCall : PrivateMethodCall :=
  ⟨.this, "pushHandlerSets", [.variable "handlerSets", wildcardLookup, .variable "method",
    .privateProperty (.variable "node") "params"]⟩

def lastBody : List PrivateControlStmt :=
  [.branch wildcardLookup [.privateCall wildcardCall] [], .privateCall NodePrivateCall.fourCall]

def enqueue : Stmt := .evaluate (.call (.variable "tempNodes") "push" [.variable "nextNode"])

def childBody : List PrivateControlStmt :=
  [.ordinary (.assign NodePrivateWrite.propagation),
   .branch (.variable "isLast") lastBody [.ordinary enqueue]]

def program : List PrivateControlStmt :=
  [.ordinary (.declare "nextNode" nextLookup), .branch (.variable "nextNode") childBody []]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem parses_source : parsePrivateControl pinnedSource bindings NodePrivateCall.classPrivateNames = some program := by cbv

end HonoLean.Upstream.NodeLiteralBranch
