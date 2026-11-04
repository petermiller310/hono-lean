import HonoLean.Upstream.SourceSubset.MethodParser
import HonoLean.Upstream.NodePrivateCall.Generated
import HonoLean.Upstream.MethodsLoop.Contract

namespace HonoLean.Upstream.NodePrivateCall

open SourceSubset ECMA2025

def classPrivateNames : List String :=
  ["methods", "children", "patterns", "pattern", "params", "pushHandlerSets"]

def lexicalBindings : List String := ["METHOD_NAME_ALL", "createNullObject", "Object"]

def recordType : TypeSyntax := .application (.named "Record") [.named "string", .named "string"]

def methodProgram : PrivateMethod :=
  ⟨"pushHandlerSets",
    [⟨"handlerSets", false, .array (.application (.named "HandlerParamsSet") [.named "T"])⟩,
     ⟨"node", false, .application (.named "Node") [.named "T"]⟩,
     ⟨"method", false, .named "string"⟩,
     ⟨"nodeParams", false, recordType⟩,
     ⟨"params", true, recordType⟩],
    .named "void", MethodsLoop.program⟩

def fourBindings : List String := ["handlerSets", "nextNode", "method", "node"]
def fiveBindings : List String := ["handlerSets", "child", "method", "params", "node"]

def fourCall : PrivateMethodCall :=
  ⟨.this, "pushHandlerSets", [.variable "handlerSets", .variable "nextNode", .variable "method",
    .privateProperty (.variable "node") "params"]⟩

def fiveCall : PrivateMethodCall :=
  ⟨.this, "pushHandlerSets", [.variable "handlerSets", .variable "child", .variable "method",
    .variable "params", .privateProperty (.variable "node") "params"]⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem parses_method : parsePrivateMethod pinnedMethodSource lexicalBindings classPrivateNames =
    some methodProgram := by cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem parses_four : parsePrivateMethodCall pinnedFourSource fourBindings classPrivateNames =
    some fourCall := by cbv

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem parses_five : parsePrivateMethodCall pinnedFiveSource fiveBindings classPrivateNames =
    some fiveCall := by cbv

theorem parsed_body_is_existing_loop :
    (parsePrivateMethod pinnedMethodSource lexicalBindings classPrivateNames).map PrivateMethod.body =
      parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"] := by
  rw [parses_method, MethodsLoop.parses_source]
  rfl

end HonoLean.Upstream.NodePrivateCall
