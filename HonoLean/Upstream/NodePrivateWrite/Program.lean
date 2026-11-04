import HonoLean.Upstream.NodePrivateWrite.Generated
import HonoLean.Upstream.NodePrivateCall.Program
import HonoLean.Upstream.SourceSubset.Parser

namespace HonoLean.Upstream.NodePrivateWrite

open SourceSubset

def resetBindings : List String := ["emptyParams"]
def propagationBindings : List String := ["nextNode", "node"]
def parameterBindings : List String := ["child", "params"]

def reset : Assignment := ⟨.privateProperty .this "params", .variable "emptyParams"⟩
def propagation : Assignment :=
  ⟨.privateProperty (.variable "nextNode") "params", .privateProperty (.variable "node") "params"⟩
def parameter : Assignment := ⟨.privateProperty (.variable "child") "params", .variable "params"⟩

set_option maxRecDepth 32768 in
theorem parses_reset : parseAssignment pinnedResetSource resetBindings NodePrivateCall.classPrivateNames true = some reset := by cbv

set_option maxRecDepth 32768 in
theorem parses_propagation : parseAssignment pinnedPropagationSource propagationBindings NodePrivateCall.classPrivateNames = some propagation := by cbv

set_option maxRecDepth 32768 in
theorem parses_wildcard : parseAssignment pinnedWildcardSource parameterBindings NodePrivateCall.classPrivateNames = some parameter := by cbv

set_option maxRecDepth 32768 in
theorem parses_parameter : parseAssignment pinnedParameterSource parameterBindings NodePrivateCall.classPrivateNames = some parameter := by cbv

set_option maxRecDepth 32768 in
theorem parses_reset_statement : parseBlock pinnedResetSource resetBindings NodePrivateCall.classPrivateNames true = some [.assign reset] := by cbv

set_option maxRecDepth 32768 in
theorem parses_propagation_statement : parseBlock pinnedPropagationSource propagationBindings NodePrivateCall.classPrivateNames = some [.assign propagation] := by cbv

set_option maxRecDepth 32768 in
theorem parses_parameter_statement : parseBlock pinnedParameterSource parameterBindings NodePrivateCall.classPrivateNames = some [.assign parameter] := by cbv

end HonoLean.Upstream.NodePrivateWrite
