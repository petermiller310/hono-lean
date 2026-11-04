import HonoLean.Upstream.NodeLoopEntry.Generated
import HonoLean.Upstream.NodeSearchSetup.Correctness
import HonoLean.Upstream.SourceSubset.ForHeader

namespace HonoLean.Upstream.NodeLoopEntry

open SourceSubset

def outerBindings : List String := ["len"]
def innerBindings : List String := ["curNodes"]

def outerHeader : ForHeader :=
  ⟨[("i", .number 0)], .compare .less (.variable "i") (.variable "len"), "i"⟩
def innerHeader : ForHeader :=
  ⟨[("j", .number 0), ("len2", .property (.variable "curNodes") NodeParamLoop.lengthKey)],
    .compare .less (.variable "j") (.variable "len2"), "j"⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem parses_outer : parseForHeader pinnedOuterSource outerBindings = some outerHeader := by cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem parses_inner : parseForHeader pinnedInnerSource innerBindings = some innerHeader := by cbv

end HonoLean.Upstream.NodeLoopEntry
