import Std
import HonoLean.Upstream.NodeFirstLiteral.Generated
import HonoLean.Upstream.NodeSearchSetup.Generated
import HonoLean.Upstream.NodeLoopEntry.Generated
import HonoLean.Upstream.NodeIterationSetup.Generated

namespace HonoLean.Upstream.NodeFirstLiteral

set_option maxRecDepth 32768 in
/-- Every character of the actual contiguous source prefix is accounted for.
The two separators are source blank lines98/103, not omitted executable code.
The component parsers retain their explicit segmented-prefix boundaries; this
does not claim a full TypeScript parser or complete loop-body semantics. -/
theorem reassembles_source :
    pinnedFullSource = NodeSearchSetup.pinnedSource ++ "\n" ++
      NodeLoopEntry.pinnedOuterSource ++ NodeIterationSetup.pinnedIterationSource ++ "\n" ++
      NodeLoopEntry.pinnedInnerSource ++ NodeIterationSetup.pinnedEntrySource := by cbv

end HonoLean.Upstream.NodeFirstLiteral
