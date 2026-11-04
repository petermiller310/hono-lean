import HonoLean.Upstream.NodeFirstLiteral.Transport

namespace HonoLean.Upstream.NodeFirstLiteral

open SourceSubset ECMA2025 MethodsLoopInitial

theorem lookup_selected (before : State) (owner children stamp emptyParams : Nat) (old : Value)
    (path : JSString) (next : Value)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) old)
    (reads : Lookup before owner children path next) :
    NodeLiteralBranch.Lookup (selected before owner stamp emptyParams path) owner children (firstPart path) next := by
  refine ⟨selected_node before owner stamp emptyParams path, selected_part before owner stamp emptyParams path, ?_, reads.nextRead⟩
  exact selected_private_other before owner owner stamp emptyParams path "children" (stamp + 1) old (.object children) writable
    (by simp [scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]) (by omega) reads.childrenRead

theorem child_selected (before : State) (owner children target stamp emptyParams : Nat) (oldRoot oldTarget : Value)
    (path query : JSString)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) oldRoot)
    (thisValue : before.thisValue = .object owner)
    (queryBinding : before.environment.lookup "method" = some (.string query))
    (entry : Child before owner children target stamp path oldTarget) :
    NodeLiteralBranch.ChildEntry (selected before owner stamp emptyParams path) owner children target owner stamp before.heap.length
      (before.heap.length + 4) emptyParams (firstPart path) query (NodeIterationSetup.lastValue (NodeSearchSetup.producedParts path) 0)
      (targetOld owner target emptyParams oldTarget) := by
  refine ⟨lookup_selected before owner children stamp emptyParams oldRoot path (.object target) scope writable entry.lookup,
    scope, selected_writable before owner target stamp emptyParams path oldTarget entry.writable,
    selected_parent_params before owner stamp emptyParams path oldRoot writable,
    selected_last before owner stamp emptyParams path, thisValue, selected_collector before owner stamp emptyParams path,
    (selected_method before owner stamp emptyParams path).trans queryBinding, selected_temp before owner stamp emptyParams path⟩

def direct_selected (before : State) (methods : PrivateMethodTable) (closure : PrivateMethodClosure)
    (owner target stamp handle children emptyParams keyBound : Nat) (oldRoot : Value) (path query : JSString)
    (wildcard : Value) (records : List Record)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) oldRoot)
    (ready : Direct before methods closure owner target stamp handle children keyBound emptyParams query wildcard records) :
    NodeLiteralBranch.DirectEntry (selected before owner stamp emptyParams path) methods closure target owner stamp handle before.heap.length
      (before.heap.length + 4) children keyBound emptyParams query wildcard records [] :=
  ⟨selected_callable before methods closure owner stamp handle emptyParams path oldRoot scope writable ready.callable,
    ⟨ready.storage.methods, ready.storage.rows, selected_storage before closure owner target stamp emptyParams path oldRoot writable ready.storage⟩,
    selected_private_other before owner target stamp emptyParams path "children" (stamp + 1) oldRoot (.object children) writable
      (by simp [scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]) (by omega) ready.childrenRead,
    ready.wildcardRead, ready.wildcardFalsy, by omega,
    selected_layout before closure owner target stamp emptyParams keyBound path query ready.storage.rows records ready.reads⟩

def wildcard_selected (before : State) (methods : PrivateMethodTable) (closure : PrivateMethodClosure)
    (owner target wildcardTarget stamp handle children emptyParams keyBound : Nat) (oldRoot : Value) (path query : JSString)
    (records : List Record)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) oldRoot)
    (ready : Wildcard before methods closure owner target wildcardTarget stamp handle children keyBound emptyParams query records) :
    NodeLiteralBranch.WildcardEntry (selected before owner stamp emptyParams path) methods closure target wildcardTarget owner stamp handle before.heap.length
      (before.heap.length + 4) children keyBound emptyParams query records [] :=
  ⟨selected_callable before methods closure owner stamp handle emptyParams path oldRoot scope writable ready.callable,
    ⟨ready.direct.methods, ready.direct.rows, selected_storage before closure owner target stamp emptyParams path oldRoot writable ready.direct⟩,
    ⟨ready.wildcard.methods, ready.wildcard.rows, selected_storage before closure owner wildcardTarget stamp emptyParams path oldRoot writable ready.wildcard⟩,
    selected_private_other before owner target stamp emptyParams path "children" (stamp + 1) oldRoot (.object children) writable
      (by simp [scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]) (by omega) ready.childrenRead,
    ready.wildcardRead, by omega,
    selected_layout before closure owner wildcardTarget stamp emptyParams keyBound path query (ready.wildcard.rows ++ ready.direct.rows) records ready.reads⟩

end HonoLean.Upstream.NodeFirstLiteral
