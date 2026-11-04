import HonoLean.Upstream.NodeParamAssignment.Correctness

namespace HonoLean.Upstream.NodeParamAssignment

open SourceSubset ECMA2025

set_option maxRecDepth 32768

private def fixtureEnvironment (parameterReceiver : Value) (key : JSString) (index : Int) :=
  [("handlerSet", Value.object 0), ("key", .string key), ("params", parameterReceiver),
   ("nodeParams", .object 2), ("i", .number index), ("keep", .string [107])]

private def dataState (parameter node : Value) (index : Int) (key : JSString := idKey) : State :=
  {environment := fixtureEnvironment (.object 1) key index,
   heap := [[.string [107]]],
   objects := [newDataObject emptyNullObject paramsKey (.object 3),
     newDataObject emptyNullObject key parameter, newDataObject emptyNullObject key node,
     emptyNullObject]}

/-- Inhabited universal premises, not just a list of closed computations. -/
example (parameter node : Value) (index : Int) (key : JSString) :
    ∃ returned after,
      (parseAssignment pinnedSource bindings).map (fun program => runAssignment program
        (dataState parameter node index key)) = some (.ok (returned, after)) ∧
      AssignmentContract (dataState parameter node index key) 3 key parameter node index returned after := by
  have parameterRead : getProperty 32 (dataState parameter node index key).objects 1 key = .ok parameter :=
    getProperty_data _ 1 31 key (newDataObject emptyNullObject key parameter) parameter
      true true true rfl (putOwn_self _ _ _)
  have nodeRead : getProperty 32 (dataState parameter node index key).objects 2 key = .ok node :=
    getProperty_data _ 2 31 key (newDataObject emptyNullObject key node) node
      true true true rfl (putOwn_self _ _ _)
  exact parsed_source_satisfies _ 0 3 2 (.object 1) key index parameter node
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (.object 1 parameter parameterRead) nodeRead rfl

private def observed (source : String) (before : State) (output : ObjectRef) (key : JSString) :=
  (parseAssignment source bindings).map (fun program => (runAssignment program before).map
    (fun (returned, after) => (returned, (after.objects[output]?).bind (fun object => object.own.lookup key))))

private theorem observed_pinned (before : State) (output : ObjectRef) (key : JSString) :
    observed pinnedSource before output key =
      some ((runAssignment assignment before).map (fun (returned, after) =>
        (returned, (after.objects[output]?).bind (fun object => object.own.lookup key)))) := by
  rw [observed, parses_pinned_source]
  rfl

private def success (value : Value) : Option (Except EvalError (Value × Option PropertyDescriptor)) :=
  some (.ok (value, some (.data value true true true)))

example : observed pinnedSource (dataState (.string [112]) (.string [110]) 0) 3 idKey =
    success (.string [112]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string [112]) (.string [110]) 1) 3 idKey =
    success (.string [110]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string []) (.string [110]) 0) 3 idKey =
    success (.string [110]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.object 0) (.string [110]) 0) 3 idKey =
    success (.object 0) := by rw [observed_pinned]; cbv

/-- Nullish coalescing retains all three falsy-but-present node values. -/
example : observed pinnedSource (dataState (.string [112]) (.string []) 1) 3 idKey =
    success (.string []) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string [112]) (.number 0) 1) 3 idKey =
    success (.number 0) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string [112]) (.boolean false) 1) 3 idKey =
    success (.boolean false) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string [112]) .null 1) 3 idKey =
    success (.string [112]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.string [112]) .undefined 1) 3 idKey =
    success (.string [112]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (dataState (.boolean false) .null 0) 3 idKey =
    success (.boolean false) := by rw [observed_pinned]; cbv

private def nullableState (receiver node : Value) : State :=
  {dataState .undefined node 0 with environment := fixtureEnvironment receiver idKey 0}

example : observed pinnedSource (nullableState .undefined (.number 0)) 3 idKey =
    success (.number 0) := by rw [observed_pinned]; cbv
example : observed pinnedSource (nullableState .null (.string [110])) 3 idKey =
    success (.string [110]) := by rw [observed_pinned]; cbv
example : observed pinnedSource (nullableState .null .null) 3 idKey =
    success .undefined := by rw [observed_pinned]; cbv

/-- Actual parsed-fragment D1 specialization in a manually assembled entry
state, without a claim that the complete Node trace has been translated. -/
example : observed pinnedSource d1FragmentState 4 protoKey = success (.object 0) := by
  rw [observed_pinned]
  cbv

private def priorOutput : OrdinaryObject := newDataObject emptyNullObject idKey (.string [111])
private def populated : State :=
  {dataState (.string [112]) (.string [110]) 1 constructorKey with
    objects := (dataState (.string [112]) (.string [110]) 1 constructorKey).objects.set 3 priorOutput}

/-- A later slot uses the framed theorem with a prior property already present. -/
example : (parseAssignment pinnedSource bindings).map (fun program => runAssignment program populated) =
    some (.ok (.string [110], framedWrittenState populated 3 priorOutput constructorKey (.string [110]))) := by
  apply (parsed_source_correct_framed populated 0 3 2 (.object 1) constructorKey 1
    (.string [112]) (.string [110]) (.string [110]) _ priorOutput
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (.object 1 (.string [112]) rfl) rfl rfl rfl rfl rfl).mpr
  exact ⟨by simp [Selected, Truthy, Nullish], rfl⟩

example : observed pinnedSource populated 3 idKey =
    some (.ok (.string [110], some (.data (.string [111]) true true true))) := by
  rw [observed_pinned]
  cbv

/-- Wrong precedence condition: removing ! makes the first-slot winner change. -/
private def wrongIndexSource : String :=
  "handlerSet.params[key] = params?.[key] && i ? params[key] : (nodeParams[key] ?? params?.[key])"
example : observed wrongIndexSource (dataState (.string [112]) (.string [110]) 0) 3 idKey =
    success (.string [110]) := by cbv

/-- A parsed, executable fault uses truthiness where the source uses nullishness:
the empty node string is incorrectly replaced by the optional parameter value. -/
private def truthyFallbackSource : String :=
  "handlerSet.params[key] = params?.[key] && !i ? params[key] : (nodeParams[key] ? nodeParams[key] : params?.[key])"
example : observed truthyFallbackSource (dataState (.string [112]) (.string []) 1) 3 idKey =
    success (.string [112]) := by cbv

end HonoLean.Upstream.NodeParamAssignment
