import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics
import HonoLean.Upstream.NodeParamAssignment.Generated

namespace HonoLean.Upstream.NodeParamAssignment

open SourceSubset ECMA2025

def paramsKey : JSString := [112, 97, 114, 97, 109, 115]

def assignment : Assignment :=
  ⟨.index (.property (.variable "handlerSet") paramsKey) (.variable "key"),
    .conditional
      (.logicalAnd (.optionalIndex (.variable "params") (.variable "key"))
        (.logicalNot (.variable "i")))
      (.index (.variable "params") (.variable "key"))
      (.nullish (.index (.variable "nodeParams") (.variable "key"))
        (.optionalIndex (.variable "params") (.variable "key")))⟩

def bindings : List String := ["handlerSet", "key", "params", "i", "nodeParams"]

set_option maxRecDepth 32768 in
/-- Exact lines79–80 are parsed by the generic assignment/expression parser.
Surrounding Node control flow and the containing method are not parsed here. -/
theorem parses_pinned_source : parseAssignment pinnedSource bindings = some assignment := by cbv

/-- Truthiness for the declared finite-integer value domain, specified without
calling the expression evaluator. Native Number/coercion adequacy stays open. -/
def Truthy : Value → Prop
  | .string contents => contents ≠ []
  | .number integer => integer ≠ 0
  | .boolean value => value = true
  | .null | .undefined => False
  | .array _ | .object _ | .objectConstructor | .function _ | .set _ | .setConstructor => True

def Nullish (value : Value) : Prop := value = .null ∨ value = .undefined

/-- Independent value-selection relation. The first optional value wins only
when truthy at index zero. Otherwise a non-nullish node value wins, including
empty string, zero and false; only null/undefined fall back to the optional value. -/
def Selected (parameter node : Value) (index : Int) (selected : Value) : Prop :=
  (Truthy parameter ∧ index = 0 ∧ selected = parameter) ∨
  ((¬ Truthy parameter ∨ index ≠ 0) ∧
    ((¬ Nullish node ∧ selected = node) ∨ (Nullish node ∧ selected = parameter)))

def writtenState (before : State) (output : ObjectRef) (key : JSString) (value : Value) : State :=
  {before with objects := before.objects.set output (newDataObject emptyNullObject key value)}

/-- This contract does not invoke the source evaluator or Set. Its scope is an
empty-own null-prototype output slot. It states the selected value and
the exact one-cell descriptor update, preserving all other state fields/cells. -/
def AssignmentContract (before : State) (output : ObjectRef) (key : JSString)
    (parameter node : Value) (index : Int) (returned : Value) (after : State) : Prop :=
  Selected parameter node index returned ∧ after = writtenState before output key returned

structure LocalBindings (state : State) (handlerSet : ObjectRef) (parameterValue : Value) (nodeParams : ObjectRef)
    (key : JSString) (index : Int) : Prop where
  handler : state.environment.lookup "handlerSet" = some (.object handlerSet)
  keyValue : state.environment.lookup "key" = some (.string key)
  parameter : state.environment.lookup "params" = some parameterValue
  node : state.environment.lookup "nodeParams" = some (.object nodeParams)
  iteration : state.environment.lookup "i" = some (.number index)

theorem truthy_iff (value : Value) : truthy value = true ↔ Truthy value := by
  cases value <;> simp [truthy, Truthy]

theorem isNullish_iff (value : Value) : isNullish value = true ↔ Nullish value := by
  cases value <;> simp [isNullish, Nullish]

/-- Proof intermediate only; the public contract is the independent relation
above, not equality to this helper or to an evaluator result. -/
private def chosenValue (parameter node : Value) (index : Int) : Value :=
  if truthy parameter && decide (index = 0) then parameter
  else if isNullish node then parameter else node

private theorem selected_iff (parameter node : Value) (index : Int) (selected : Value) :
    Selected parameter node index selected ↔ selected = chosenValue parameter node index := by
  simp only [Selected, ← truthy_iff, ← isNullish_iff]
  cases parameterTruthy : truthy parameter <;> cases nodeNullish : isNullish node <;>
    by_cases zero : index = 0 <;> simp [chosenValue, parameterTruthy, nodeNullish, zero, -truthy, -isNullish]

theorem reference_captured (state : State) (handlerSet output : ObjectRef) (parameterValue : Value) (nodeParams : ObjectRef)
    (key : JSString) (index : Int) (limit : Nat)
    (context : LocalBindings state handlerSet parameterValue nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output)) :
    evalReference 31 limit assignment.target state = .ok (⟨.object output, .string key⟩, state) := by
  simp [assignment, evalReference, evalExpression, lookupVariable, context.handler, context.keyValue,
    handlerRead, readProperty, Except.mapError, bind, pure, Except.bind, Except.pure]

theorem rhs_selected (state : State) (handlerSet parameterRef nodeParams : ObjectRef)
    (key : JSString) (index : Int) (limit : Nat) (parameter node : Value)
    (context : LocalBindings state handlerSet (.object parameterRef) nodeParams key index)
    (parameterRead : getProperty propertyFuel state.objects parameterRef key = .ok parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression 31 limit assignment.value state = .ok (chosenValue parameter node index, state) := by
  have truthyBoolean (value : Bool) : truthy (.boolean value) = value := rfl
  have truthyNumber (integer : Int) : truthy (.number integer) = decide (integer ≠ 0) := rfl
  have objectNotNullish (reference : ObjectRef) : isNullish (.object reference) = false := rfl
  cases parameterTruthy : truthy parameter <;> cases nodeNullish : isNullish node <;>
    by_cases zero : index = 0 <;>
    simp [assignment, evalExpression, lookupVariable, context.parameter, context.keyValue,
      context.node, context.iteration, parameterRead, nodeRead, readProperty, Except.mapError,
      chosenValue, parameterTruthy, nodeNullish, zero, bind, pure, Except.bind, Except.pure,
      -truthy, -isNullish, truthyBoolean, truthyNumber, objectNotNullish]

theorem run_selected (state : State) (handlerSet output parameterRef nodeParams : ObjectRef)
    (key : JSString) (index : Int) (limit : Nat) (parameter node : Value)
    (context : LocalBindings state handlerSet (.object parameterRef) nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : getProperty propertyFuel state.objects parameterRef key = .ok parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputEmpty : state.objects[output]? = some emptyNullObject) :
    runAssignment assignment state limit =
      .ok (chosenValue parameter node index,
        writtenState state output key (chosenValue parameter node index)) := by
  simp only [runAssignment, executeAssignment, evalAssignmentReference, assignment]
  have captured := reference_captured state handlerSet output (.object parameterRef) nodeParams key index limit context handlerRead
  simp only [assignment] at captured
  rw [captured]
  simp only [Except.bind, bind, pure, Except.pure]
  have selected := rhs_selected state handlerSet parameterRef nodeParams key index limit parameter node context
    parameterRead nodeRead
  simp only [assignment] at selected
  rw [selected]
  have write := setProperty_null state.objects output 31 key (chosenValue parameter node index) outputEmpty
  change setProperty 32 state.objects output key (chosenValue parameter node index) = _ at write
  simp [putAssignmentReference, putReference, propertyFuel, write, writtenState, Except.mapError, bind,
    pure, Except.bind, Except.pure]

/-- Universal selected-values/keys theorem for admissible pure object reads and
an empty-own null-prototype output. Reads may be own data or supported inherited
legacy descriptors; arbitrary effectful getters/proxies are outside this model.
Requiring both reads to succeed is conservative even on a skipped branch. -/
theorem parsed_object_source_correct (state : State)
    (handlerSet output parameterRef nodeParams : ObjectRef) (key : JSString)
    (index : Int) (parameter node returned : Value) (after : State)
    (context : LocalBindings state handlerSet (.object parameterRef) nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : getProperty propertyFuel state.objects parameterRef key = .ok parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputEmpty : state.objects[output]? = some emptyNullObject) :
    (parseAssignment pinnedSource bindings).map (fun program => runAssignment program state) =
      some (.ok (returned, after)) ↔
      AssignmentContract state output key parameter node index returned after := by
  rw [parses_pinned_source, Option.map_some,
    run_selected state handlerSet output parameterRef nodeParams key index defaultSplitLimit
      parameter node context handlerRead parameterRead nodeRead outputEmpty]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, AssignmentContract, selected_iff]
  constructor
  · rintro ⟨value, stateEqual⟩
    exact ⟨value.symm, by simpa only [value] using stateEqual.symm⟩
  · rintro ⟨value, stateEqual⟩
    subst returned
    exact ⟨rfl, stateEqual.symm⟩

theorem rhs_nullish_parameter (state : State) (handlerSet nodeParams : ObjectRef)
    (parameterValue : Value) (key : JSString) (index : Int) (limit : Nat) (node : Value)
    (context : LocalBindings state handlerSet parameterValue nodeParams key index)
    (nullish : Nullish parameterValue)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression 31 limit assignment.value state =
      .ok (chosenValue .undefined node index, state) := by
  have nullishParameter := (isNullish_iff parameterValue).mpr nullish
  have undefinedFalsy : truthy .undefined = false := rfl
  cases nodeNullish : isNullish node <;>
    simp [assignment, evalExpression, lookupVariable, context.parameter, context.keyValue,
      context.node, nodeRead, readProperty, Except.mapError, chosenValue, nullishParameter,
      undefinedFalsy, nodeNullish, bind, pure, Except.bind, Except.pure, -truthy, -isNullish]

theorem run_nullish_parameter (state : State) (handlerSet output nodeParams : ObjectRef)
    (parameterValue : Value) (key : JSString) (index : Int) (limit : Nat) (node : Value)
    (context : LocalBindings state handlerSet parameterValue nodeParams key index)
    (nullish : Nullish parameterValue)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputEmpty : state.objects[output]? = some emptyNullObject) :
    runAssignment assignment state limit =
      .ok (chosenValue .undefined node index,
        writtenState state output key (chosenValue .undefined node index)) := by
  simp only [runAssignment, executeAssignment, evalAssignmentReference, assignment]
  have captured := reference_captured state handlerSet output parameterValue nodeParams key index limit context handlerRead
  simp only [assignment] at captured
  rw [captured]
  simp only [Except.bind, bind, pure, Except.pure]
  have selected := rhs_nullish_parameter state handlerSet nodeParams parameterValue key index limit node context nullish nodeRead
  simp only [assignment] at selected
  rw [selected]
  have write := setProperty_null state.objects output 31 key (chosenValue .undefined node index) outputEmpty
  change setProperty 32 state.objects output key (chosenValue .undefined node index) = _ at write
  simp [putAssignmentReference, putReference, propertyFuel, write, writtenState, Except.mapError, bind,
    pure, Except.bind, Except.pure]

/-- Supported optional input: either an object with a pure successful own or
inherited read, or a nullish receiver whose optional read is undefined. -/
inductive ParameterRead (state : State) (key : JSString) : Value → Value → Prop where
  | object (reference : ObjectRef) (value : Value)
      (read : getProperty propertyFuel state.objects reference key = .ok value) :
      ParameterRead state key (.object reference) value
  | nullish (receiver : Value) (missing : Nullish receiver) :
      ParameterRead state key receiver .undefined

/-- Checked assignment-fragment behavior for all supported optional receiver
cases and all keys/selected values. Repeated reads coincide because the declared
property reader is pure; arbitrary accessor effects and surrounding Node loops,
branch selection and traversal are not covered. No allocation freshness follows
from the empty-output-slot premise; allocation is a separate source slice. -/
theorem parsed_source_correct (state : State) (handlerSet output nodeParams : ObjectRef)
    (parameterReceiver : Value) (key : JSString) (index : Int)
    (parameter node returned : Value) (after : State)
    (context : LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputEmpty : state.objects[output]? = some emptyNullObject) :
    (parseAssignment pinnedSource bindings).map (fun program => runAssignment program state) =
      some (.ok (returned, after)) ↔
      AssignmentContract state output key parameter node index returned after := by
  cases parameterRead with
  | object reference _ read =>
    exact parsed_object_source_correct state handlerSet output reference nodeParams key index
      parameter node returned after context handlerRead read nodeRead outputEmpty
  | nullish _ missing =>
    rw [parses_pinned_source, Option.map_some,
      run_nullish_parameter state handlerSet output nodeParams parameterReceiver key index defaultSplitLimit
        node context missing handlerRead nodeRead outputEmpty]
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, AssignmentContract, selected_iff]
    constructor
    · rintro ⟨value, stateEqual⟩
      exact ⟨value.symm, by simpa only [value] using stateEqual.symm⟩
    · rintro ⟨value, stateEqual⟩
      subst returned
      exact ⟨rfl, stateEqual.symm⟩

theorem contract_preserves_frame (before after : State) (output : ObjectRef) (key : JSString)
    (parameter node returned : Value) (index : Int)
    (contract : AssignmentContract before output key parameter node index returned after) :
    after.environment = before.environment ∧ after.heap = before.heap ∧
      ∀ other, other ≠ output → after.objects[other]? = before.objects[other]? := by
  rw [contract.2]
  refine ⟨rfl, rfl, ?_⟩
  intro other different
  exact List.getElem?_set_ne (Ne.symm different)

theorem contract_output_read (before after : State) (output : ObjectRef) (key : JSString)
    (parameter node returned : Value) (index : Int)
    (contract : AssignmentContract before output key parameter node index returned after)
    (outputEmpty : before.objects[output]? = some emptyNullObject) :
    getProperty 32 after.objects output key = .ok returned ∧
      hasOwn after.objects output key = .ok true := by
  rw [contract.2]
  exact null_set_get before.objects output 31 key returned outputEmpty

theorem parsed_source_satisfies (state : State) (handlerSet output nodeParams : ObjectRef)
    (parameterReceiver : Value) (key : JSString) (index : Int) (parameter node : Value)
    (context : LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputEmpty : state.objects[output]? = some emptyNullObject) :
    ∃ returned after,
      (parseAssignment pinnedSource bindings).map (fun program => runAssignment program state) =
        some (.ok (returned, after)) ∧
      AssignmentContract state output key parameter node index returned after := by
  have contract : AssignmentContract state output key parameter node index
      (chosenValue parameter node index) (writtenState state output key (chosenValue parameter node index)) :=
    ⟨(selected_iff _ _ _ _).mpr rfl, rfl⟩
  exact ⟨_, _, (parsed_source_correct state handlerSet output nodeParams parameterReceiver key index
    parameter node _ _ context handlerRead parameterRead nodeRead outputEmpty).mpr contract, contract⟩

def framedWrittenState (before : State) (output : ObjectRef) (object : OrdinaryObject)
    (key : JSString) (value : Value) : State :=
  {before with objects := before.objects.set output (newDataObject object key value)}

def FramedAssignmentContract (before : State) (output : ObjectRef) (object : OrdinaryObject)
    (key : JSString) (parameter node : Value) (index : Int) (returned : Value) (after : State) : Prop :=
  Selected parameter node index returned ∧ after = framedWrittenState before output object key returned

theorem setProperty_null_framed (heap : ObjectHeap) (reference fuel : Nat)
    (object : OrdinaryObject) (key : JSString) (value : Value)
    (found : heap[reference]? = some object) (prototype : object.prototype = none)
    (absent : object.own.lookup key = none) (extensible : object.extensible = true) :
    setProperty (fuel + 1) heap reference key value = .ok (heap.set reference (newDataObject object key value)) := by
  simp [setProperty, lookupProperty, found, prototype, absent, extensible, writeOwnData,
    bind, Except.bind]

theorem absent_key_preserves_prior_properties (object : OrdinaryObject) (key : JSString) (value : Value)
    (absent : object.own.lookup key = none) :
    (newDataObject object key value).own = (key, .data value true true true) :: object.own := by
  have keep : object.own.filter (fun entry => entry.1 != key) = object.own := by
    apply List.filter_eq_self.mpr
    intro entry member
    have different := (List.lookup_eq_none_iff.mp absent) entry member
    have unequal : key ≠ entry.1 := by simpa using different
    simp [Ne.symm unequal]
  simp only [newDataObject, putOwn, keep]

private theorem rhs_supported (state : State) (handlerSet nodeParams : ObjectRef)
    (parameterReceiver : Value) (key : JSString) (index : Int) (limit : Nat) (parameter node : Value)
    (context : LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (parameterRead : ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression 31 limit assignment.value state = .ok (chosenValue parameter node index, state) := by
  cases parameterRead with
  | object reference _ read =>
    exact rhs_selected state handlerSet reference nodeParams key index limit parameter node context read nodeRead
  | nullish _ missing =>
    exact rhs_nullish_parameter state handlerSet nodeParams parameterReceiver key index limit node context missing nodeRead

theorem run_framed (state : State) (handlerSet output nodeParams : ObjectRef)
    (parameterReceiver : Value) (key : JSString) (index : Int) (limit : Nat) (parameter node : Value)
    (object : OrdinaryObject)
    (context : LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputFound : state.objects[output]? = some object) (prototype : object.prototype = none)
    (absent : object.own.lookup key = none) (extensible : object.extensible = true) :
    runAssignment assignment state limit =
      .ok (chosenValue parameter node index,
        framedWrittenState state output object key (chosenValue parameter node index)) := by
  simp only [runAssignment, executeAssignment, evalAssignmentReference, assignment]
  have captured := reference_captured state handlerSet output parameterReceiver nodeParams key index limit context handlerRead
  simp only [assignment] at captured
  rw [captured]
  simp only [Except.bind, bind, pure, Except.pure]
  have selected := rhs_supported state handlerSet nodeParams parameterReceiver key index limit parameter node
    context parameterRead nodeRead
  simp only [assignment] at selected
  rw [selected]
  have write := setProperty_null_framed state.objects output 31 object key
    (chosenValue parameter node index) outputFound prototype absent extensible
  change setProperty 32 state.objects output key (chosenValue parameter node index) = _ at write
  simp [putAssignmentReference, putReference, propertyFuel, write, framedWrittenState, Except.mapError, bind,
    pure, Except.bind, Except.pure]

/-- Populated-output form: prior own properties are allowed. Null prototype,
extensibility and absence of the current key give ordinary data creation while
retaining earlier slots. Establishing this key-absence invariant from Node's
possibleKeys Set and surrounding loop remains outside this fragment proof. -/
theorem parsed_source_correct_framed (state : State) (handlerSet output nodeParams : ObjectRef)
    (parameterReceiver : Value) (key : JSString) (index : Int)
    (parameter node returned : Value) (after : State) (object : OrdinaryObject)
    (context : LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet paramsKey = .ok (.object output))
    (parameterRead : ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (outputFound : state.objects[output]? = some object) (prototype : object.prototype = none)
    (absent : object.own.lookup key = none) (extensible : object.extensible = true) :
    (parseAssignment pinnedSource bindings).map (fun program => runAssignment program state) =
      some (.ok (returned, after)) ↔
      FramedAssignmentContract state output object key parameter node index returned after := by
  rw [parses_pinned_source, Option.map_some,
    run_framed state handlerSet output nodeParams parameterReceiver key index defaultSplitLimit
      parameter node object context handlerRead parameterRead nodeRead outputFound prototype absent extensible]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, FramedAssignmentContract, selected_iff]
  constructor
  · rintro ⟨value, stateEqual⟩
    exact ⟨value.symm, by simpa only [value] using stateEqual.symm⟩
  · rintro ⟨value, stateEqual⟩
    subst returned
    exact ⟨rfl, stateEqual.symm⟩

theorem framed_contract_preserves_state (before after : State) (output : ObjectRef)
    (object : OrdinaryObject) (key : JSString) (parameter node returned : Value) (index : Int)
    (contract : FramedAssignmentContract before output object key parameter node index returned after) :
    after.environment = before.environment ∧ after.heap = before.heap ∧
      ∀ other, other ≠ output → after.objects[other]? = before.objects[other]? := by
  rw [contract.2]
  refine ⟨rfl, rfl, ?_⟩
  intro other different
  exact List.getElem?_set_ne (Ne.symm different)

/-- An admissible manually assembled fragment-entry state: ordinary nodeParams
at1 inherits the legacy accessor at0; optional params at2 is empty/nullproto;
handlerSet at3 points to the empty/nullproto output at4. Reachability of this
state through the entire Node traversal is a separate, unproved obligation. -/
def d1FragmentState : State :=
  {environment := [("handlerSet", .object 3), ("key", .string protoKey),
      ("params", .object 2), ("nodeParams", .object 1), ("i", .number 0)],
   objects := d1Realm [] ++ [emptyNullObject,
      newDataObject emptyNullObject paramsKey (.object 4), emptyNullObject]}

/-- The actual parsed assignment returns/stores an object reference in this
fragment state. This is not a source-connected whole-TrieRouter counterexample. -/
theorem d1_fragment_returns_object :
    (parseAssignment pinnedSource bindings).map (fun program => runAssignment program d1FragmentState) =
      some (.ok (.object 0, writtenState d1FragmentState 4 protoKey (.object 0))) := by
  apply (parsed_source_correct d1FragmentState 3 4 1 (.object 2) protoKey 0 .undefined
    (.object 0) (.object 0) _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
    (.object 2 .undefined rfl) rfl rfl).mpr
  exact ⟨by simp [Selected, Truthy, Nullish], rfl⟩

/-- info: 'HonoLean.Upstream.NodeParamAssignment.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

/--
info: 'HonoLean.Upstream.NodeParamAssignment.parsed_source_correct_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms parsed_source_correct_framed

end HonoLean.Upstream.NodeParamAssignment
