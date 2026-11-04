import HonoLean.Upstream.CreateNullObject.Correctness
import HonoLean.Upstream.NodeParamLoop.Correctness

namespace HonoLean.Upstream.D1

open SourceSubset ECMA2025

inductive TransferError where
  | source (error : EvalError)
  | object (error : ObjectError)
  | invalidSource | wrongReturn
  deriving Repr

structure Observation where
  temporaryHasOwn : Bool
  readValue : Value
  outputHasOwn : Bool
  outputValue : Value
  outputPrototype : Option ObjectRef
  descriptor : Option PropertyDescriptor
  deriving Repr

/-- The parsed complete chosen-handler block, invoking the parsed allocation
helper through its lexical function binding. Temporary capture, the chosen
handler/key-array entry and route reachability remain explicit model setup.
Observation.readValue samples the temporary lookup after the block; it is not
an event trace or a separately returned assignment result. -/
def captureTransfer (key contents : JSString) : Except TransferError Observation := do
  let heap ← (setProperty 4 (d1Realm []) 1 key (.string contents)).mapError .object
  let temporaryHasOwn ← (hasOwn heap 1 key).mapError .object
  let helper ← match parseNoArg CreateNullObject.pinnedSource with
    | some helper => pure helper
    | none => throw .invalidSource
  let state : State :=
    {objects := heap ++ [emptyNullObject,
        newDataObject {prototype := some 0} NodeParamLoop.possibleKeysKey (.array 0)]
     heap := [[.string key], []]
     environment := [("handlerSet", .object 3), ("handlerSets", .array 1),
       ("params", .object 2), ("nodeParams", .object 1), ("createNullObject", .function 0)]
     functions := [⟨helper, []⟩]}
  let block ← match parseBlock NodeParamLoop.pinnedSource NodeParamLoop.bindings with
    | some block => pure block
    | none => throw .invalidSource
  let completed ← (runBlock 65 block state).mapError .source
  let state ← match completed with
    | .normal state => pure state
    | .returned _ _ => throw .wrongReturn
  let heap := state.objects
  let reference ← match ← (getProperty 4 heap 3 NodeParamAssignment.paramsKey).mapError .object with
    | .object reference => pure reference
    | _ => throw .wrongReturn
  let readValue ← (getProperty 4 heap 1 key).mapError .object
  let outputHasOwn ← (hasOwn heap reference key).mapError .object
  let outputValue ← (getProperty 4 heap reference key).mapError .object
  let output ← match heap[reference]? with
    | some output => pure output
    | none => throw (.object .invalidReference)
  return ⟨temporaryHasOwn, readValue, outputHasOwn, outputValue,
    output.prototype, output.own.lookup key⟩

/-- Every string RHS is ignored by the inherited setter; the inherited getter
reads the receiver's unchanged prototype. Null-prototype output then stores
that object reference as its own data property. This is a local mechanism
theorem, not a source-connected counterexample for the entire TrieRouter. -/
theorem proto_transfer (contents : JSString) :
    captureTransfer protoKey contents =
      .ok ⟨false, .object 0, true, .object 0, none,
        some (.data (.object 0) true true true)⟩ := by
  unfold captureTransfer
  rw [CreateNullObject.parses_pinned_source]
  rw [NodeParamLoop.parses_pinned_source]
  cbv

/-- The model mechanism contradicts a string-only capture claim nonvacuously.
The observed endpoint is an object reference, whatever string was assigned. -/
theorem proto_capture_not_string (contents : JSString) :
    (captureTransfer protoKey contents).map Observation.outputValue ≠ .ok (.string contents) := by
  rw [proto_transfer]
  intro impossible
  cases impossible

example : captureTransfer idKey [97, 108, 112, 104, 97] =
    .ok ⟨true, .string [97, 108, 112, 104, 97], true, .string [97, 108, 112, 104, 97],
      none, some (.data (.string [97, 108, 112, 104, 97]) true true true)⟩ := by
  unfold captureTransfer
  rw [CreateNullObject.parses_pinned_source]
  rw [NodeParamLoop.parses_pinned_source]
  cbv

example : captureTransfer constructorKey [97, 108, 112, 104, 97] =
    .ok ⟨true, .string [97, 108, 112, 104, 97], true, .string [97, 108, 112, 104, 97],
      none, some (.data (.string [97, 108, 112, 104, 97]) true true true)⟩ := by
  unfold captureTransfer
  rw [CreateNullObject.parses_pinned_source]
  rw [NodeParamLoop.parses_pinned_source]
  cbv

/-- info: 'HonoLean.Upstream.D1.proto_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proto_transfer

end HonoLean.Upstream.D1
