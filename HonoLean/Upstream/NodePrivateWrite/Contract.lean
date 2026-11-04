import HonoLean.Upstream.NodePrivateWrite.Program
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.NodePrivateWrite

open SourceSubset ECMA2025

/-- One existing DATA slot, identified by the source class's lexical name.
The kind is a stored tag, independent of the stored Value or TypeScript type. -/
structure Writable (before : State) (owner identity : Nat) (old : Value) : Prop where
  scope : before.privates.names.lookup "params" = some identity
  allocated : ∃ object, before.objects[owner]? = some object
  data : ∃ elements, before.privates.elements.lookup owner = some elements ∧
    elements.lookup identity = some (.data old)

/-- Independent first-entry replacement. Every leading and trailing entry, including
all other DATA/METHOD tags, remains exactly the same. -/
def DataReplacement (identity : Nat) (old value : Value)
    (before after : List (Nat × PrivateElement)) : Prop :=
  ∃ leading trailing, identity ∉ leading.map Prod.fst ∧
    before = leading ++ (identity, .data old) :: trailing ∧
    after = leading ++ (identity, .data value) :: trailing

/-- An owner-list leading/trailing witnesses preservation of all other private
owners and their element tags, rather than only equal public read values. -/
def PrivateReplacement (owner identity : Nat) (old value : Value)
    (before after : List (Nat × List (Nat × PrivateElement))) : Prop :=
  ∃ leading trailing oldFields newFields, owner ∉ leading.map Prod.fst ∧
    before = leading ++ (owner, oldFields) :: trailing ∧
    after = leading ++ (owner, newFields) :: trailing ∧
    DataReplacement identity old value oldFields newFields

structure WriteContract (before after : State) (owner identity : Nat) (old value returned : Value) : Prop where
  result : returned = value
  privateChange : PrivateReplacement owner identity old value before.privates.elements after.privates.elements
  names : after.privates.names = before.privates.names
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  objects : after.objects = before.objects
  heap : after.heap = before.heap
  functions : after.functions = before.functions
  sets : after.sets = before.sets

structure ResetReads (before : State) (owner : Nat) (value : Value) : Prop where
  receiver : before.thisValue = .object owner
  binding : before.environment.lookup "emptyParams" = some value

structure PropagationReads (before : State) (owner : Nat) (value : Value) : Prop where
  target : before.environment.lookup "nextNode" = some (.object owner)
  source : ∃ receiver, before.environment.lookup "node" = some receiver ∧
    privateGet receiver "params" before = .ok value

structure ParameterReads (before : State) (owner : Nat) (value : Value) : Prop where
  target : before.environment.lookup "child" = some (.object owner)
  binding : before.environment.lookup "params" = some value

end HonoLean.Upstream.NodePrivateWrite
