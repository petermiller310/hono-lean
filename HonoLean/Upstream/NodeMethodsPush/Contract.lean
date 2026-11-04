import HonoLean.Upstream.HandlerRecord.Contract

namespace HonoLean.Upstream.NodeMethodsPush

open SourceSubset ECMA2025

/-- Independent structural append: one new method map after the old dense
reference prefix; fresh key snapshot remains a distinct cell at old heap length.
The record structure and lexical score update are the independent earlier
record contract, not an evaluator-computed desired value. -/
def pushedState (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) : State :=
  {HandlerRecord.constructedState before method handler keys order with
    heap := (before.heap.set methods (prior ++ [.object before.objects.length])) ++ [keys.map Value.string]}

def PushContract (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value)
    (returned : Value) (after : State) : Prop :=
  returned = .number (Int.ofNat (prior.length + 1)) ∧
    after = pushedState before method handler keys order methods prior

/-- State-only projection for the source statement. The expression's push
length is discarded by execute; this is neither a native Completion-value nor
a whole Node.insert return/termination theorem. -/
def StatementContract (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) (after : State) : Prop :=
  after = pushedState before method handler keys order methods prior

/-- Actual lexical private-name identity, receiver brand/slot and old array
contents. These entry facts do not assert any successful final append. Native
class initialization/reachability and standard stable push lookup are separate
interpretation obligations; an ordinary public '#methods' field cannot supply
the lexical stamp or the branded private slot. -/
structure Inputs (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int)
    (owner stamp methods : Nat) (prior : List Value) : Prop
    extends HandlerRecord.Inputs before method handler reference keys order where
  ownerBinding : before.environment.lookup "curNode" = some (.object owner)
  ownerFound : ∃ object, before.objects[owner]? = some object
  privateName : before.privates.names.lookup "methods" = some stamp
  privateSlot : ∃ fields, before.privates.slots.lookup owner = some fields ∧
    fields.lookup stamp = some (.array methods)
  methodsFound : before.heap[methods]? = some prior

/-- Native normal push interpretation needs successful ordinary dense Array
behavior with standard stable push lookup, writable length/slots and relevant
prototype/resource restrictions. The core model theorem is not that adequacy. -/
def NativeBounds (before : State) (method : JSString) (keys : List JSString)
    (order : Int) (prior : List Value) : Prop :=
  HandlerRecord.NativeBounds before method keys order ∧ prior.length < 4294967295

end HonoLean.Upstream.NodeMethodsPush
