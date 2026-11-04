import HonoLean.Upstream.NodeLoopEntry.Program

namespace HonoLean.Upstream.NodeLoopEntry

open SourceSubset ECMA2025

def outerState (before : State) : State :=
  {before with environment := ("i", .number 0) :: withoutBindings before.environment ["i"]}

def innerState (before : State) (length : Nat) : State :=
  {before with environment := [("len2", .number length), ("j", .number 0)] ++
    withoutBindings before.environment ["j", "len2"]}

structure HeapFrame (before after : State) : Prop where
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

/-- Exact new header bindings and all non-environment frames. This relation
does not run the source initializer or assume a completed header. -/
structure EntryContract (before after : State) (names : List String) (bindings : List (String × Value)) : Prop where
  environment : after.environment = bindings ++ withoutBindings before.environment names
  frame : HeapFrame before after

/-- Numeric guard specification from actual current bindings. Saved bounds
are numeric snapshots; no current array-length claim is hidden here. -/
structure GuardContract (before after : State) (counter bound : String)
    (index length : Int) (taken : Bool) : Prop where
  counterBinding : before.environment.lookup counter = some (.number index)
  boundBinding : before.environment.lookup bound = some (.number length)
  outcome : taken = decide (index < length)
  environment : after.environment = before.environment
  frame : HeapFrame before after

structure PrefixResult where
  state : State
  outerTaken : Bool
  innerTaken : Option Bool
  nodeDeclared : Bool

/-- Independent supported-prefix endpoint. Empty search never reaches body
setup. The nonempty case derives both header indices and the saved inner
length before the selected source105 declaration. No full loop body or later
iteration semantics is encoded in this relation. -/
inductive PrefixContract (before : State) (owner identity emptyParams : Nat) (old : Value) (path : JSString) : PrefixResult → Prop where
  | empty (parts : List JSString) (noParts : parts = []) (started entered checked : State)
      (startup : NodeSearchSetup.StartupContract before started owner identity emptyParams old path parts)
      (entry : EntryContract started entered ["i"] [("i", .number 0)])
      (guard : GuardContract entered checked "i" "len" 0 parts.length false) :
      PrefixContract before owner identity emptyParams old path ⟨checked, false, none, false⟩
  | nonempty (parts : List JSString) (hasParts : parts ≠ []) (started outerEntered outerChecked iterated innerEntered innerChecked after : State)
      (startup : NodeSearchSetup.StartupContract before started owner identity emptyParams old path parts)
      (outerEntry : EntryContract started outerEntered ["i"] [("i", .number 0)])
      (outerGuard : GuardContract outerEntered outerChecked "i" "len" 0 parts.length true)
      (iteration : NodeIterationSetup.OuterContract outerChecked iterated parts 0)
      (innerEntry : EntryContract iterated innerEntered ["j", "len2"] [("len2", .number 1), ("j", .number 0)])
      (innerGuard : GuardContract innerEntered innerChecked "j" "len2" 0 1 true)
      (node : NodeIterationSetup.NodeContract innerChecked after [owner] 0) :
      PrefixContract before owner identity emptyParams old path ⟨after, true, some true, true⟩

end HonoLean.Upstream.NodeLoopEntry
