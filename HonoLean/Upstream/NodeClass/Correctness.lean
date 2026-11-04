import HonoLean.Upstream.NodeClass.Contract

namespace HonoLean.Upstream.NodeClass

open SourceSubset ECMA2025

/-- The selected source windows are parsed independently. The surrounding
public methods/full class are provenance, not silently translated or skipped
inside a purported whole-class parser. -/
def defineSource (before : State) (world : PrivateWorld) (table : PrivateMethodTable) :
    Option (SelectedPrivateClass × PrivateWorld × PrivateMethodTable) := do
  let fields ← parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  definePrivateClass fields [method] before world table

theorem parsed_define_node (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (separate : before.functions.length ≤ table.base) :
    defineSource before world table =
      some (definition before.environment world.nextIdentity (table.base + table.entries.length),
        ⟨world.nextIdentity + 6⟩, extendedTable table before.environment world.nextIdentity) := by
  simp only [defineSource, parses_fields, parses_method]
  exact define_node before world table separate

theorem parsed_instance_satisfies (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (prototypeReady : NodeInitialization.PrototypeReady before prototype)
    (bindings : NodeInitialization.InitializerBindings before environment emptyParams) :
    ∃ owner after,
      (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
        (fun fields => (parsePrivateMethod pinnedMethodSource NodePrivateCall.lexicalBindings
          NodePrivateCall.classPrivateNames).map (fun method => instantiatePrivateClass 64 defaultSplitLimit
            ⟨fields, [method], firstIdentity, environment, firstHandle⟩ prototype before)) =
              some (.ok (owner, after)) ∧
      InstanceContract before after prototype firstIdentity firstHandle owner emptyParams := by
  refine ⟨before.objects.length, instanceState before prototype environment firstIdentity firstHandle emptyParams,
    ?_, instance_contract before prototype environment firstIdentity firstHandle emptyParams⟩
  rw [parses_fields, Option.bind_some, parses_method, Option.map_some]
  exact congrArg some (instantiate_node before prototype environment firstIdentity firstHandle emptyParams
    fresh prototypeReady bindings)

def initializedState (before : State) (prototype : Option Nat) (firstIdentity firstHandle : Nat) : State :=
  classActivation (instanceState (NodeInitialization.preambleState before) prototype
    (NodeInitialization.preambleState before).environment firstIdentity firstHandle (.object before.objects.length)) firstIdentity

def initializedOwner (before : State) : Nat := (NodeInitialization.preambleState before).objects.length

/-- Actual preamble/selected private declarations derive both the history Seed
and private-call Callable. No desired method closure, read handle, slot, empty
array or zero counter is a premise. The import/helper/realm/prototype context
and explicit threaded reservation protocol remain interpretation boundaries. -/
theorem parsed_initialized_satisfies (before : State) (prototype : Option Nat)
    (world : PrivateWorld) (table : PrivateMethodTable)
    (helper : NodeInitialization.HelperBinding before)
    (separate : before.functions.length ≤ table.base)
    (rootFound : ∃ root, before.objects[0]? = some root)
    (fresh : (NodeInitialization.preambleState before).privates.slots.lookup
      (NodeInitialization.preambleState before).objects.length = none)
    (prototypeReady : NodeInitialization.PrototypeReady (NodeInitialization.preambleState before) prototype) :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (NodeInitialization.preambleEntry before)) =
        some (.ok (.normal (NodeInitialization.preambleState before))) ∧
    defineSource (NodeInitialization.preambleState before) world table =
      some (definition (NodeInitialization.preambleState before).environment world.nextIdentity
        (table.base + table.entries.length), ⟨world.nextIdentity + 6⟩,
        extendedTable table (NodeInitialization.preambleState before).environment world.nextIdentity) ∧
    instantiatePrivateClass 64 defaultSplitLimit
      (definition (NodeInitialization.preambleState before).environment world.nextIdentity
        (table.base + table.entries.length)) prototype (NodeInitialization.preambleState before) =
          .ok (initializedOwner before, instanceState (NodeInitialization.preambleState before) prototype
            (NodeInitialization.preambleState before).environment world.nextIdentity
            (table.base + table.entries.length) (.object before.objects.length)) ∧
    RegistrationHistory.Seed (initializedState before prototype world.nextIdentity (table.base + table.entries.length))
      (initializedOwner before) world.nextIdentity before.heap.length 0 [] ∧
    NodePrivateCall.Callable (initializedState before prototype world.nextIdentity (table.base + table.entries.length))
      (extendedTable table (NodeInitialization.preambleState before).environment world.nextIdentity)
      (closure (NodeInitialization.preambleState before).environment world.nextIdentity)
      (initializedOwner before) (table.base + table.entries.length) := by
  have contract := instance_contract (NodeInitialization.preambleState before) prototype
    (NodeInitialization.preambleState before).environment world.nextIdentity
    (table.base + table.entries.length) (.object before.objects.length)
  refine ⟨?_, parsed_define_node (NodeInitialization.preambleState before) world table separate,
    instantiate_node _ _ _ _ _ _ fresh prototypeReady
      (NodeInitialization.preamble_initializer_bindings before helper),
    initialized_seed before _ prototype world.nextIdentity _ (initializedOwner before) rootFound contract,
    initialized_callable (NodeInitialization.preambleState before) _ prototype
      (NodeInitialization.preambleState before).environment world.nextIdentity (initializedOwner before)
      (.object before.objects.length) table separate contract⟩
  rw [parses_preamble, Option.map_some, NodeInitialization.run_preamble before helper]

def initialNodeWorld (before : State) (table : PrivateMethodTable) : PrivateWorld :=
  initialPrivateClassWorld (NodeInitialization.preambleState before) table

theorem initial_definition_fresh (before : State) (table : PrivateMethodTable) (name : String) (identity : Nat)
    (member : (name, identity) ∈ (definition (NodeInitialization.preambleState before).environment
      (initialNodeWorld before table).nextIdentity (table.base + table.entries.length)).names) :
    identity ∉ storedPrivateIdentities (NodeInitialization.preambleState before) := by
  intro used
  have lower := (class_name_range _ name identity member).1
  have smaller := initialPrivateClassWorld_state_fresh (NodeInitialization.preambleState before) table identity used
  change (initialNodeWorld before table).nextIdentity ≤ identity at lower
  change identity < (initialNodeWorld before table).nextIdentity at smaller
  omega

/-- The initial cursor also excludes identities captured by represented method
closures for definitions that have not produced any instance. Threading remains
required for earlier unrepresented/external definitions. -/
theorem initial_definition_table_fresh (before : State) (table : PrivateMethodTable)
    (name : String) (identity : Nat)
    (member : (name, identity) ∈ (definition (NodeInitialization.preambleState before).environment
      (initialNodeWorld before table).nextIdentity (table.base + table.entries.length)).names)
    (oldClosure : PrivateMethodClosure) (present : oldClosure ∈ table.entries)
    (oldName : String) (oldIdentity : Nat) (used : (oldName, oldIdentity) ∈ oldClosure.privateNames) :
    identity ≠ oldIdentity := by
  have lower := (class_name_range _ name identity member).1
  have smaller := initialPrivateClassWorld_closure_fresh (NodeInitialization.preambleState before) table
    oldClosure oldName oldIdentity present used
  change (initialNodeWorld before table).nextIdentity ≤ identity at lower
  change oldIdentity < (initialNodeWorld before table).nextIdentity at smaller
  omega

/-- info: 'HonoLean.Upstream.NodeClass.parsed_initialized_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_initialized_satisfies

end HonoLean.Upstream.NodeClass
