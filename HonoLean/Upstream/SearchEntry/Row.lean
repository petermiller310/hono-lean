import HonoLean.Upstream.SearchEntry.Collector

namespace HonoLean.Upstream.SearchEntry

open SourceSubset ECMA2025

def rowProgram : List Stmt :=
  [.declare "m" (.index (.privateProperty (.variable "node") "methods") (.variable "i"))]
def rowBindings : List String := ["node", "i"]

set_option maxRecDepth 32768 in
theorem parses_row : parseBlock pinnedRowSource rowBindings ["methods"] = some rowProgram := by cbv

structure RowInputs (before : State) (owner stamp methods index : Nat) (entries : List Value) (row : Value) : Prop where
  nodeBinding : before.environment.lookup "node" = some (.object owner)
  indexBinding : before.environment.lookup "i" = some (.number (Int.ofNat index))
  ownerFound : ∃ object, before.objects[owner]? = some object
  privateName : before.privates.names.lookup "methods" = some stamp
  privateSlot : ∃ fields, before.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
  methodsFound : before.heap[methods]? = some entries
  rowRead : entries[index]?.getD .undefined = row

theorem run_row (before : State) (owner stamp methods index : Nat) (entries : List Value) (row : Value)
    (inputs : RowInputs before owner stamp methods index entries row) :
    execute 32 defaultSplitLimit rowProgram {before with environment := withoutBindings before.environment ["m"]} =
      .ok (.normal (boundState before "m" row)) := by
  obtain ⟨object, ownerFound⟩ := inputs.ownerFound
  obtain ⟨fields, fieldsFound, slotFound⟩ := inputs.privateSlot
  have nodeBinding := lookup_withoutBindings before.environment ["m"] "node" (by decide)
  have indexBinding := lookup_withoutBindings before.environment ["m"] "i" (by decide)
  simp [rowProgram, execute, evalExpression, lookupVariable, nodeBinding, indexBinding,
    inputs.nodeBinding, inputs.indexBinding, privateGet, inputs.privateName, ownerFound,
    fieldsFound, slotFound, readProperty, inputs.methodsFound, inputs.rowRead, boundState,
    bind, pure, Except.bind, Except.pure]

theorem parsed_row_correct (before after : State) (owner stamp methods index : Nat) (entries : List Value) (row : Value)
    (inputs : RowInputs before owner stamp methods index entries row) :
    (parseBlock pinnedRowSource rowBindings ["methods"]).map (fun source => execute 32 defaultSplitLimit source
      {before with environment := withoutBindings before.environment ["m"]}) = some (.ok (.normal after)) ↔
        RowContract before after row := by
  rw [parses_row, Option.map_some, run_row before owner stamp methods index entries row inputs]
  simp [RowContract, eq_comm]

theorem parsed_row_satisfies (before : State) (owner stamp methods index : Nat) (entries : List Value) (row : Value)
    (inputs : RowInputs before owner stamp methods index entries row) :
    ∃ after,
      (parseBlock pinnedRowSource rowBindings ["methods"]).map (fun source => execute 32 defaultSplitLimit source
        {before with environment := withoutBindings before.environment ["m"]}) = some (.ok (.normal after)) ∧
      RowContract before after row := by
  refine ⟨boundState before "m" row, ?_, rfl⟩
  rw [parses_row, Option.map_some, run_row before owner stamp methods index entries row inputs]

end HonoLean.Upstream.SearchEntry
