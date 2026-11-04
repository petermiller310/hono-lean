import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.LoopChecks

set_option maxRecDepth 65536

private def loopSource : String :=
  "for (let i = 0, len = keys.length; i < len; i++) {\n const key = keys[i]\n output.push(key)\n}"

private def bindings : List String := ["keys", "output", "i", "len", "key"]

private def loopProgram : List Stmt := [
  .countedFor [("i", .number 0), ("len", .property (.variable "keys") [108,101,110,103,116,104])]
    (.compare .less (.variable "i") (.variable "len")) "i"
    [.declare "key" (.index (.variable "keys") (.variable "i")),
     .evaluate (.call (.variable "output") "push" [.variable "key"])]]

example : parseBlock loopSource bindings = some loopProgram := by cbv

private def frame : List (String × Value) :=
  [("keys", .array 0), ("output", .array 1),
   ("i", .string [105]), ("len", .boolean false), ("key", .number (-9))]

-- Outer names are shadowed and restored, and each iteration gets its own key.
example : runBlock 40 loopProgram {environment := frame, heap := [[.string [97], .string [98]], []]} =
    .ok (.normal {environment := frame, heap := [[.string [97], .string [98]], [.string [97], .string [98]]]}) := by cbv
example : runBlock 40 loopProgram {environment := frame, heap := [[], []]} =
    .ok (.normal {environment := frame, heap := [[], []]}) := by cbv

private def many : List Value := (List.range 40).map (fun n => .number (Int.ofNat n))

-- The budget is supplied by the caller; the loop has no fixed32-key cutoff.
example : runBlock 80 loopProgram {environment := frame, heap := [many, []]} =
    .ok (.normal {environment := frame, heap := [many, many]}) := by cbv
example : runBlock 20 loopProgram {environment := frame, heap := [many, []]} =
    .error .exhausted := by cbv

-- Snapshot len once: appending to the source array inside the loop does not
-- extend the iteration count. The original two-element length remains bound.
private def savedLengthSource : String :=
  "for (let i = 0, len = keys.length; i < len; i++) { keys.push(i) }"

example : (parseBlock savedLengthSource ["keys"]).map
    (fun program => runBlock 40 program {environment := [("keys", .array 0)], heap := [[.number 9, .number 8]]}) =
      some (.ok (.normal {environment := [("keys", .array 0)], heap := [[.number 9, .number 8, .number 0, .number 1]]})) := by cbv

-- Sequential header initialization sees the new i, rather than caller i.
example : (parseBlock "for (let i = 0, len = i; i < len; i++) { output.push(i) }" ["output", "i"]).map
    (fun program => runBlock 40 program {environment := [("output", .array 0), ("i", .number 7)], heap := [[]]}) =
      some (.ok (.normal {environment := [("output", .array 0), ("i", .number 7)], heap := [[]]})) := by cbv

private def helper : NoArgFunction :=
  ⟨"make", .call (.variable "Object") "create" [.null]⟩

example : parseNoArg "export const make = () => Object.create(null)" = some helper := by cbv

private def caller : State :=
  {environment := [("make", .function 0), ("Object", .string [120])],
   functions := [⟨helper, []⟩]}

-- The helper's lexical Object is independent of the caller's shadowing binding.
-- A successful call restores the caller while retaining allocation effects.
example : evalExpression 32 defaultSplitLimit (.invoke (.variable "make") []) caller =
    .ok (.object 0, {caller with objects := [ECMA2025.emptyNullObject]}) := by cbv
example : truthy (.function 0) = true := by cbv

-- Push appends the same object reference; it does not clone the referred object.
example : intrinsic defaultSplitLimit (.array 0) "push" [.object 0]
    {heap := [[.object 0]], objects := [ECMA2025.emptyNullObject]} =
      .ok (.number 2, {heap := [[.object 0, .object 0]], objects := [ECMA2025.emptyNullObject]}) := by cbv

private def rejected : List String := [
  "for (let i = i, len = 1; i < len; i++) {}",
  "for (let i = 0, len = len; i < len; i++) {}",
  "for (let i = 0, i = 1; i < i; i++) {}",
  "for (let i = 0, len = 1; i < len; other++) {}",
  "for (let i = 0, len = 1; i < len; i\n++) {}",
  "for (let i = 0, len = 1; i < len; i++) { const key = key }",
  "for (let i = 0, len = 1; i < len; i++) { output.push(key); const key = 'x' }",
  "for (let Object = 0; Object < 1; Object++) {}"]

example : rejected.all (fun source => (parseBlock source bindings).isNone) = true := by cbv

end HonoLean.Upstream.SourceSubset.LoopChecks
