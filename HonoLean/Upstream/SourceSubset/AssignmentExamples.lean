import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.AssignmentChecks

open ECMA2025

set_option maxRecDepth 65536

private def key : JSString := [107]

private def initial : State :=
  {environment := [("out", .object 0), ("key", .string key)], objects := [emptyNullObject]}

private def bound : List String := ["out", "key", "a", "b", "c", "params", "i", "nodeParams", "handlerSet"]

def assignmentSource : String :=
  "handlerSet.params[key] =\n  params?.[key] && !i ? params[key] : (nodeParams[key] ?? params?.[key])"

example : (parseAssignment assignmentSource bound).isSome = true := by cbv

example : [Value.undefined, .null, .boolean false, .number 0, .string []].map truthy =
    [false, false, false, false, false] := by cbv
example : [Value.boolean true, .number (-1), .string [0], .array 0, .object 0, .objectConstructor].map truthy =
    [true, true, true, true, true, true] := by cbv
example : [Value.undefined, .null, .boolean false, .number 0, .string []].map isNullish =
    [true, true, false, false, false] := by cbv

-- A false && operand returns that original value and never allocates RHS.
example : (parseAssignment "out[key] = '' && Object.create(null)" bound).map
    (fun program => runAssignment program initial) =
      some (.ok (.string [], {initial with objects := [newDataObject emptyNullObject key (.string [])]})) := by cbv

-- Nullish coalescing retains every non-nullish falsy value unchanged.
example : (parseAssignment "out[key] = false ?? Object.create(null)" bound).map
    (fun program => runAssignment program initial) =
      some (.ok (.boolean false, {initial with objects := [newDataObject emptyNullObject key (.boolean false)]})) := by cbv
example : (parseAssignment "out[key] = 0 ?? Object.create(null)" bound).map
    (fun program => runAssignment program initial) =
      some (.ok (.number 0, {initial with objects := [newDataObject emptyNullObject key (.number 0)]})) := by cbv
example : (parseAssignment "out[key] = null ?? Object.create(null)" bound).map
    (fun program => runAssignment program initial) =
      some (.ok (.object 1, {initial with objects :=
        [newDataObject emptyNullObject key (.object 1), emptyNullObject]})) := by cbv

-- The LHS allocation is captured as object0, then RHS allocates object1, then
-- PutValue writes object1 through the saved object0 reference. Reordering or
-- re-evaluating the LHS changes this complete observable state.
theorem reference_order :
    (parseAssignment "Object.create(null)[key] = Object.create(null)" ["key"]).map
      (fun program => runAssignment program {environment := [("key", .string key)]}) =
        some (.ok (.object 1,
          {environment := [("key", .string key)], objects :=
            [newDataObject emptyNullObject key (.object 1), emptyNullObject]})) := by cbv

-- Nullish optional access does not evaluate even an effectful key expression.
example : (parseNoArg "export const f = () => null?.[Object.create(null)]").map
    (fun program => runNoArg program {}) = some (.ok (.undefined, {})) := by cbv

-- Grouping changes the short-circuit extent, rather than silently extending
-- an optional chain across a following ordinary computed access.
example : (parseAssignment "out[key] = (null?.[key])[key]" bound).map
    (fun program => runAssignment program initial) = some (.error .unsupported) := by cbv

-- `undefined` remains an ordinary declared identifier in this subset, so a
-- lexical binding is respected instead of being replaced with a literal tag.
example : (parseAssignment "out[key] = undefined" ["out", "key", "undefined"]).map
    (fun program => runAssignment program
      {initial with environment := ("undefined", .string [115]) :: initial.environment}) =
        some (.ok (.string [115],
          {environment := ("undefined", .string [115]) :: initial.environment,
           objects := [newDataObject emptyNullObject key (.string [115])]})) := by cbv

-- Precise object-model rejection survives the interpreter wrapper.
private def readOnly : State :=
  {initial with objects := [⟨[(key, .data (.number 7) false true true)], none, true⟩]}

example : (parseAssignment "out[key] = 1" bound).map
    (fun program => runAssignment program readOnly) =
      some (.error (.objectError .notWritable)) := by cbv
example : readProperty (.object 7) (.string key) {} =
    .error (.objectError .invalidReference) := by cbv

-- Outer receiver/key validation and destination descriptor selection wait for
-- the RHS. Its own read failure therefore wins over either unsupported base
-- validation, unsupported key coercion, or an eventual non-writable target.
private def badReadState : State :=
  {readOnly with environment := ("bad", .object 7) :: initial.environment}

example : (parseAssignment "null[key] = bad[key]" ["key", "bad"]).map
    (fun program => runAssignment program badReadState) =
      some (.error (.objectError .invalidReference)) := by cbv
example : (parseAssignment "out[Object.create(null)] = bad[key]" ["out", "key", "bad"]).map
    (fun program => runAssignment program badReadState) =
      some (.error (.objectError .invalidReference)) := by cbv
example : (parseAssignment "out[key] = bad[key]" ["out", "key", "bad"]).map
    (fun program => runAssignment program badReadState) =
      some (.error (.objectError .invalidReference)) := by cbv

-- An inherited setter can ignore the write; assignment still returns its RHS,
-- rather than re-reading the inherited getter's different object value.
private def setterState : State :=
  {environment := [("out", .object 1), ("key", .string protoKey)], objects := d1Realm []}

example : (parseAssignment "out[key] = 'x'" ["out", "key"]).map
    (fun program => runAssignment program setterState) =
      some (.ok (.string [120], setterState)) := by cbv

-- Object property keys are already primitive strings. Numeric-key coercion
-- is deliberately unsupported, rather than silently converting 0 to "0".
example : (parseAssignment "out[0] = 1" bound).map
    (fun program => runAssignment program initial) = some (.error .unsupported) := by cbv

def rejectedAssignments : List String := [
  "out[key] = a ?? b && c", "out[key] = a && b ?? c",
  "out[key] = a ?? b || c", "out[key] = a || b ?? c",
  "out?.[key] = a", "out[key] = params? .[key]", "out[key] = params?\n.[key]",
  "out[key] = params?.[key][key]", "out[key] = params?.[key].other",
  "out[key] = params?.[key]?.[key]", "out[key] = unbound",
  "out[key] = undefined", "out[key] = a; out[key] = b",
  "out[key] = a ? b", "out[key] = a ??= b"]

example : rejectedAssignments.all (fun source => (parseAssignment source bound).isNone) = true := by cbv

def groupedAssignments : List String := [
  "out[key] = (a ?? b) && c", "out[key] = a && (b ?? c)",
  "out[key] = a ?? (b && c)", "out[key] = (a && b) ?? c",
  "out[key] = params?. [key]", "out[key] = (params?.[key])[key]"]

example : groupedAssignments.all (fun source => (parseAssignment source bound).isSome) = true := by cbv

example : parseAssignment "out[key] = a ?? b ?? c" bound =
    some ⟨.index (.variable "out") (.variable "key"),
      .nullish (.nullish (.variable "a") (.variable "b")) (.variable "c")⟩ := by cbv

example : parseAssignment "out[key] = a && b && c" bound =
    some ⟨.index (.variable "out") (.variable "key"),
      .logicalAnd (.logicalAnd (.variable "a") (.variable "b")) (.variable "c")⟩ := by cbv

-- New grouping support must not erase JavaScript call-continuation/ASI rules.
example : (parseString "export const f = (url: string): string => { return url\n(url) }").isNone = true := by cbv
example : (parseString "export const f = (url: string): string => { const Object = Object.create(null); return url }").isNone = true := by cbv

end HonoLean.Upstream.SourceSubset.AssignmentChecks
