import HonoLean.Upstream.NodePartOffsets.Source

namespace HonoLean.Upstream.NodePartOffsets

open SourceSubset ECMA2025

def initialOffset (path : JSString) : Nat := if path[0]? = some 47 then 1 else 0
def weights (parts : List JSString) : Nat := (parts.map (fun field => field.length + 1)).sum
def offsetAt (path : JSString) (parts : List JSString) (index : Nat) : Nat := initialOffset path + weights (parts.take index)
def tableValues (path : JSString) (parts : List JSString) (count : Nat) : List Value :=
  (List.range count).map (fun index => .number (offsetAt path parts index))

/-- Prefix-length specification independent of the source loop evaluator. -/
structure CumulativeTable (path : JSString) (parts : List JSString) (values : List Value) : Prop where
  length : values.length = parts.length
  index : ∀ index, index < parts.length → values[index]? = some (.number (offsetAt path parts index))

structure FreshInputs (before : State) (partsRef : Nat) (path : JSString) (parts : List JSString)
    (front back : List (String × Value)) : Prop where
  reference : before.environment = front ++ ("partOffsets", .null) :: back
  first : front.lookup "partOffsets" = none
  pathBinding : before.environment.lookup "path" = some (.string path)
  partsBinding : before.environment.lookup "parts" = some (.array partsRef)
  partsFound : before.heap[partsRef]? = some (parts.map Value.string)
  savedLength : before.environment.lookup "len" = some (.number parts.length)
  partsBound : parts.length ≤ maximumArrayLength
  exactBound : (initialOffset path + weights parts : Int) ≤ Arithmetic.maximumSafeInteger

def updatedEnvironment (before : State) (front back : List (String × Value)) : List (String × Value) :=
  front ++ ("partOffsets", .array before.heap.length) :: back
def loopState (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString) (count : Nat) : State :=
  {before with
    environment := [("p", .number count), ("offset", .number (offsetAt path parts count))] ++
      withoutBindings (withoutBindings (updatedEnvironment before front back) ["offset"]) ["p"]
    heap := before.heap ++ [tableValues path parts count]}
def prepareState (before : State) (front back : List (String × Value)) (path : JSString) (parts : List JSString) : State :=
  {before with
    environment := updatedEnvironment before front back
    heap := before.heap ++ [tableValues path parts parts.length]}
def sliceState (before : State) (output : JSString) : State :=
  {before with environment := ("restPathString", .string output) :: before.environment}

structure PreparedContract (before after : State) (path : JSString) (parts : List JSString) : Prop where
  initial : ∃ partsRef front back, FreshInputs before partsRef path parts front back
  reference : ∃ front back, before.environment = front ++ ("partOffsets", .null) :: back ∧ front.lookup "partOffsets" = none ∧
    after.environment = front ++ ("partOffsets", .array before.heap.length) :: back
  table : ∃ values, after.heap = before.heap ++ [values] ∧ CumulativeTable path parts values
  fresh : before.heap[before.heap.length]? = none
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

def sliceArgument : Value → Option Int
  | .number value => some value
  | .undefined => some 0
  | _ => none

/-- A cache hit depends only on its actual index Get and supported slice
argument. No parts/len/layout/alignment or correct-cache premise is present. -/
structure CachedInputs (before : State) (cache : Nat) (values : List Value) (path : JSString) (index : Nat) (start : Int) : Prop where
  cacheBinding : before.environment.lookup "partOffsets" = some (.array cache)
  cacheFound : before.heap[cache]? = some values
  pathBinding : before.environment.lookup "path" = some (.string path)
  indexBinding : before.environment.lookup "i" = some (.number index)
  actualStart : sliceArgument (values[index]?.getD .undefined) = some start
  indexBound : index < maximumArrayLength
  lengthBound : values.length ≤ maximumArrayLength
  exact : Arithmetic.SafeInteger start

structure CachedContract (before after : State) (cache : Nat) (values : List Value) (path : JSString) (index : Nat) (start : Int) : Prop where
  initial : CachedInputs before cache values path index start
  environment : after.environment = ("restPathString", .string (stringSlice path start)) :: before.environment
  cacheBinding : after.environment.lookup "partOffsets" = some (.array cache)
  cacheFound : after.heap[cache]? = some values
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

end HonoLean.Upstream.NodePartOffsets
