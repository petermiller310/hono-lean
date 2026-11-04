import HonoLean.Upstream.ECMA2025.Objects

namespace HonoLean.Upstream.ECMA2025

open SourceSubset (JSString Value)

private def alpha : JSString := [97, 108, 112, 104, 97]

example : WellFormedHeap (d1Realm []) := by
  simp [WellFormedHeap, d1Realm, objectPrototypeProjection, WellFormedObject,
    protoKey, constructorKey]

example : createNull [] = (0, [emptyNullObject]) := by rfl
example : hasOwn [emptyNullObject] 0 protoKey = .ok false := by rfl
example : getProperty 1 [emptyNullObject] 0 protoKey = .ok .undefined := by rfl

/-- These two reads use the same getter descriptor but different receivers.
The root's prototype is null; the child receives the root's abstract address. -/
example : getProperty 1 (d1Realm []) 0 protoKey = .ok .null := by rfl
example : getProperty 2 (d1Realm []) 1 protoKey = .ok (.object 0) := by rfl
example : setProperty 2 (d1Realm []) 1 protoKey (.string alpha) = .ok (d1Realm []) := by rfl
example : hasOwn (d1Realm []) 1 protoKey = .ok false := by rfl

example : getProperty 2 (d1Realm []) 1 constructorKey = .ok .objectConstructor := by rfl
example : getProperty 2 (d1Realm []) 1 idKey = .ok .undefined := by rfl

private def controlOutcome (key : JSString) : Except ObjectError
    (Except ObjectError Bool × Except ObjectError Value × Except ObjectError Value) := do
  let heap ← setProperty 2 (d1Realm []) 1 key (.string alpha)
  return (hasOwn heap 1 key, getProperty 1 heap 1 key, getProperty 1 heap 0 constructorKey)

/-- Both controls create receiver own data with the captured string. Updating
the child constructor does not change Object.prototype's constructor descriptor. -/
example : controlOutcome idKey =
    .ok (.ok true, .ok (.string alpha), .ok .objectConstructor) := by rfl
example : controlOutcome constructorKey =
    .ok (.ok true, .ok (.string alpha), .ok .objectConstructor) := by rfl

private def nullWithProtoString : ObjectHeap :=
  [newDataObject emptyNullObject protoKey (.string alpha)]

/-- The same UTF-16 key becomes ordinary own data without an inherited setter. -/
example : setProperty 1 [emptyNullObject] 0 protoKey (.string alpha) = .ok nullWithProtoString := by rfl
example : hasOwn nullWithProtoString 0 protoKey = .ok true := by rfl
example : getProperty 1 nullWithProtoString 0 protoKey = .ok (.string alpha) := by rfl

private def ownProtoData : OrdinaryObject :=
  ⟨[(protoKey, .data (.string []) true false false)], some 0, true⟩

/-- An own data descriptor shadows the inherited accessor. Nonconfigurability
does not prevent changing an existing writable data value. -/
example : setProperty 1 [objectPrototypeProjection [], ownProtoData] 1 protoKey (.string alpha) =
    .ok [objectPrototypeProjection [],
      {ownProtoData with own := putOwn protoKey (.data (.string alpha) true false false) ownProtoData.own}] := by rfl

example : setProperty 1 [⟨[(idKey, .data (.string []) false true true)], none, true⟩]
    0 idKey (.string alpha) = .error .notWritable := by rfl
example : setProperty 1 [⟨[], none, false⟩] 0 idKey (.string alpha) = .error .notExtensible := by rfl

/-- Extensibility is checked for new data, but the primitive-RHS setter exits
before prototype mutation would consult extensibility. -/
example : setProperty 2 [objectPrototypeProjection [], ⟨[], some 0, false⟩]
    1 protoKey (.string alpha) =
      .ok [objectPrototypeProjection [], ⟨[], some 0, false⟩] := by rfl

private def descriptorAtOtherName : ObjectHeap :=
  [⟨[(idKey, .accessor .prototype .prototype false true)], none, true⟩,
   ⟨[], some 0, true⟩]

/-- Dispatch follows the descriptor's callable tag rather than hard-coding a
special outcome for a spelling: this accessor is installed at a different key. -/
example : getProperty 2 descriptorAtOtherName 1 idKey = .ok (.object 0) := by rfl
example : setProperty 2 descriptorAtOtherName 1 idKey (.string alpha) = .ok descriptorAtOtherName := by rfl

example : getProperty 1 [⟨[(idKey, .accessor .unsupported .unsupported true true)], none, true⟩]
    0 idKey = .error .unsupported := by rfl
example : getProperty 2 [⟨[], some 0, true⟩] 0 idKey = .error .exhausted := by rfl
example : getProperty 2 [] 0 idKey = .error .invalidReference := by rfl

/-- Only the local property operations behind D1 are composed here. This is
not an extracted router program or a JSON-serialization theorem. -/
private def localCaptureSteps (contents : JSString) : Except ObjectError (ObjectRef × ObjectHeap) := do
  let heap ← setProperty 2 (d1Realm []) 1 protoKey (.string contents)
  let captured ← getProperty 2 heap 1 protoKey
  let fresh := createNull heap
  let heap ← setProperty 1 fresh.2 fresh.1 protoKey captured
  return (fresh.1, heap)

example : (localCaptureSteps alpha).map (fun (reference, heap) =>
    (hasOwn heap reference protoKey, getProperty 1 heap reference protoKey,
      getProperty 2 heap 1 protoKey)) =
      .ok (.ok true, .ok (.object 0), .ok (.object 0)) := by rfl

/-- info: 'HonoLean.Upstream.ECMA2025.proto_string_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proto_string_ignored

end HonoLean.Upstream.ECMA2025
