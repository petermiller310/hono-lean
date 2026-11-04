import HonoLean.Upstream.MethodsLoopRegistration.Layout

namespace HonoLean.Upstream.RegistrationHistoryLoop

open SourceSubset ECMA2025

/-- Old read receivers and their closed prototype chains keep their meaning
when registration only appends fresh ordinary objects. -/
theorem old_get_frame (before after : State) (fresh : List OrdinaryObject)
    (objects : after.objects = before.objects ++ fresh)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (reference : Nat) (inside : reference < before.objects.length) (key : JSString) :
    getProperty propertyFuel after.objects reference key =
      getProperty propertyFuel before.objects reference key := by
  symm
  exact NodeParamLoop.getProperty_frame propertyFuel _ _ before.objects.length
    (fun ref bound => by rw [objects, List.getElem?_append_left bound]) closed reference inside key

theorem old_lookup_frame (before after : State) (fresh : List OrdinaryObject)
    (objects : after.objects = before.objects ++ fresh)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (fuel reference : Nat) (inside : reference < before.objects.length) (key : JSString) :
    lookupProperty fuel after.objects reference key = lookupProperty fuel before.objects reference key := by
  symm
  exact NodeParamLoop.lookupProperty_frame fuel _ _ before.objects.length
    (fun ref bound => by rw [objects, List.getElem?_append_left bound]) closed reference inside key

theorem old_parameter_read (before after : State) (fresh : List OrdinaryObject)
    (objects : after.objects = before.objects ++ fresh)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (receiver value : Value) (key : JSString)
    (bound : ∀ reference, receiver = .object reference → reference < before.objects.length)
    (read : NodeParamAssignment.ParameterRead before key receiver value) :
    NodeParamAssignment.ParameterRead after key receiver value := by
  cases read with
  | object reference _ read =>
    apply NodeParamAssignment.ParameterRead.object
    rw [old_get_frame before after fresh objects closed reference (bound reference rfl) key]
    exact read
  | nullish _ missing => exact .nullish _ missing

/-- Every source-created map and record has the preexisting root as parent.
This lemma classifies only appended cells; it does not assume they are already
closed in the completed state. -/
theorem appended_parent (before after : State) (fresh : List OrdinaryObject)
    (objects : after.objects = before.objects ++ fresh)
    (parents : ∀ object ∈ fresh, object.prototype = some 0)
    (reference : Nat) (notOld : before.objects.length ≤ reference)
    (object : OrdinaryObject) (found : after.objects[reference]? = some object) :
    object.prototype = some 0 := by
  rw [objects, List.getElem?_append_right notOld] at found
  exact parents object (List.mem_of_getElem? found)

theorem appended_closed (before after : State) (fresh : List OrdinaryObject)
    (objects : after.objects = before.objects ++ fresh)
    (parents : ∀ object ∈ fresh, object.prototype = some 0)
    (rootBound : 0 < before.objects.length)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length) :
    NodeParamLoop.PrototypeClosed after.objects after.objects.length := by
  intro reference inside object found parent prototype
  have length : before.objects.length ≤ after.objects.length := by rw [objects, List.length_append]; omega
  by_cases old : reference < before.objects.length
  · rw [objects, List.getElem?_append_left old] at found
    exact Nat.lt_of_lt_of_le (closed reference old object found parent prototype) length
  · have root := appended_parent before after fresh objects parents reference (by omega) object found
    have same : parent = 0 := Option.some.inj (prototype.symm.trans root)
    subst parent
    exact Nat.lt_of_lt_of_le rootBound length

end HonoLean.Upstream.RegistrationHistoryLoop
