import HonoLean.Literal.Spec

namespace HonoLean.Literal

theorem capture_follows_rules {pattern suffix path params} (h : capture pattern suffix path = some params) :
    Captures pattern suffix path params := by
  induction pattern generalizing path params with
  | nil =>
    cases suffix with
    | false =>
      cases path with
      | nil =>
        simp [capture] at h
        subst params
        exact Captures.nil
      | cons segment remaining => simp [capture] at h
    | true =>
      have same : params = [] := by cases path <;> simpa [capture] using h.symm
      subst params
      exact Captures.suffix
  | cons component rest ih =>
    cases path with
    | nil => simp [capture] at h
    | cons segment remaining =>
      cases component with
      | literal text =>
        by_cases same : text = segment
        · simp [capture, consume, same] at h
          exact Captures.literal same (ih h)
        · simp [capture, consume, same] at h
      | parameter name =>
        by_cases nonempty : segment ≠ ""
        · cases tailResult : capture rest suffix remaining with
          | none => simp [capture, consume, nonempty, tailResult] at h
          | some bindings =>
            simp [capture, consume, nonempty, tailResult] at h
            subst params
            exact Captures.parameter nonempty (ih tailResult)
        · simp [capture, consume, nonempty] at h

theorem rules_determine_capture {pattern suffix path params} (h : Captures pattern suffix path params) :
    capture pattern suffix path = some params := by
  induction h with
  | nil => rfl
  | @suffix remaining => cases remaining <;> rfl
  | literal same tail ih => simp [capture, consume, same, ih]
  | parameter nonempty tail ih => simp [capture, consume, nonempty, ih]

theorem capture_iff {pattern suffix path params} :
    capture pattern suffix path = some params ↔ Captures pattern suffix path params :=
  ⟨capture_follows_rules, rules_determine_capture⟩

theorem capture_unique {pattern suffix path left right}
    (first : Captures pattern suffix path left) (second : Captures pattern suffix path right) : left = right :=
  Option.some.inj ((rules_determine_capture first).symm.trans (rules_determine_capture second))

theorem captures_keys {pattern suffix path params} (h : Captures pattern suffix path params) :
    params.map Prod.fst = parameterNames pattern := by
  induction h with
  | nil => rfl
  | suffix => rfl
  | literal same tail ih => simpa [parameterNames] using ih
  | @parameter suffix name segment rest remaining params nonempty tail ih =>
    simpa [parameterNames] using congrArg (List.cons name) ih

theorem captures_nonempty {pattern suffix path params} (h : Captures pattern suffix path params) :
    ∀ binding ∈ params, binding.2 ≠ "" := by
  induction h with
  | nil => simp
  | suffix => simp
  | literal same tail ih => exact ih
  | parameter nonempty tail ih =>
    intro binding member
    rcases List.mem_cons.mp member with equal | member
    · simpa [equal] using nonempty
    · exact ih binding member

theorem captures_unique_keys {route : Route} {path params} (h : Captures route.path route.suffix path params) :
    (params.map Prod.fst).Nodup := by
  rw [captures_keys h]
  exact route.valid.2

theorem routeCapture_iff {route method path params} :
    routeCapture route method path = some params ↔
      Accepts route.selector method ∧ Captures route.path route.suffix path params := by
  by_cases accepted : Accepts route.selector method
  · simp [routeCapture, accepted, capture_iff]
  · simp [routeCapture, accepted]

def referenceFrom (start : Nat) (routes : List Route)
    (method : Method) (path : Path) : List Match :=
  match routes with
  | [] => []
  | route :: rest =>
    match routeCapture route method path with
    | none => referenceFrom (start + 1) rest method path
    | some params => result start route params :: referenceFrom (start + 1) rest method path

def referenceLookup (routes : List Route) (method : Method) (path : Path) : List Match :=
  referenceFrom 0 routes method path

theorem reference_follows_rules (start : Nat) (routes : List Route) (method : Method) (path : Path) :
    Matches start routes method path (referenceFrom start routes method path) := by
  induction routes generalizing start with
  | nil => exact Matches.nil start method path
  | cons route rest ih =>
    cases captured : routeCapture route method path with
    | none =>
      have absent : ¬ ∃ params, Accepts route.selector method ∧ Captures route.path route.suffix path params := by
        rintro ⟨params, h⟩
        have := routeCapture_iff.mpr h
        simp [captured] at this
      simpa [referenceFrom, captured] using Matches.miss absent (ih (start + 1))
    | some params =>
      obtain ⟨accepted, follows⟩ := routeCapture_iff.mp captured
      simpa [referenceFrom, captured] using Matches.hit accepted follows (ih (start + 1))

theorem rules_determine_reference {start routes method path output}
    (h : Matches start routes method path output) :
    output = referenceFrom start routes method path := by
  induction h with
  | nil => rfl
  | hit accepted captured tail ih =>
    have present := routeCapture_iff.mpr ⟨accepted, captured⟩
    simp [referenceFrom, present, ih]
  | @miss start route rest method path output absent tail ih =>
    have missing : routeCapture route method path = none := by
      cases h : routeCapture route method path with
      | none => rfl
      | some params => exact False.elim (absent ⟨params, routeCapture_iff.mp h⟩)
    simp [referenceFrom, missing, ih]

theorem rules_iff_reference {start routes method path output} :
    Matches start routes method path output ↔ output = referenceFrom start routes method path := by
  constructor
  · exact rules_determine_reference
  · intro equal
    rw [equal]
    exact reference_follows_rules start routes method path

theorem referenceFrom_lower {start routes method path item}
    (member : item ∈ referenceFrom start routes method path) : start ≤ item.registration := by
  induction routes generalizing start with
  | nil => simp [referenceFrom] at member
  | cons route rest ih =>
    cases captured : routeCapture route method path with
    | none =>
      simp only [referenceFrom, captured] at member
      have := ih member
      omega
    | some params =>
      simp only [referenceFrom, captured] at member
      rcases List.mem_cons.mp member with equal | member
      · subst item
        simp [result]
      · have := ih member
        omega

theorem referenceFrom_strict (start : Nat) (routes : List Route) (method : Method) (path : Path) :
    (referenceFrom start routes method path).Pairwise
      (fun left right => left.registration < right.registration) := by
  induction routes generalizing start with
  | nil => simp [referenceFrom]
  | cons route rest ih =>
    cases captured : routeCapture route method path with
    | none => simpa [referenceFrom, captured] using ih (start + 1)
    | some params =>
      simp only [referenceFrom, captured, List.pairwise_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro item member
      have bound := referenceFrom_lower member
      simp only [result]
      omega

theorem strict_keys_injective {items : List Match}
    (ordered : items.Pairwise (fun left right => left.registration < right.registration))
    {left right : Match} (leftMember : left ∈ items) (rightMember : right ∈ items)
    (same : left.registration = right.registration) : left = right := by
  induction items with
  | nil => simp at leftMember
  | cons head tail ih =>
    rcases List.mem_cons.mp leftMember with leftHead | leftTail
    · subst left
      rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · exact rightHead.symm
      · have less := (List.pairwise_cons.mp ordered).1 right rightTail
        omega
    · rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · subst right
        have less := (List.pairwise_cons.mp ordered).1 left leftTail
        omega
      · exact ih ordered.tail leftTail rightTail

theorem matches_member_capture {start routes method path output item}
    (follows : Matches start routes method path output) (member : item ∈ output) :
    ∃ route ∈ routes, Accepts route.selector method ∧
      Captures route.path route.suffix path item.params ∧ item.handler = route.handler := by
  induction follows with
  | nil => simp at member
  | @hit start route rest method path params output accepted captured tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst item
      exact ⟨route, List.mem_cons_self, accepted, captured, rfl⟩
    · obtain ⟨found, foundMember, accepted, captured, label⟩ := ih member
      exact ⟨found, List.mem_cons_of_mem route foundMember, accepted, captured, label⟩
  | @miss start route rest method path output absent tail ih =>
    obtain ⟨found, foundMember, accepted, captured, label⟩ := ih member
    exact ⟨found, List.mem_cons_of_mem route foundMember, accepted, captured, label⟩

/-- Unique keys turn the canonical association list into a finite map. -/
theorem params_lookup_iff {params : Params} (unique : (params.map Prod.fst).Nodup)
    (key value : String) : params.lookup key = some value ↔ (key, value) ∈ params := by
  induction params with
  | nil => simp
  | cons binding rest ih =>
    rcases binding with ⟨name, text⟩
    have distinct := List.nodup_cons.mp unique
    by_cases same : key = name
    · subst key
      have absent : (name, value) ∉ rest := by
        intro member
        exact distinct.1 (List.mem_map.mpr ⟨(name, value), member, rfl⟩)
      simp [absent, eq_comm]
    · have different : (key == name) = false := by simpa using same
      simp only [List.lookup_cons, different]
      simpa [same] using ih distinct.2

def SameParams (left right : Params) : Prop := ∀ key, left.lookup key = right.lookup key

theorem params_permutation_same_map {left right : Params}
    (leftUnique : (left.map Prod.fst).Nodup) (rightUnique : (right.map Prod.fst).Nodup)
    (reordered : left.Perm right) : SameParams left right := by
  intro key
  apply Option.ext
  intro value
  rw [params_lookup_iff leftUnique, params_lookup_iff rightUnique]
  exact reordered.mem_iff

end HonoLean.Literal
