import HonoLean.Literal.Reference
import HonoLean.Literal.Trie

namespace HonoLean.Literal
namespace Trie

theorem select_append (entries : List Entry) (entry : Entry) (method : Method) :
    select (entries ++ [entry]) method =
      select entries method ++ (if Accepts entry.selector method then [entryMatch entry []] else []) := by
  by_cases accepted : Accepts entry.selector method
  · simp [select, List.filterMap_append, accepted]
  · simp [select, List.filterMap_append, accepted]

theorem entryResults_cons (entry : Entry) (component : Component) (rest : List Component) (suffix : Bool)
    (method : Method) (segment : String) (remaining : Path) :
    entryResults entry (component :: rest) suffix method (segment :: remaining) =
      match consume component segment with
      | none => []
      | some bindings => (entryResults entry rest suffix method remaining).map (prefixMatch bindings) := by
  by_cases accepted : Accepts entry.selector method
  · cases step : consume component segment <;> cases tail : capture rest suffix remaining <;>
      simp [entryResults, capture, step, tail, accepted, prefixMatch, entryMatch]
  · cases consume component segment <;> simp [entryResults, accepted]

@[simp] theorem candidates_empty (method : Method) (path : Path) : candidates empty method path = [] := by
  cases path <;> simp [empty, candidates, select]

theorem flatMap_alterChild (children : List (Component × Trie)) (key : Component)
    (change : Trie → Trie) (view : Component → Trie → List Match) (extra : List Match)
    (emptyView : view key empty = [])
    (effect : ∀ tree, (view key (change tree)).Perm (view key tree ++ extra)) :
    ((alterChild children key change).flatMap (fun edge => view edge.1 edge.2)).Perm
      (children.flatMap (fun edge => view edge.1 edge.2) ++ extra) := by
  induction children with
  | nil => simpa [alterChild, emptyView] using effect empty
  | cons edge rest ih =>
    rcases edge with ⟨label, tree⟩
    by_cases same : label = key
    · subst label
      simp only [alterChild, ↓reduceIte, List.flatMap_cons]
      have first := (effect tree).append_right (rest.flatMap (fun edge => view edge.1 edge.2))
      have move := (List.perm_append_comm :
        (extra ++ rest.flatMap (fun edge => view edge.1 edge.2)).Perm
          (rest.flatMap (fun edge => view edge.1 edge.2) ++ extra)).append_left (view key tree)
      exact first.trans (by simpa [List.append_assoc] using move)
    · simpa [alterChild, same, List.append_assoc] using ih.append_left (view label tree)

theorem candidates_insert (tree : Trie) (pattern : List Component) (suffix : Bool) (entry : Entry)
    (method : Method) (path : Path) :
    (candidates (insert tree pattern suffix entry) method path).Perm
      (candidates tree method path ++ entryResults entry pattern suffix method path) := by
  induction pattern generalizing tree path with
  | nil =>
    cases tree with
    | node terminal wildcard children =>
      cases suffix with
      | false =>
        cases path <;> simp [insert, candidates, select_append, entryResults, capture, List.append_assoc]
      | true =>
        cases path <;>
          simp only [insert, ↓reduceIte, candidates, select_append, entryResults, capture]
        all_goals
          by_cases accepted : Accepts entry.selector method
          · simp only [accepted, ↓reduceIte, Option.toList_some, List.map_cons, List.map_nil]
            simpa only [List.append_assoc] using
              (List.perm_append_comm (l₁ := [entryMatch entry []])).append_left (select wildcard method)
          · simp [accepted]
  | cons component rest ih =>
    cases tree with
    | node terminal wildcard children =>
      cases path with
      | nil => simp [insert, candidates, entryResults, capture]
      | cons segment remaining =>
        have changed :
            ((alterChild children component (fun subtree => insert subtree rest suffix entry)).flatMap
              (fun edge => branch edge.1 edge.2 method segment remaining)).Perm
            (children.flatMap (fun edge => branch edge.1 edge.2 method segment remaining) ++
              entryResults entry (component :: rest) suffix method (segment :: remaining)) := by
          apply flatMap_alterChild children component (fun subtree => insert subtree rest suffix entry)
            (fun key subtree => branch key subtree method segment remaining)
            (entryResults entry (component :: rest) suffix method (segment :: remaining))
          · cases step : consume component segment <;> simp [branch, step]
          · intro subtree
            cases step : consume component segment with
            | none => simp [branch, step, entryResults_cons]
            | some bindings =>
              have mapped := (ih subtree remaining).map (prefixMatch bindings)
              simpa [branch, step, List.map_append, entryResults_cons] using mapped
        simpa only [insert, candidates, branch, List.append_assoc] using
          changed.append_left (select wildcard method)

theorem referenceFrom_cons (start : Nat) (route : Route) (rest : List Route)
    (method : Method) (path : Path) :
    referenceFrom start (route :: rest) method path =
      entryResults (entryOf start route) route.path route.suffix method path ++
        referenceFrom (start + 1) rest method path := by
  by_cases accepted : Accepts route.selector method
  · cases captured : capture route.path route.suffix path <;>
      simp [referenceFrom, routeCapture, entryResults, entryOf, entryMatch, result, accepted, captured]
  · simp [referenceFrom, routeCapture, entryResults, entryOf, accepted]

theorem candidates_buildFrom (routes : List Route) (next : Nat) (tree : Trie)
    (method : Method) (path : Path) :
    (candidates (buildFrom routes next tree) method path).Perm
      (candidates tree method path ++ referenceFrom next routes method path) := by
  induction routes generalizing next tree with
  | nil => simp [buildFrom, referenceFrom]
  | cons route rest ih =>
    simp only [buildFrom]
    have inserted := (candidates_insert tree route.path route.suffix (entryOf next route) method path).append_right
      (referenceFrom (next + 1) rest method path)
    exact (ih (next + 1) (insert tree route.path route.suffix (entryOf next route))).trans
      (by simpa [referenceFrom_cons, List.append_assoc] using inserted)

theorem candidates_build (routes : List Route) (method : Method) (path : Path) :
    (candidates (build routes) method path).Perm (referenceLookup routes method path) := by
  simpa [build, referenceLookup] using candidates_buildFrom routes 0 empty method path

theorem lookup_build (routes : List Route) (method : Method) (path : Path) :
    lookup (build routes) method path = referenceLookup routes method path := by
  have perm := (List.mergeSort_perm (candidates (build routes) method path) byRegistration).trans
    (candidates_build routes method path)
  have strict := referenceFrom_strict 0 routes method path
  have sorted : ((candidates (build routes) method path).mergeSort byRegistration).Pairwise
      (fun left right => left.registration ≤ right.registration) := by
    apply (List.pairwise_mergeSort (le := byRegistration) ?_ ?_ _).imp
    · intro left right related
      simpa [byRegistration] using related
    · intro left middle right first second
      simp only [byRegistration, decide_eq_true_eq] at *
      omega
    · intro left right
      simp only [byRegistration, Bool.or_eq_true, decide_eq_true_eq]
      omega
  apply List.Perm.eq_of_pairwise (le := fun left right => left.registration ≤ right.registration)
    ?_ sorted ?_ perm
  · intro left right leftMember rightMember first second
    apply strict_keys_injective strict (perm.subset leftMember) rightMember
    omega
  · exact strict.imp (fun less => Nat.le_of_lt less)

theorem lookup_build_follows_rules (routes : List Route) (method : Method) (path : Path) :
    Matches 0 routes method path (lookup (build routes) method path) := by
  rw [lookup_build]
  exact reference_follows_rules 0 routes method path

theorem lookup_build_iff_rules (routes : List Route) (method : Method) (path : Path)
    (output : List Match) :
    lookup (build routes) method path = output ↔ Matches 0 routes method path output := by
  rw [lookup_build, rules_iff_reference]
  exact eq_comm

theorem lookup_strict (routes : List Route) (method : Method) (path : Path) :
    (lookup (build routes) method path).Pairwise
      (fun left right => left.registration < right.registration) := by
  rw [lookup_build]
  exact referenceFrom_strict 0 routes method path

theorem lookup_capture_properties (routes : List Route) (method : Method) (path : Path)
    (item : Match) (member : item ∈ lookup (build routes) method path) :
    (item.params.map Prod.fst).Nodup ∧
      (∀ binding ∈ item.params, binding.2 ≠ "") ∧
      ∃ route ∈ routes, item.handler = route.handler ∧
        item.params.map Prod.fst = parameterNames route.path ∧ Captures route.path route.suffix path item.params := by
  obtain ⟨route, registered, accepted, captured, label⟩ :=
    matches_member_capture (lookup_build_follows_rules routes method path) member
  exact ⟨captures_unique_keys captured, captures_nonempty captured,
    route, registered, label, captures_keys captured, captured⟩

/-- info: 'HonoLean.Literal.Trie.lookup_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_build

/-- info: 'HonoLean.Literal.Trie.lookup_build_iff_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_build_iff_rules

/-- info: 'HonoLean.Literal.Trie.lookup_capture_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_capture_properties

end Trie
end HonoLean.Literal
