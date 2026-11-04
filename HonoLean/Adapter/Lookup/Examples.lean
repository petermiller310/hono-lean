import HonoLean.Adapter.Lookup.Correctness

namespace HonoLean.Adapter.LookupText
open Literal

private def get : Method := ⟨"GET", by decide⟩
private def exactRoute : Literal.Route := literalRoute (.exact get) ["students", "new"] "same"
private def parameterRoute : Literal.Route :=
  {selector := .exact get, path := [.literal "students", .parameter "id"],
   handler := "same", valid := by decide}
private def suffixRoute : Literal.Route :=
  {selector := .all, path := [.literal "students"], suffix := true,
   handler := "all", valid := by decide}
private def inputs : List TextRoute := [
  ⟨"GET", "/students/new", "same"⟩, ⟨"GET", "/students/:id", "same"⟩,
  ⟨"ALL", "/students/*", "all"⟩]
private def routes : List Literal.Route := [exactRoute, parameterRoute, suffixRoute]
private def request : TextRequest := ⟨"GET", "/students/new"⟩
private def expected : List Match := [
  {registration := 0, handler := "same"},
  {registration := 1, handler := "same", params := [("id", "new")]},
  {registration := 2, handler := "all"}]

private theorem table : BuildText.TableDenotes inputs routes := by
  dsimp only [inputs, routes]
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  all_goals apply (RecordText.parseRoute_iff _ _).mp
  all_goals simp only [parseRoute, parsePattern, patternTexts, rootedPieces,
    String.toList_split_char]
  all_goals rfl

private theorem built : build inputs = .ok (Router.build routes) :=
  (BuildText.build_iff _ _).mpr ⟨routes, table, rfl⟩

private theorem requestMeaning : RecordText.RequestDenotes request (get, ["students", "new"]) := by
  dsimp only [request]
  apply (RecordText.parseRequest_iff _ _).mp
  simp only [parseRequest, parsePath, String.toList_split_char]
  rfl

/-- Full public text construction and lookup retain both same-label occurrences,
their branch-local captures, and the ALL wildcard in registration order. -/
example : ∃ router, build inputs = .ok router ∧ lookup router request = .ok expected := by
  apply (build_lookup_iff _ _ _).mpr
  refine ⟨routes, (get, ["students", "new"]), table, requestMeaning, ?_⟩
  apply rules_iff_reference.mpr
  decide +kernel

private def bad : TextRoute := ⟨"GET", "/:id/:id", "bad"⟩
private def good : TextRoute := ⟨"GET", "/students/:id", "same"⟩
private def old : Router := Router.build routes

private theorem rejected_keeps : (registerStep old bad).1 = old := by
  dsimp only [bad]
  simp only [registerStep, register, parseRoute, parsePattern, patternTexts,
    rootedPieces, String.toList_split_char]
  rfl

private theorem registered : register old good = .ok (Router.register old parameterRoute) := by
  dsimp only [good]
  simp only [register, parseRoute, parsePattern, patternTexts, rootedPieces,
    String.toList_split_char]
  rfl

/-- A rejected append consumes no ordinal; the next valid duplicate is #3.
The earlier router is still the one used by `built` above. -/
example :
    let afterBad := (registerStep old bad).1
    let updated := (registerStep afterBad good).1
    lookup old request = .ok expected ∧
    lookup updated request = .ok (expected ++ [
      {registration := 3, handler := "same", params := [("id", "new")]}]) ∧
      updated.nextOrdinal = 4 := by
  dsimp only
  rw [rejected_keeps, RegistrationText.step_success registered]
  constructor
  · apply (lookup_build_iff built _ _).mpr
    refine ⟨routes, (get, ["students", "new"]), table, requestMeaning, ?_⟩
    apply rules_iff_reference.mpr
    decide +kernel
  constructor
  · apply (lookup_iff
      (RegistrationText.register_state (RegistrationText.StateDenotes.of_build built) registered)
      _ _).mpr
    refine ⟨routes ++ [parameterRoute], (get, ["students", "new"]), ?_, requestMeaning, ?_⟩
    · apply (BuildText.parseRoutes_iff _ _).mp
      change ([⟨"GET", "/students/new", "same"⟩, ⟨"GET", "/students/:id", "same"⟩,
        ⟨"ALL", "/students/*", "all"⟩, ⟨"GET", "/students/:id", "same"⟩] : List TextRoute).mapM
          parseRoute = .ok [exactRoute, parameterRoute, suffixRoute, parameterRoute]
      simp only [List.mapM_cons, parseRoute, parsePattern, patternTexts,
        rootedPieces, String.toList_split_char]
      rfl
    · apply rules_iff_reference.mpr
      decide +kernel
  · rfl

/-- A valid miss succeeds with []; malformed input produces a categorized error. -/
example : lookup old ⟨"GET", "/missing"⟩ = .ok [] := by
  apply (lookup_build_iff built _ _).mpr
  refine ⟨routes, (get, ["missing"]), table, ?_, ?_⟩
  · apply (RecordText.parseRequest_iff _ _).mp
    simp only [parseRequest, parsePath, String.toList_split_char]
    rfl
  · apply rules_iff_reference.mpr
    decide +kernel

example : ([⟨"ALL", "/"⟩, ⟨"GET", "/students/"⟩] : List TextRequest).all (fun input =>
    match lookup old input with
    | .error error => error.kind == .invalidRequest
    | .ok _ => false) = true := by
  simp only [lookup, parseRequest, parsePath, String.toList_split_char]
  rfl

end HonoLean.Adapter.LookupText
