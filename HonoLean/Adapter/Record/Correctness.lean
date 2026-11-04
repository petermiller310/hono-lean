import HonoLean.Adapter.Record.Spec
import HonoLean.Adapter.Method.Correctness
import HonoLean.Adapter.Pattern.Correctness

namespace HonoLean.Adapter.RecordText
open Literal

private def selectorResult (text : String) : Except Error Selector :=
  if text == "ALL" then .ok .all
  else (parseMethod .invalidRoute text).map Selector.exact

private theorem bind_ok_iff {α β : Type} (input : Except Error α)
    (next : α → Except Error β) (output : β) :
    input.bind next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | error error => simp [Except.bind]
  | ok value => simp [Except.bind]

private theorem selector_iff (text : String) (selector : Selector) :
    selectorResult text = .ok selector ↔ SelectorDenotes text selector := by
  by_cases all : text = "ALL"
  · subst text
    cases selector with
    | all => simp [selectorResult, SelectorDenotes]
    | exact method =>
      simp [selectorResult, SelectorDenotes, MethodText.Denotes, MethodText.Spelling]
  · cases selector with
    | all =>
      cases parsed : parseMethod .invalidRoute text <;>
        simp [selectorResult, all, parsed, SelectorDenotes, Except.map]
    | exact method =>
      constructor
      · intro parsed
        simp only [selectorResult, show (text == "ALL") = false by simp [all],
          Bool.false_eq_true, ↓reduceIte] at parsed
        cases result : parseMethod .invalidRoute text with
        | error error => simp [result, Except.map] at parsed
        | ok actual =>
          have equal : actual = method := by simpa [result, Except.map] using parsed
          subst actual
          exact (MethodText.parseMethod_iff _ _ _).mp result
      · intro grammar
        have parsed := (MethodText.parseMethod_iff .invalidRoute text method).mpr grammar
        simp [selectorResult, all, parsed, Except.map]

/-- Exact selector, pattern structure, and opaque label are preserved together. -/
theorem parseRoute_iff (input : TextRoute) (route : Literal.Route) :
    parseRoute input = .ok route ↔ RouteDenotes input route := by
  have assemble : parseRoute input = (selectorResult input.method).bind (fun selector =>
    (parsePattern input.pattern).bind (fun pattern =>
      .ok (Literal.Route.mk selector pattern.path pattern.suffix input.handler pattern.valid))) := by
    by_cases all : input.method = "ALL"
    · simp [parseRoute, selectorResult, all, bind, pure, Except.bind, Except.pure]
    · cases parsed : parseMethod .invalidRoute input.method <;>
        simp [parseRoute, selectorResult, all, parsed, bind, pure,
          Except.bind, Except.pure, Except.map]
  rw [assemble]
  rw [bind_ok_iff]
  constructor
  · rintro ⟨selector, selected, rest⟩
    obtain ⟨pattern, parsed, result⟩ := (bind_ok_iff _ _ _).mp rest
    cases result
    exact ⟨(selector_iff _ _).mp selected, (PatternText.parsePattern_iff _ _).mp parsed, rfl⟩
  · rintro ⟨selected, pattern, handler⟩
    refine ⟨route.selector, (selector_iff _ _).mpr selected, ?_⟩
    apply (bind_ok_iff _ _ _).mpr
    let parsed : ParsedPattern := ⟨route.path, route.suffix, route.valid⟩
    refine ⟨parsed, (PatternText.parsePattern_iff _ _).mpr pattern, ?_⟩
    cases route
    simp only at handler
    cases handler
    rfl

theorem parseRequest_iff (input : TextRequest) (request : Method × HonoLean.Path) :
    parseRequest input = .ok request ↔ RequestDenotes input request := by
  change (parseMethod .invalidRequest input.method).bind (fun method =>
    (parsePath input.path).bind (fun path => .ok (method, path))) = .ok request ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨method, parsedMethod, rest⟩
    obtain ⟨path, parsedPath, result⟩ := (bind_ok_iff _ _ _).mp rest
    cases result
    exact ⟨(MethodText.parseMethod_iff _ _ _).mp parsedMethod,
      (PathText.parsePath_iff _ _).mp parsedPath⟩
  · rintro ⟨method, path⟩
    refine ⟨request.1, (MethodText.parseMethod_iff _ _ _).mpr method, ?_⟩
    apply (bind_ok_iff _ _ _).mpr
    exact ⟨request.2, (PathText.parsePath_iff _ _).mpr path, by cases request; rfl⟩

theorem route_complete {input : TextRoute} (grammar : RouteSpelling input) :
    ∃ route, parseRoute input = .ok route := by
  obtain ⟨pattern, parsed⟩ := (PatternText.accepts_iff input.pattern).mpr grammar.2
  have patternGrammar := (PatternText.parsePattern_iff _ _).mp parsed
  have selector : ∃ selector, SelectorDenotes input.method selector := by
    rcases grammar.1 with all | exact
    · exact ⟨.all, all⟩
    · obtain ⟨method, _, name⟩ := MethodText.complete .invalidRoute exact
      exact ⟨.exact method, exact, name⟩
  obtain ⟨selector, selectorGrammar⟩ := selector
  let route : Literal.Route := ⟨selector, pattern.path, pattern.suffix, input.handler, pattern.valid⟩
  exact ⟨route, (parseRoute_iff _ _).mpr ⟨selectorGrammar, patternGrammar, rfl⟩⟩

theorem route_accepts_iff (input : TextRoute) :
    (∃ route, parseRoute input = .ok route) ↔ RouteSpelling input := by
  constructor
  · rintro ⟨route, parsed⟩
    obtain ⟨selector, pattern, _⟩ := (parseRoute_iff _ _).mp parsed
    refine ⟨?_, route.path, route.suffix, pattern⟩
    cases selected : route.selector with
    | all => exact .inl (by simpa only [SelectorDenotes, selected] using selector)
    | exact method =>
      simp only [SelectorDenotes, selected] at selector
      exact .inr selector.1
  · exact route_complete

theorem request_complete {input : TextRequest} (grammar : RequestSpelling input) :
    ∃ request, parseRequest input = .ok request := by
  obtain ⟨method, parsedMethod, _⟩ := MethodText.complete .invalidRequest grammar.1
  obtain ⟨path, pathGrammar⟩ := grammar.2
  exact ⟨(method, path), (parseRequest_iff _ _).mpr
    ⟨(MethodText.parseMethod_iff _ _ _).mp parsedMethod, pathGrammar⟩⟩

theorem request_accepts_iff (input : TextRequest) :
    (∃ request, parseRequest input = .ok request) ↔ RequestSpelling input := by
  constructor
  · rintro ⟨request, parsed⟩
    obtain ⟨method, path⟩ := (parseRequest_iff _ _).mp parsed
    exact ⟨method.1, request.2, path⟩
  · exact request_complete

theorem route_error_kind {input : TextRoute} {error : Error}
    (rejected : parseRoute input = .error error) : error.kind = .invalidRoute := by
  unfold parseRoute at rejected
  split at rejected
  next =>
    cases pattern : parsePattern input.pattern with
    | error failure =>
      have equal : failure = error := by
        simpa [pattern, bind, pure, Except.bind, Except.pure] using rejected
      cases equal
      exact PatternText.error_kind pattern
    | ok pattern => simp [pattern, bind, pure, Except.bind, Except.pure] at rejected
  next =>
    cases method : parseMethod .invalidRoute input.method with
    | error failure =>
      have equal : failure = error := by
        simpa [method, bind, pure, Except.bind, Except.pure] using rejected
      cases equal
      exact MethodText.error_kind method
    | ok method =>
      cases pattern : parsePattern input.pattern with
      | error failure =>
        have equal : failure = error := by
          simpa [method, pattern, bind, pure, Except.bind, Except.pure] using rejected
        cases equal
        exact PatternText.error_kind pattern
      | ok pattern => simp [method, pattern, bind, pure, Except.bind, Except.pure] at rejected

theorem request_error_kind {input : TextRequest} {error : Error}
    (rejected : parseRequest input = .error error) : error.kind = .invalidRequest := by
  unfold parseRequest at rejected
  cases method : parseMethod .invalidRequest input.method with
  | error failure =>
    have equal : failure = error := by
      simpa [method, bind, pure, Except.bind, Except.pure] using rejected
    cases equal
    exact MethodText.error_kind method
  | ok method =>
    cases path : parsePath input.path with
    | error failure =>
      have equal : failure = error := by
        simpa [method, path, bind, pure, Except.bind, Except.pure] using rejected
      cases equal
      exact PathText.error_kind path
    | ok path => simp [method, path, bind, pure, Except.bind, Except.pure] at rejected

theorem route_rejects_iff (input : TextRoute) :
    (∃ error, parseRoute input = .error error ∧ error.kind = .invalidRoute) ↔
      ¬ RouteSpelling input := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨route, parsed⟩ := route_complete grammar
    rw [rejected] at parsed
    contradiction
  · intro outside
    cases parsed : parseRoute input with
    | ok route => exact False.elim (outside ((route_accepts_iff _).mp ⟨route, parsed⟩))
    | error error => exact ⟨error, rfl, route_error_kind parsed⟩

theorem request_rejects_iff (input : TextRequest) :
    (∃ error, parseRequest input = .error error ∧ error.kind = .invalidRequest) ↔
      ¬ RequestSpelling input := by
  constructor
  · rintro ⟨error, rejected, _⟩ grammar
    obtain ⟨request, parsed⟩ := request_complete grammar
    rw [rejected] at parsed
    contradiction
  · intro outside
    cases parsed : parseRequest input with
    | ok request => exact False.elim (outside ((request_accepts_iff _).mp ⟨request, parsed⟩))
    | error error => exact ⟨error, rfl, request_error_kind parsed⟩

theorem handler_preserved {input : TextRoute} {route : Literal.Route}
    (parsed : parseRoute input = .ok route) : route.handler = input.handler :=
  ((parseRoute_iff _ _).mp parsed).2.2

/-- info: 'HonoLean.Adapter.RecordText.parseRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parseRoute_iff

/-- info: 'HonoLean.Adapter.RecordText.parseRequest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parseRequest_iff

/-- info: 'HonoLean.Adapter.RecordText.route_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms route_accepts_iff

/-- info: 'HonoLean.Adapter.RecordText.request_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms request_accepts_iff

/-- info: 'HonoLean.Adapter.RecordText.route_rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms route_rejects_iff

/-- info: 'HonoLean.Adapter.RecordText.request_rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms request_rejects_iff

end HonoLean.Adapter.RecordText
