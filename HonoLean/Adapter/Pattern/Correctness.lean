import HonoLean.Adapter.Pattern.Spec
import HonoLean.Adapter.Path.Correctness

namespace HonoLean.Adapter.PatternText
open Literal

theorem validName_iff (text : String) : validName text = true ↔ Name text := by
  cases spelling : text.toList with
  | nil => simp [validName, Name, spelling]
  | cons first rest =>
    simp [validName, Name, spelling, NameStart, nameStart, Bool.or_eq_true,
      Bool.and_eq_true, List.all_eq_true, or_assoc]

theorem component_iff (text : String) (item : Component) :
    parseComponent text = .ok item ↔ ComponentText text item := by
  constructor
  · intro parsed
    unfold parseComponent at parsed
    split at parsed
    next rest spelling =>
      dsimp only at parsed
      split at parsed
      next valid =>
        cases parsed
        constructor
        · apply String.toList_inj.mp
          simp [String.toList_append, spelling]
        · exact (validName_iff _).mp valid
      next => contradiction
    next =>
      split at parsed
      next valid =>
        cases parsed
        exact ⟨rfl, (PathText.validSegment_iff _).mp valid⟩
      next => contradiction
  · cases item with
    | literal segment =>
      rintro ⟨rfl, valid⟩
      unfold parseComponent
      split
      next rest spelling =>
        have member : ':' ∈ text.toList := by rw [spelling]; simp
        have := valid.2 ':' member
        simp [PathText.Character] at this
      next => simp only [ite_eq_left ((PathText.validSegment_iff _).mpr valid)]; rfl
    | parameter name =>
      rintro ⟨rfl, valid⟩
      simp [parseComponent, String.toList_append, (validName_iff _).mpr valid]
      rfl

private theorem component_not_star {text : String} {item : Component}
    (grammar : ComponentText text item) : text ≠ "*" := by
  intro equal
  have parsed := (component_iff text item).mpr grammar
  subst text
  simp [parseComponent, validSegment, nameStart] at parsed

theorem pieces_iff (texts : List String) (items : List Component) (suffix : Bool) :
    parsePatternPieces texts = .ok (items, suffix) ↔ Pieces texts items suffix := by
  induction texts generalizing items suffix with
  | nil =>
    constructor
    · intro parsed
      simp only [parsePatternPieces, Except.ok.injEq, Prod.mk.injEq] at parsed
      rcases parsed with ⟨rfl, rfl⟩
      exact .exact
    · intro grammar; cases grammar; rfl
  | cons text texts ih =>
    constructor
    · intro parsed
      unfold parsePatternPieces at parsed
      split at parsed
      next wildcard =>
        have conditions := Bool.and_eq_true_iff.mp wildcard
        have head : text = "*" := by simpa using conditions.1
        have tail : texts = [] := by simpa using conditions.2
        subst text; subst texts
        simp only [Except.ok.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        exact .wildcard
      next =>
        dsimp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map] at parsed
        cases head : parseComponent text with
        | error error => simp [head] at parsed
        | ok item =>
          cases tail : parsePatternPieces texts with
          | error error => simp [head, tail] at parsed
          | ok result =>
            rcases result with ⟨rest, ending⟩
            simp only [head, tail, Except.ok.injEq,
              Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            exact .component ((component_iff _ _).mp head) ((ih _ _).mp tail)
    · intro grammar
      cases grammar with
      | wildcard => simp [parsePatternPieces]
      | component head tail =>
        have different := component_not_star head
        unfold parsePatternPieces
        simp only [show (text == "*" && texts.isEmpty) = false by simp [different], Bool.false_eq_true, ↓reduceIte]
        rw [(component_iff _ _).mpr head, (ih _ _).mpr tail]
        rfl

private theorem Name.no_slash {text : String} (valid : Name text) :
    '/' ∉ text.toList := by
  cases spelling : text.toList with
  | nil => simp
  | cons first rest =>
    simp only [Name, spelling] at valid
    intro member
    rcases List.mem_cons.mp member with equal | member
    · subst first; simpa [NameStart] using valid.1
    · have := valid.2 '/' member
      simp [NameStart] at this

private theorem component_good {text : String} {item : Component}
    (grammar : ComponentText text item) : text ≠ "" ∧ '/' ∉ text.toList := by
  cases item with
  | literal segment =>
    rcases grammar with ⟨rfl, valid⟩
    exact ⟨valid.1, valid.no_slash⟩
  | parameter name =>
    rcases grammar with ⟨rfl, valid⟩
    simp [String.toList_append, valid.no_slash]

private theorem Pieces.good {texts : List String} {items : List Component} {suffix : Bool}
    (grammar : Pieces texts items suffix) :
    ∀ text ∈ texts, text ≠ "" ∧ '/' ∉ text.toList := by
  induction grammar with
  | exact => simp
  | wildcard => simp
  | component head _ ih =>
    intro text member
    rcases List.mem_cons.mp member with rfl | member
    · exact component_good head
    · exact ih text member

theorem Pieces.valid_names {texts : List String} {items : List Component} {suffix : Bool}
    (grammar : Pieces texts items suffix) :
    (parameterNames items).all validName = true := by
  induction grammar with
  | exact => rfl
  | wildcard => rfl
  | @component text item texts items suffix head _ ih =>
    cases item with
    | literal segment => simpa [parameterNames] using ih
    | parameter name =>
      change (validName name && (parameterNames items).all validName) = true
      simp [(validName_iff name).mpr head.2, ih]

private theorem rejoin_split (text : String) :
    "/".intercalate ((text.split '/').toList.map (·.copy)) = text := by
  apply String.toList_inj.mp
  rw [String.toList_intercalate, String.toList_split_char]
  simp

private theorem split_slashes {texts : List String}
    (good : ∀ text ∈ texts, text ≠ "" ∧ '/' ∉ text.toList) (nonempty : texts ≠ []) :
    ((("/" ++ "/".intercalate texts).split '/').toList.map (·.copy)) = "" :: texts := by
  have spelling : "/" ++ "/".intercalate texts = "/".intercalate ("" :: texts) := by
    simp [String.intercalate_cons_of_ne_nil nonempty]
  rw [spelling]
  have noSlash : ∀ piece ∈ "" :: texts, '/' ∉ piece.toList := by
    intro piece member
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · exact (good piece member).2
  simpa using (String.toList_split_intercalate (c := '/') noSlash)

private theorem rooted_sound {kind : ErrorKind} {text : String} {texts : List String}
    (parsed : rootedPieces kind text = .ok texts) : text = "/" ++ "/".intercalate texts := by
  unfold rootedPieces at parsed
  split at parsed
  next root =>
    cases parsed
    simpa using root
  next =>
    split at parsed
    next head parts splitEq =>
      split at parsed
      next accepted =>
        cases parsed
        have nonempty : texts ≠ [] := by
          simpa using (Bool.and_eq_true_iff.mp accepted).1
        have joined := rejoin_split text
        rw [splitEq] at joined
        simpa [String.intercalate_cons_of_ne_nil nonempty] using joined.symm
      next => contradiction
    next => contradiction

private theorem rooted_complete (kind : ErrorKind) {texts : List String}
    (good : ∀ text ∈ texts, text ≠ "" ∧ '/' ∉ text.toList) :
    rootedPieces kind ("/" ++ "/".intercalate texts) = .ok texts := by
  cases texts with
  | nil => rfl
  | cons first rest =>
    have nonroot : "/" ++ "/".intercalate (first :: rest) ≠ "/" := by
      intro equal
      have splitEq := split_slashes good (by simp)
      rw [equal, String.toList_split_char] at splitEq
      have headEmpty : first = "" := (List.cons.inj (List.cons.inj splitEq).2).1.symm
      exact (good first (by simp)).1 headEmpty
    have allNonempty : (first :: rest).all (fun text => !text.isEmpty) = true := by
      apply List.all_eq_true.mpr
      intro text member
      simpa using (good text member).1
    simp [rootedPieces, nonroot, split_slashes good (by simp), allNonempty]
    rfl

private theorem source_sound {text : String} {texts : List String}
    (parsed : (if text == "*" then .ok ["*"] else rootedPieces .invalidRoute text) = .ok texts) :
    text = "/" ++ "/".intercalate texts ∨ (text = "*" ∧ texts = ["*"]) := by
  split at parsed
  next star => cases parsed; exact Or.inr ⟨by simpa using star, rfl⟩
  next => exact Or.inl (rooted_sound parsed)

private theorem source_complete {text : String} {texts : List String}
    (good : ∀ text ∈ texts, text ≠ "" ∧ '/' ∉ text.toList)
    (spelling : text = "/" ++ "/".intercalate texts ∨ (text = "*" ∧ texts = ["*"])) :
    (if text == "*" then .ok ["*"] else rootedPieces .invalidRoute text) = .ok texts := by
  rcases spelling with rfl | ⟨rfl, rfl⟩
  · have notStar : "/" ++ "/".intercalate texts ≠ "*" := by
      intro equal
      have := congrArg (fun s : String => s.toList.head?) equal
      simp [String.toList_append] at this
    simp only [beq_iff_eq, notStar, ↓reduceIte]
    exact rooted_complete .invalidRoute good
  · rfl

/-- Accepted patterns have precisely the grammar's components and suffix flag. -/
theorem parsePattern_iff (text : String) (parsed : ParsedPattern) :
    parsePattern text = .ok parsed ↔ Denotes text parsed.path parsed.suffix := by
  constructor
  · intro accepted
    unfold parsePattern at accepted
    dsimp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map] at accepted
    cases source : patternTexts text with
    | error error => rw [source] at accepted; contradiction
    | ok texts =>
      rw [source] at accepted
      dsimp only at accepted
      cases contents : parsePatternPieces texts with
      | error error => rw [contents] at accepted; contradiction
      | ok pair =>
        rcases pair with ⟨items, suffix⟩
        rw [contents] at accepted
        dsimp only at accepted
        split at accepted
        next valid =>
          cases accepted
          exact ⟨⟨texts, (pieces_iff _ _ _).mp contents, source_sound source⟩, valid.2⟩
        next => contradiction
  · cases parsed with
    | mk items suffix valid =>
      rintro ⟨⟨texts, grammar, spelling⟩, _⟩
      have source : patternTexts text = .ok texts := source_complete grammar.good spelling
      have contents := (pieces_iff _ _ _).mpr grammar
      unfold parsePattern
      dsimp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map]
      rw [source]
      dsimp only
      rw [contents]
      dsimp only
      rw [dite_eq_left valid]

theorem sound {text : String} {parsed : ParsedPattern}
    (accepted : parsePattern text = .ok parsed) : Denotes text parsed.path parsed.suffix :=
  (parsePattern_iff text parsed).mp accepted

/-- Construct the result from the grammar, without assuming parser success. -/
theorem complete {text : String} {items : List Component} {suffix : Bool}
    (grammar : Denotes text items suffix) :
    ∃ parsed, parsePattern text = .ok parsed ∧ parsed.path = items ∧ parsed.suffix = suffix := by
  obtain ⟨⟨texts, pieces, spelling⟩, unique⟩ := grammar
  let parsed : ParsedPattern := ⟨items, suffix, pieces.valid_names, unique⟩
  exact ⟨parsed, (parsePattern_iff text parsed).mpr ⟨⟨texts, pieces, spelling⟩, unique⟩, rfl, rfl⟩

theorem accepts_iff (text : String) :
    (∃ parsed, parsePattern text = .ok parsed) ↔
      ∃ items suffix, Denotes text items suffix := by
  constructor
  · rintro ⟨parsed, accepted⟩
    exact ⟨parsed.path, parsed.suffix, sound accepted⟩
  · rintro ⟨items, suffix, grammar⟩
    obtain ⟨parsed, accepted, _, _⟩ := complete grammar
    exact ⟨parsed, accepted⟩

private theorem component_error_kind {text : String} {error : Error}
    (rejected : parseComponent text = .error error) : error.kind = .invalidRoute := by
  unfold parseComponent at rejected
  split at rejected
  · dsimp only at rejected
    split at rejected
    · contradiction
    · cases rejected; rfl
  · split at rejected
    · contradiction
    · cases rejected; rfl

private theorem pieces_error_kind {texts : List String} {error : Error}
    (rejected : parsePatternPieces texts = .error error) : error.kind = .invalidRoute := by
  induction texts with
  | nil => contradiction
  | cons text texts ih =>
    unfold parsePatternPieces at rejected
    split at rejected
    · contradiction
    · dsimp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map] at rejected
      cases head : parseComponent text with
      | error bad =>
        rw [head] at rejected
        cases rejected
        exact component_error_kind head
      | ok item =>
        rw [head] at rejected
        dsimp only at rejected
        cases tail : parsePatternPieces texts with
        | error bad =>
          rw [tail] at rejected
          cases rejected
          exact ih tail
        | ok pair => rw [tail] at rejected; contradiction

private theorem rooted_error_kind {kind : ErrorKind} {text : String} {error : Error}
    (rejected : rootedPieces kind text = .error error) : error.kind = kind := by
  unfold rootedPieces at rejected
  split at rejected
  · contradiction
  · split at rejected
    · split at rejected
      · contradiction
      · cases rejected; rfl
    · cases rejected; rfl

theorem error_kind {text : String} {error : Error}
    (rejected : parsePattern text = .error error) : error.kind = .invalidRoute := by
  unfold parsePattern at rejected
  dsimp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map] at rejected
  cases source : patternTexts text with
  | error bad =>
    rw [source] at rejected
    cases rejected
    unfold patternTexts at source
    split at source
    · contradiction
    · exact rooted_error_kind source
  | ok texts =>
    rw [source] at rejected
    dsimp only at rejected
    cases contents : parsePatternPieces texts with
    | error bad =>
      rw [contents] at rejected
      cases rejected
      exact pieces_error_kind contents
    | ok pair =>
      rw [contents] at rejected
      dsimp only at rejected
      split at rejected
      · contradiction
      · cases rejected; rfl

theorem rejects_iff (text : String) :
    (∃ error, parsePattern text = .error error ∧ error.kind = .invalidRoute) ↔
      ¬ ∃ items suffix, Denotes text items suffix := by
  constructor
  · rintro ⟨error, rejected, _⟩ ⟨items, suffix, grammar⟩
    obtain ⟨parsed, accepted, _, _⟩ := complete grammar
    rw [rejected] at accepted
    contradiction
  · intro outside
    cases parsed : parsePattern text with
    | ok pattern => exact False.elim (outside ⟨pattern.path, pattern.suffix, sound parsed⟩)
    | error error => exact ⟨error, rfl, error_kind parsed⟩

/-- info: 'HonoLean.Adapter.PatternText.parsePattern_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsePattern_iff

/-- info: 'HonoLean.Adapter.PatternText.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepts_iff

/-- info: 'HonoLean.Adapter.PatternText.rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejects_iff

end HonoLean.Adapter.PatternText
