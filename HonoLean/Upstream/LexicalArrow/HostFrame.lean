import HonoLean.Upstream.LexicalArrow.Runtime

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

/-- Internal decomposition of a successful closed operation. These helper
premises are never the public inputs of an invocation correctness theorem. -/
private theorem bind_ok {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (returned : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind, Except.bind] at returned
  | ok value => exact ⟨value, rfl, returned⟩

private def environment (state : LabelMatchState) : List (String × Value) :=
  state.base.regexp.ambient.environment

/-- The three mutually recursive host operations call only closed intrinsic
identities. Their normal results preserve the value-environment observation.
They do not receive a lexical-cell store and cannot write one. -/
private theorem label_host_environments (fuel : Nat) :
    (∀ (context : LabelMatchContext) (receiver : Value) (reference : Nat)
      (key : LabelPropertyKey) (before : LabelMatchState) (value : Value) (after : LabelMatchState),
      getLabelProperty fuel context receiver reference key before = .ok (value, after) →
      environment after = environment before) ∧
    (∀ (context : LabelMatchContext) (callee receiver : Value)
      (before : LabelMatchState) (value : Value) (after : LabelMatchState),
      invokeLabelGetter fuel context callee receiver before = .ok (value, after) →
      environment after = environment before) ∧
    (∀ (context : LabelMatchContext) (reference : Nat) (flags : List LabelFlag)
      (before : LabelMatchState) (value : JSString) (after : LabelMatchState),
      getLabelFlags fuel context reference flags before = .ok (value, after) →
      environment after = environment before) := by
  induction fuel with
  | zero =>
    constructor
    · intro context receiver reference key before value after returned
      simp [getLabelProperty] at returned
    constructor
    · intro context callee receiver before value after returned
      simp [invokeLabelGetter] at returned
    · intro context reference flags before value after returned
      simp [getLabelFlags] at returned
  | succ fuel ih =>
    obtain ⟨propertyIH, getterIH, flagsIH⟩ := ih
    constructor
    · intro context receiver reference key before value after returned
      simp only [getLabelProperty] at returned
      obtain ⟨resolved, _, returned⟩ := bind_ok _ _ _ returned
      cases resolved with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
        obtain ⟨rfl, rfl⟩ := returned
        rfl
      | some found =>
        obtain ⟨foundHolder, descriptor⟩ := found
        cases descriptor with
        | data observed writable enumerable configurable =>
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
          obtain ⟨rfl, rfl⟩ := returned
          rfl
        | accessor getter setter enumerable configurable =>
          cases getter with
          | missing =>
            simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
            obtain ⟨rfl, rfl⟩ := returned
            rfl
          | prototype =>
            cases receiver <;> dsimp only at returned <;>
              try { solve | cases returned }
            case object =>
              obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
              obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
              simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, rfl⟩ := returned
              rfl
          | unsupported =>
            cases accessor : labelAccessorAt before foundHolder key with
            | none => simp [accessor, bind, Except.bind] at returned
            | some callee =>
              simp only [accessor] at returned
              obtain ⟨boundCallee, _, returned⟩ := bind_ok _ _ _ returned
              obtain ⟨result, invoked, returned⟩ := bind_ok _ _ _ returned
              obtain ⟨resultValue, resultState⟩ := result
              have preserved := getterIH context boundCallee receiver before resultValue resultState invoked
              simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact preserved
    constructor
    · intro context callee receiver before value after returned
      cases separated : labelTablesSeparated context before.base.regexp.ambient with
      | false => simp [invokeLabelGetter, separated] at returned
      | true =>
        simp only [invokeLabelGetter, separated, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at returned
        cases identity : labelBuiltinAt context.builtins callee with
        | none => simp [identity] at returned
        | some builtin =>
          cases builtin with
          | stringMatch => simp [identity] at returned
          | regexpMatch => simp [identity] at returned
          | flagsGetter =>
            simp only [identity] at returned
            cases receiver <;> dsimp only at returned <;>
              try { solve | cases returned }
            case object =>
              obtain ⟨boundReference, _, returned⟩ := bind_ok _ _ _ returned
              obtain ⟨result, invoked, returned⟩ := bind_ok _ _ _ returned
              obtain ⟨flags, intermediate⟩ := result
              have preserved := flagsIH context boundReference labelFlags _ flags intermediate invoked
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact preserved
          | flagGetter flag =>
            simp only [identity] at returned
            cases receiver <;> dsimp only at returned <;>
              try { solve | cases returned }
            case object =>
              obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
              split at returned
              · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
                obtain ⟨rfl, rfl⟩ := returned
                rfl
              · split at returned
                · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
                  obtain ⟨rfl, rfl⟩ := returned
                  rfl
                · split at returned
                  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
                    obtain ⟨rfl, rfl⟩ := returned
                    rfl
                  · simp at returned
    · intro context reference flags before value after returned
      cases flags with
      | nil =>
        simp only [getLabelFlags, Except.ok.injEq, Prod.mk.injEq] at returned
        obtain ⟨rfl, rfl⟩ := returned
        rfl
      | cons flag flags =>
        simp only [getLabelFlags] at returned
        obtain ⟨first, fetched, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨flagValue, intermediate⟩ := first
        obtain ⟨last, rest, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨restFlags, finalState⟩ := last
        have firstFrame := propertyIH context (.object reference) reference (.string (labelFlagKey flag))
          before flagValue intermediate fetched
        have restFrame := flagsIH context reference flags intermediate restFlags finalState rest
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
        obtain ⟨rfl, rfl⟩ := returned
        exact restFrame.trans firstFrame

theorem getLabelProperty_environment (fuel : Nat) (context : LabelMatchContext)
    (receiver : Value) (reference : Nat) (key : LabelPropertyKey)
    (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : getLabelProperty fuel context receiver reference key before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment :=
  (label_host_environments fuel).1 context receiver reference key before value after returned

theorem invokeLabelGetter_environment (fuel : Nat) (context : LabelMatchContext)
    (callee receiver : Value) (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : invokeLabelGetter fuel context callee receiver before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment :=
  (label_host_environments fuel).2.1 context callee receiver before value after returned

theorem getLabelFlags_environment (fuel : Nat) (context : LabelMatchContext)
    (reference : Nat) (flags : List LabelFlag) (before : LabelMatchState) (value : JSString) (after : LabelMatchState)
    (returned : getLabelFlags fuel context reference flags before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment :=
  (label_host_environments fuel).2.2 context reference flags before value after returned

theorem allocateLabelLiteral_environment (context : LabelMatchContext) (literal : LabelRegExpLiteral)
    (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : allocateLabelLiteral context literal before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  simp only [allocateLabelLiteral] at returned
  cases prototype : before.base.regexp.ambient.objects[context.regexpPrototype]? with
  | none => simp [prototype, bind, Except.bind] at returned
  | some object =>
    simp only [prototype] at returned
    obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
    cases initialized : initializeLabelRecord literal with
    | none => simp [initialized, bind, Except.bind] at returned
    | some record =>
      simp only [initialized] at returned
      obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
      obtain ⟨objects, _, returned⟩ := bind_ok _ _ _ returned
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      rfl

theorem invokeLabelExec_environment (fuel : Nat) (context : LabelMatchContext) (receiver input : Value)
    (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : invokeLabelExec fuel context receiver input before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  simp only [invokeLabelExec] at returned
  cases receiver <;> dsimp only at returned <;>
    try { solve | cases returned }
  case object =>
    obtain ⟨reference, _, returned⟩ := bind_ok _ _ _ returned
    cases branded : before.brands.lookup reference with
    | none => simp [branded, bind, Except.bind] at returned
    | some record =>
      simp only [branded] at returned
      obtain ⟨record, _, returned⟩ := bind_ok _ _ _ returned
      cases input <;> dsimp only at returned <;>
        try { solve | cases returned }
      case string =>
        obtain ⟨text, _, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨result, fetched, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨lastIndex, intermediate⟩ := result
        have preserved := getLabelProperty_environment fuel context _ reference (.string lastIndexKey)
          _ lastIndex intermediate fetched
        cases lastIndex <;> dsimp only at returned <;>
          try { solve | cases returned }
        case number =>
          obtain ⟨number, _, returned⟩ := bind_ok _ _ _ returned
          obtain ⟨length, _, returned⟩ := bind_ok _ _ _ returned
          split at returned
          · simp at returned
          · split at returned
            · simp at returned
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact preserved
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact preserved

theorem invokeLabelRegExpMatch_environment (fuel : Nat) (context : LabelMatchContext) (receiver input : Value)
    (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : invokeLabelRegExpMatch fuel context receiver input before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  simp only [invokeLabelRegExpMatch] at returned
  cases receiver <;> dsimp only at returned <;>
    try { solve | cases returned }
  case object =>
    obtain ⟨reference, _, returned⟩ := bind_ok _ _ _ returned
    cases input <;> dsimp only at returned <;>
      try { solve | cases returned }
    case string =>
      obtain ⟨text, _, returned⟩ := bind_ok _ _ _ returned
      obtain ⟨flagsResult, fetchedFlags, returned⟩ := bind_ok _ _ _ returned
      obtain ⟨flags, afterFlags⟩ := flagsResult
      have flagsFrame := getLabelProperty_environment fuel context _ reference (.string labelFlagsKey)
        _ flags afterFlags fetchedFlags
      cases flags <;> dsimp only at returned <;>
        try { solve | cases returned }
      case string =>
        obtain ⟨flagsText, _, returned⟩ := bind_ok _ _ _ returned
        split at returned
        · simp at returned
        · obtain ⟨execResult, fetchedExec, returned⟩ := bind_ok _ _ _ returned
          obtain ⟨callee, afterExec⟩ := execResult
          have execFrame := getLabelProperty_environment fuel context _ reference (.string labelExecKey)
            _ callee afterExec fetchedExec
          split at returned
          · simp at returned
          · have callFrame := invokeLabelExec_environment fuel context _ (.string text) _ value after returned
            exact callFrame.trans (execFrame.trans flagsFrame)

theorem invokeLabelStringMatch_environment (fuel : Nat) (context : LabelMatchContext) (callee receiver argument : Value)
    (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : invokeLabelStringMatch fuel context callee receiver argument before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  simp only [invokeLabelStringMatch] at returned
  split at returned
  · simp at returned
  · split at returned
    · simp at returned
    · cases argument <;> dsimp only at returned <;>
        try { solve | cases returned }
      case object =>
        obtain ⟨reference, _, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨methodResult, fetched, returned⟩ := bind_ok _ _ _ returned
        obtain ⟨method, intermediate⟩ := methodResult
        have propertyFrame := getLabelProperty_environment fuel context _ reference (.symbol .match)
          _ method intermediate fetched
        split at returned
        · simp at returned
        · have callFrame := invokeLabelRegExpMatch_environment fuel context _ receiver _ value after returned
          exact callFrame.trans propertyFrame

/-- Internal frame law for the actual closed host sequence. No arbitrary
user callback or native failure-state interpretation is inferred. -/
theorem runResolvedLabelMatch_environment (fuel : Nat) (context : LabelMatchContext) (receiver : Value)
    (method : String) (literal : LabelRegExpLiteral) (before : LabelMatchState) (value : Value) (after : LabelMatchState)
    (returned : runResolvedLabelMatch fuel context receiver method literal before = .ok (value, after)) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  simp only [runResolvedLabelMatch] at returned
  cases receiver <;> dsimp only at returned <;>
    try { solve | cases returned }
  case string =>
    obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
    obtain ⟨calleeResult, fetched, returned⟩ := bind_ok _ _ _ returned
    obtain ⟨callee, afterGet⟩ := calleeResult
    have getFrame := getLabelProperty_environment fuel context _ context.stringPrototype (.string (cacheAscii method))
      _ callee afterGet fetched
    obtain ⟨argumentResult, allocated, returned⟩ := bind_ok _ _ _ returned
    obtain ⟨argument, afterLiteral⟩ := argumentResult
    have allocationFrame := allocateLabelLiteral_environment context literal afterGet argument afterLiteral allocated
    have callFrame := invokeLabelStringMatch_environment fuel context callee _ argument afterLiteral value after returned
    exact callFrame.trans (allocationFrame.trans getFrame)

private theorem initializeAllocatedRegExp_environment (reference : Nat) (source : JSString)
    (before : RegExpCallState) (value : Value) (after : RegExpCallState)
    (returned : initializeAllocatedRegExp reference source before = .ok (value, after)) :
    after.ambient.environment = before.ambient.environment := by
  simp only [initializeAllocatedRegExp] at returned
  cases initialized : initializeRangeRecord source [] with
  | none => simp [initialized, bind, Except.bind] at returned
  | some record =>
    simp only [initialized] at returned
    obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
    obtain ⟨objects, _, returned⟩ := bind_ok _ _ _ returned
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
    obtain ⟨rfl, rfl⟩ := returned
    rfl

/-- RegExp construction changes ordinary objects and internal brands, while
preserving the lexical environment observation on normal completion. -/
theorem invokeRegExpConstructor_environment (context : RegExpConstructContext) (callee argument : Value)
    (before : RegExpCallState) (value : Value) (after : RegExpCallState)
    (returned : invokeRegExpConstructor context callee argument before = .ok (value, after)) :
    after.ambient.environment = before.ambient.environment := by
  simp only [invokeRegExpConstructor] at returned
  split at returned
  · simp at returned
  · cases identity : constructorAt context.constructors callee with
    | none => simp [identity, bind, Except.bind] at returned
    | some constructor =>
      simp only [identity] at returned
      obtain ⟨constructor, _, returned⟩ := bind_ok _ _ _ returned
      cases prototype : before.ambient.objects[constructor.prototype]? with
      | none => simp [prototype, bind, Except.bind] at returned
      | some object =>
        simp only [prototype] at returned
        obtain ⟨_, _, returned⟩ := bind_ok _ _ _ returned
        cases argument <;> dsimp only at returned <;>
          try { solve | cases returned }
        case string =>
          obtain ⟨source, _, returned⟩ := bind_ok _ _ _ returned
          exact initializeAllocatedRegExp_environment before.ambient.objects.length source
            (regExpAllocatedState before constructor.prototype) value after returned

end HonoLean.Upstream.LexicalArrow
