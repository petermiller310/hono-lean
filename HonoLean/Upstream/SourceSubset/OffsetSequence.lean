import HonoLean.Upstream.SourceSubset.OffsetSyntax
import HonoLean.Upstream.ECMA2025.DenseArray

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

/-- Only this new entry adds primitive UTF16 indexing/length to the shared
property rules. No boxing, generic key conversion or prototype claim is added. -/
def readOffsetProperty (receiver key : Value) (state : State) : Except EvalError Value :=
  match receiver, key with
  | .string input, .number (.ofNat index) => .ok ((input[index]?).map (fun unit => Value.string [unit]) |>.getD .undefined)
  | .string input, .string [108, 101, 110, 103, 116, 104] => .ok (.number input.length)
  | _, _ => readProperty receiver key state

/-- Dense update or next-index append only. Gaps reject; source fresh offsets
prove each p equals current length. Standard writable own/length and clean
numeric prototypes, legal native lengths/resources remain domain premises. -/
def putOffsetReference (reference : OffsetReference) (value : Value) (state : State) : Except EvalError State :=
  match reference with
  | .binding _ none => .error .missingVariable
  | .binding name (some index) => .ok {state with environment := state.environment.set index (name, value)}
  | .property ⟨.array reference, .number (.ofNat index)⟩ =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some values =>
      if index < values.length then .ok {state with heap := state.heap.set reference (values.set index value)}
      else if index = values.length && index < maximumArrayLength then
        .ok {state with heap := state.heap.set reference (values ++ [value])}
      else .error .unsupported
  | _ => .error .unsupported

mutual
  /-- Mathematical Int addition only; both operand effects precede numeric
  rejection. Native interpretation requires exact integral operands AND sum;
  ToPrimitive/string concatenation/rounding/negative-zero identity stay open. -/
  def evalOffsetExpression : Nat → Nat → OffsetExpr → State → Except EvalError (Value × State)
    | 0, _, _, _ => .error .exhausted
    | fuel + 1, limit, expression, state => do
      match expression with
      | .ordinary value =>
        match value with
        | .variable _ | .number _ | .string _ | .boolean _ | .null | .arrayLiteral [] => evalExpression fuel limit value state
        | _ => .error .unsupported
      | .add left right =>
        let (left, state) ← evalOffsetExpression fuel limit left state
        let (right, state) ← evalOffsetExpression fuel limit right state
        match left, right with
        | .number left, .number right => return (.number (left + right), state)
        | _, _ => .error .unsupported
      | .index receiver key =>
        let (receiver, state) ← evalOffsetExpression fuel limit receiver state
        let (key, state) ← evalOffsetExpression fuel limit key state
        let value ← readOffsetProperty receiver key state
        return (value, state)
      | .property receiver key =>
        let (receiver, state) ← evalOffsetExpression fuel limit receiver state
        let value ← readOffsetProperty receiver (.string key) state
        return (value, state)
      | .logicalNot value =>
        let (value, state) ← evalOffsetExpression fuel limit value state
        return (.boolean (!truthy value), state)
      | .strictEqual left right =>
        let (left, state) ← evalOffsetExpression fuel limit left state
        let (right, state) ← evalOffsetExpression fuel limit right state
        return (.boolean (left == right), state)
      | .compare operation left right =>
        let (left, state) ← evalOffsetExpression fuel limit left state
        let (right, state) ← evalOffsetExpression fuel limit right state
        match left, right with
        | .number left, .number right => return (.boolean (compareNumbers operation left right), state)
        | _, _ => .error .unsupported
      | .conditional condition yes no =>
        let (value, state) ← evalOffsetExpression fuel limit condition state
        evalOffsetExpression fuel limit (if truthy value then yes else no) state
      | .call receiver method arguments =>
        let (receiver, state) ← evalOffsetExpression fuel limit receiver state
        match receiver with
        | .array _ | .string _ => pure ()
        | _ => .error .unsupported
        let prepared ← prepareMethod receiver method state
        let (arguments, state) ← evalOffsetArguments fuel limit arguments state
        match receiver, method, arguments with
        | .string _, "slice", [.undefined] => invokePrepared fuel limit prepared [.number 0] state
        | _, _, _ => invokePrepared fuel limit prepared arguments state

  def evalOffsetArguments : Nat → Nat → List OffsetExpr → State → Except EvalError (List Value × State)
    | 0, _, _, _ => .error .exhausted
    | _ + 1, _, [], state => .ok ([], state)
    | fuel + 1, limit, head :: tail, state => do
      let (value, state) ← evalOffsetExpression fuel limit head state
      let (values, state) ← evalOffsetArguments fuel limit tail state
      return (value :: values, state)
end

def captureOffsetReference (fuel limit : Nat) (mutableBindings : List String) (target : OffsetExpr) (state : State) :
    Except EvalError (OffsetReference × State) := do
  match target with
  | .ordinary (.variable name) =>
    if mutableBindings.contains name then return (.binding name (mutableBindingIndex name state.environment), state)
    else .error .unsupported
  | .index receiver key =>
    let (receiver, state) ← evalOffsetExpression fuel limit receiver state
    let (key, state) ← evalOffsetExpression fuel limit key state
    return (.property ⟨receiver, key⟩, state)
  | _ => .error .unsupported

def executeOffsetAssign (fuel limit : Nat) (mutableBindings : List String) (target rhs : OffsetExpr) (state : State) : Except EvalError State := do
  let (reference, state) ← captureOffsetReference fuel limit mutableBindings target state
  let (value, state) ← evalOffsetExpression fuel limit rhs state
  putOffsetReference reference value state

/-- Compound assignment captures and GetValues the existing first lexical cell
BEFORE RHS; unresolved names fail before RHS. Numeric checks follow RHS effects. -/
def executeOffsetAddAssign (fuel limit : Nat) (mutableBindings : List String) (name : String) (rhs : OffsetExpr) (state : State) : Except EvalError State := do
  if !mutableBindings.contains name then .error .unsupported else
  let index ← match mutableBindingIndex name state.environment with
    | none => .error .missingVariable
    | some index => .ok index
  let old ← match state.environment[index]? with
    | none => .error .missingVariable
    | some (_, value) => .ok value
  let (value, state) ← evalOffsetExpression fuel limit rhs state
  match old, value with
  | .number old, .number value => putOffsetReference (.binding name (some index)) (.number (old + value)) state
  | _, _ => .error .unsupported

mutual
  def executeOffsetSequence : Nat → Nat → List String → List OffsetStmt → State → Except EvalError State
    | 0, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, [], state => .ok state
    | fuel + 1, limit, mutableBindings, head :: tail, state => do
      match head with
      | .declare mutableBinding name value =>
        let (value, state) ← evalOffsetExpression fuel limit value state
        let mutableBindings := if mutableBinding then name :: mutableBindings else mutableBindings.filter (· != name)
        executeOffsetSequence fuel limit mutableBindings tail {state with environment := (name, value) :: state.environment}
      | .assign target rhs =>
        let state ← executeOffsetAssign fuel limit mutableBindings target rhs state
        executeOffsetSequence fuel limit mutableBindings tail state
      | .addAssign name rhs =>
        let state ← executeOffsetAddAssign fuel limit mutableBindings name rhs state
        executeOffsetSequence fuel limit mutableBindings tail state
      | .branch condition body =>
        let (value, state) ← evalOffsetExpression fuel limit condition state
        if truthy value then
          let outer := state.environment
          let names := offsetDeclaredNames body
          let state ← executeOffsetSequence fuel limit (mutableBindings.filter (fun name => !names.contains name)) body
            {state with environment := withoutBindings outer names}
          executeOffsetSequence fuel limit mutableBindings tail (restoreOffsetScope outer names state)
        else executeOffsetSequence fuel limit mutableBindings tail state
      | .countedFor header body =>
        let outer := state.environment
        let state ← enterForHeader fuel limit header state
        let names := header.initializers.map Prod.fst
        let state ← executeOffsetFor fuel limit (names ++ mutableBindings.filter (fun name => !names.contains name)) header body state
        executeOffsetSequence fuel limit mutableBindings tail (restoreOffsetScope outer names state)

  def executeOffsetFor : Nat → Nat → List String → ForHeader → List OffsetStmt → State → Except EvalError State
    | 0, _, _, _, _, _ => .error .exhausted
    | fuel + 1, limit, mutableBindings, header, body, state => do
      let (inside, state) ← testForHeader fuel limit header state
      if inside then
        let outer := state.environment
        let names := offsetDeclaredNames body
        let state ← executeOffsetSequence fuel limit (mutableBindings.filter (fun name => !names.contains name)) body
          {state with environment := withoutBindings outer names}
        let state ← advanceForHeader header (restoreOffsetScope outer names state)
        executeOffsetFor fuel limit mutableBindings header body state
      else return state
end

/-- Local maximal-munch +/+=/++ extension. Quoted plus signs remain strings;
comments, templates and unsupported escapes are not rewritten. -/
private def offsetTokens : Nat → Option Char → List Char → List Char → Option (List Token)
  | 0, _, _, _ => none
  | _ + 1, none, pending, [] => tokenizeFragment (String.ofList pending.reverse)
  | _ + 1, some _, _, [] => none
  | fuel + 1, quote, pending, character :: rest => do
    match quote with
    | some delimiter =>
      if character == '\\' || character == '\n' || character == '\r' then none else
      offsetTokens fuel (if character == delimiter then none else quote) (character :: pending) rest
    | none =>
      if character == '\'' || character == '"' then offsetTokens fuel (some character) (character :: pending) rest
      else if character == '+' then
        let front ← tokenizeFragment (String.ofList pending.reverse)
        let (operator, rest) := match rest with
          | '+' :: rest => ("++", rest)
          | '=' :: rest => ("+=", rest)
          | _ => ("+", rest)
        return front ++ .punctuation operator :: (← offsetTokens fuel none [] rest)
      else offsetTokens fuel none (character :: pending) rest

def tokenizeOffsetSequence (text : String) : Option (List Token) :=
  offsetTokens (text.toList.length + 1) none [] text.toList

mutual
  private def offsetExpression : Nat → List Token → Option (OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (condition, rest) ← offsetEquality fuel tokens
      match skipTokenLines rest with
      | .punctuation "?" :: rest =>
        let (yes, rest) ← offsetExpression fuel (skipTokenLines rest)
        let rest ← match skipTokenLines rest with | .punctuation ":" :: rest => some rest | _ => none
        let (no, rest) ← offsetExpression fuel (skipTokenLines rest)
        some (.conditional condition yes no, rest)
      | _ => some (condition, rest)

  private def offsetEquality : Nat → List Token → Option (OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← offsetComparison fuel tokens
      match skipTokenLines rest with
      | .punctuation "===" :: rest =>
        let (right, rest) ← offsetComparison fuel (skipTokenLines rest)
        match skipTokenLines rest with | .punctuation "===" :: _ => none | _ => some (.strictEqual left right, rest)
      | _ => some (left, rest)

  private def offsetComparison : Nat → List Token → Option (OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← offsetAddition fuel tokens
      match skipTokenLines rest with
      | .punctuation operator :: rest =>
        if operator == "<" || operator == "<=" then
          let (right, rest) ← offsetAddition fuel (skipTokenLines rest)
          match skipTokenLines rest with
          | .punctuation "<" :: _ | .punctuation "<=" :: _ => none
          | _ => some (.compare (if operator == "<" then .less else .lessEqual) left right, rest)
        else some (left, .punctuation operator :: rest)
      | _ => some (left, rest)

  private def offsetAddition : Nat → List Token → Option (OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← offsetUnary fuel tokens
      offsetAdditionTail fuel left rest

  private def offsetAdditionTail : Nat → OffsetExpr → List Token → Option (OffsetExpr × List Token)
    | 0, _, _ => none
    | fuel + 1, left, tokens =>
      match skipTokenLines tokens with
      | .punctuation "+" :: rest => do
        let (right, rest) ← offsetUnary fuel (skipTokenLines rest)
        offsetAdditionTail fuel (.add left right) rest
      | _ => some (left, tokens)

  private def offsetUnary : Nat → List Token → Option (OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens =>
      match skipTokenLines tokens with
      | .punctuation "!" :: rest => do
        let (value, rest) ← offsetUnary fuel (skipTokenLines rest)
        some (.logicalNot value, rest)
      | .punctuation "-" :: .number value :: rest =>
        if value == 0 then none else offsetPostfix fuel (.ordinary (.number (-(value : Int)))) rest
      | tokens => do
        let (value, rest) ← match tokens with
          | .name "null" :: rest => some (OffsetExpr.ordinary .null, rest)
          | .name "true" :: rest => some (.ordinary (.boolean true), rest)
          | .name "false" :: rest => some (.ordinary (.boolean false), rest)
          | .name name :: rest => some (.ordinary (.variable name), rest)
          | .number value :: rest => some (.ordinary (.number value), rest)
          | .string value :: rest => some (.ordinary (.string value), rest)
          | .punctuation "[" :: rest => match skipTokenLines rest with
            | .punctuation "]" :: rest => some (.ordinary (.arrayLiteral []), rest)
            | _ => none
          | .punctuation "(" :: rest => do
            let (value, rest) ← offsetExpression fuel (skipTokenLines rest)
            match skipTokenLines rest with | .punctuation ")" :: rest => some (value, rest) | _ => none
          | _ => none
        offsetPostfix fuel value rest

  private def offsetPostfix : Nat → OffsetExpr → List Token → Option (OffsetExpr × List Token)
    | 0, _, _ => none
    | fuel + 1, value, tokens =>
      match skipTokenLines tokens with
      | .punctuation "[" :: rest => do
        let (key, rest) ← offsetExpression fuel (skipTokenLines rest)
        let rest ← match skipTokenLines rest with | .punctuation "]" :: rest => some rest | _ => none
        offsetPostfix fuel (.index value key) rest
      | .punctuation "." :: .name method :: rest => do
        match skipTokenLines rest with
        | .punctuation "(" :: rest =>
          let (arguments, rest) ← offsetArguments fuel (skipTokenLines rest)
          let arity := (method == "slice" && (arguments.length == 1 || arguments.length == 2)) ||
            (method == "split" && arguments.length == 1) || (method == "indexOf" && arguments.length == 2) ||
            (method == "shift" && arguments.isEmpty) || method == "push"
          if !arity then none else
          offsetPostfix fuel (.call value method arguments) rest
        | _ =>
          if method == "length" then offsetPostfix fuel (.property value [108, 101, 110, 103, 116, 104]) rest else none
      | _ => some (value, tokens)

  private def offsetArguments : Nat → List Token → Option (List OffsetExpr × List Token)
    | 0, _ => none
    | fuel + 1, tokens => do
      match skipTokenLines tokens with
      | .punctuation ")" :: rest => some ([], rest)
      | tokens =>
        let (value, rest) ← offsetExpression fuel tokens
        match skipTokenLines rest with
        | .punctuation ")" :: rest => some ([value], rest)
        | .punctuation "," :: rest =>
          let (values, rest) ← offsetArguments fuel (skipTokenLines rest)
          some (value :: values, rest)
        | _ => none
end

private def offsetExpressionAdmittedCore : Nat → OffsetExpr → List String → Bool
  | 0, _, _ => false
  | fuel + 1, expression, bindings =>
    match expression with
    | .ordinary value => expressionAdmitted value bindings [] false && privateControlExpressionAllowed 65536 value
    | .add left right | .index left right | .strictEqual left right | .compare _ left right =>
      offsetExpressionAdmittedCore fuel left bindings && offsetExpressionAdmittedCore fuel right bindings
    | .property receiver _ | .logicalNot receiver => offsetExpressionAdmittedCore fuel receiver bindings
    | .call receiver _ arguments => offsetExpressionAdmittedCore fuel receiver bindings &&
      arguments.all (fun value => offsetExpressionAdmittedCore fuel value bindings)
    | .conditional condition yes no => offsetExpressionAdmittedCore fuel condition bindings &&
      offsetExpressionAdmittedCore fuel yes bindings && offsetExpressionAdmittedCore fuel no bindings

def offsetExpressionAdmitted (expression : OffsetExpr) (bindings : List String) : Bool :=
  offsetExpressionAdmittedCore 65536 expression bindings

private def offsetBoundary : List Token → Option (List Token)
  | .punctuation ";" :: rest => some rest
  | .punctuation "}" :: rest => some (.punctuation "}" :: rest)
  | .lineBreak :: rest =>
    match skipTokenLines rest with
    | .punctuation "+" :: _ | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | _ => none

private def offsetInitializers : Nat → List Token → Option (List (String × Expr) × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
    let (name, rest) ← match skipTokenLines tokens with
      | .name name :: .punctuation "=" :: rest => some (name, rest)
      | _ => none
    let (value, rest) ← parseRawExpressionTokens rest
    match skipTokenLines rest with
    | .punctuation ";" :: rest => some ([(name, value)], rest)
    | .punctuation "," :: rest =>
      let (values, rest) ← offsetInitializers fuel rest
      some ((name, value) :: values, rest)
    | _ => none
private def offsetHeaderPure : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, value =>
    match value with
    | .variable _ | .number _ | .boolean _ | .string _ | .null => true
    | .logicalNot value | .typeAssertion value _ => offsetHeaderPure fuel value
    | .compare _ left right | .strictEqual left right | .subtract left right
    | .logicalAnd left right | .logicalOr left right | .nullish left right => offsetHeaderPure fuel left && offsetHeaderPure fuel right
    | .conditional condition yes no => offsetHeaderPure fuel condition && offsetHeaderPure fuel yes && offsetHeaderPure fuel no
    | _ => false

private def offsetNextBindings (statement : OffsetStmt) (bindings : List String) : List String :=
  match statement with | .declare _ name _ => name :: bindings | _ => bindings
private def offsetNextMutable (statement : OffsetStmt) (bindings : List String) : List String :=
  match statement with
  | .declare true name _ => name :: bindings
  | .declare false name _ => bindings.filter (· != name)
  | _ => bindings

mutual
  private def offsetStatements : Nat → Bool → List String → List String → List Token → Option (List OffsetStmt × List Token)
    | 0, _, _, _, _ => none
    | fuel + 1, top, bindings, mutableBindings, tokens => do
      match skipTokenLines tokens with
      | [] => if top then some ([], []) else none
      | .punctuation "}" :: rest => if top then none else some ([], rest)
      | tokens =>
        let (head, rest) ← offsetStatement fuel bindings mutableBindings tokens
        let (tail, rest) ← offsetStatements fuel top (offsetNextBindings head bindings) (offsetNextMutable head mutableBindings) rest
        some (head :: tail, rest)

  private def offsetStatement : Nat → List String → List String → List Token → Option (OffsetStmt × List Token)
    | 0, _, _, _ => none
    | fuel + 1, bindings, mutableBindings, tokens => do
      match tokens with
      | .name keyword :: .name name :: .punctuation "=" :: rest =>
        if keyword == "const" || keyword == "let" then
          if !bindingNameAllowed name || name == "Object" || name == "Set" || bindings.contains name then none else
          let (value, rest) ← offsetExpression fuel (skipTokenLines rest)
          if !offsetExpressionAdmitted value bindings then none else
          return (.declare (keyword == "let") name value, ← offsetBoundary rest)
        else none
      | .name "if" :: rest =>
        let rest ← match skipTokenLines rest with | .punctuation "(" :: rest => some rest | _ => none
        let (condition, rest) ← offsetExpression fuel (skipTokenLines rest)
        if !offsetExpressionAdmitted condition bindings then none else
        let rest ← match skipTokenLines rest with | .punctuation ")" :: rest => some rest | _ => none
        let rest ← match skipTokenLines rest with | .punctuation "{" :: rest => some rest | _ => none
        let (body, rest) ← offsetStatements fuel false bindings mutableBindings rest
        some (.branch condition body, rest)
      | .name "for" :: rest =>
        let rest ← match skipTokenLines rest with | .punctuation "(" :: rest => some rest | _ => none
        let rest ← match skipTokenLines rest with | .name "let" :: rest => some rest | _ => none
        let (initializers, rest) ← offsetInitializers fuel rest
        let (condition, rest) ← parseRawExpressionTokens rest
        let rest ← match skipTokenLines rest with | .punctuation ";" :: rest => some rest | _ => none
        let (incrementName, rest) ← match skipTokenLines rest with
          | .name name :: .punctuation "++" :: rest => some (name, rest)
          | _ => none
        let rest ← match skipTokenLines rest with | .punctuation ")" :: rest => some rest | _ => none
        let rest ← match skipTokenLines rest with | .punctuation "{" :: rest => some rest | _ => none
        if !statementAdmitted (.countedFor initializers condition incrementName []) bindings [] false ||
            !initializers.all (fun entry => offsetHeaderPure 65536 entry.2) || !offsetHeaderPure 65536 condition then none else
        let names := initializers.map Prod.fst
        let (body, rest) ← offsetStatements fuel false (names.reverse ++ bindings.filter (fun name => !names.contains name))
          (names ++ mutableBindings.filter (fun name => !names.contains name)) rest
        some (.countedFor ⟨initializers, condition, incrementName⟩ body, rest)
      | tokens =>
        let (target, rest) ← offsetExpression fuel tokens
        if !offsetExpressionAdmitted target bindings then none else
        match skipTokenLines rest with
        | .punctuation "=" :: rest =>
          let permitted := match target with
            | .ordinary (.variable name) => mutableBindings.contains name
            | .index _ _ => true
            | _ => false
          if !permitted then none else
          let (rhs, rest) ← offsetExpression fuel (skipTokenLines rest)
          if !offsetExpressionAdmitted rhs bindings then none else
          return (.assign target rhs, ← offsetBoundary rest)
        | .punctuation "+=" :: rest =>
          let name ← match target with | .ordinary (.variable name) => some name | _ => none
          if !mutableBindings.contains name then none else
          let (rhs, rest) ← offsetExpression fuel (skipTokenLines rest)
          if !offsetExpressionAdmitted rhs bindings then none else
          return (.addAssign name rhs, ← offsetBoundary rest)
        | _ => none
end

/-- Separate exact-source extension. Ordinary spans use the shared fail-closed
lexer; original +/+= nodes and actual for body are retained. Callback dispatch,
outer captured writes beyond the authority list, const writes and TDZ reads
reject. Native mutable lexical cells/closures and general Number coercion stay
outside this source-normal integer/dense-array specialization. -/
def parseOffsetSequence (text : String) (allowedBindings mutableBindings : List String) : Option (List OffsetStmt) := do
  if !allowedBindings.all bindingNameAllowed || !mutableBindings.all bindingNameAllowed then none else
  let tokens ← tokenizeOffsetSequence text
  let (program, rest) ← offsetStatements (16 * (tokens.length + 2)) true allowedBindings mutableBindings (tokens ++ [.lineBreak])
  if rest.isEmpty then some program else none

end HonoLean.Upstream.SourceSubset
