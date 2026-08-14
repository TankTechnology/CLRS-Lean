import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import Mathlib.Computability.TuringMachine.Computable

/-!
# Compiling bounded builders to TM2

The compiler in this file is intentionally separate from the independent
instruction semantics. Its correctness theorem compares the concrete TM2 step
with the independently defined builder semantics.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The compiled machine's cleared buffers and counter-test bit. -/
private def initialControl {Γ : Type} : ControlState Γ :=
  ⟨none, none, false⟩

/-- Store the symbol read by a buffer-one instruction family. -/
private def setBuffer₁ {Γ : Type} (state : ControlState Γ)
    (symbol : Option Γ) : ControlState Γ :=
  { state with buffer₁ := symbol }

/-- Store the symbol read by a buffer-two instruction family. -/
private def setBuffer₂ {Γ : Type} (state : ControlState Γ)
    (symbol : Option Γ) : ControlState Γ :=
  { state with buffer₂ := symbol }

/-- Record whether a unary-counter pop found a successor token. -/
private def setCounterTest {Γ : Type} (state : ControlState Γ)
    (head : Option Unit) : ControlState Γ :=
  { state with test := head.isSome }

/-- Read buffer one after its nonempty branch, with a compiler fallback. -/
private def buffer₁Value {Γ : Type} (fallback : Γ)
    (state : ControlState Γ) : Γ :=
  state.buffer₁.getD fallback

/-- Read buffer two after its nonempty branch, with a compiler fallback. -/
private def buffer₂Value {Γ : Type} (fallback : Γ)
    (state : ControlState Γ) : Γ :=
  state.buffer₂.getD fallback

/-- Compile a legal stack move whose popped symbol is owned by buffer one. -/
private def compileMove₁ {Γ Δ Λ : Type} (fallback : Γ)
    (source target : Stack) (nextEmpty : Λ) (nextMoved : Γ → Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  let stmt (pop : (ControlState Γ → Option Γ → ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ))
      (push : (ControlState Γ → Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ)) :=
    pop setBuffer₁ <|
      _root_.Turing.TM2.Stmt.branch (fun state => state.buffer₁.isSome)
        (push (buffer₁Value fallback) <|
          _root_.Turing.TM2.Stmt.goto
            (fun state => nextMoved (buffer₁Value fallback state)))
        (_root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty))
  match source, target with
  | .input, .work₁ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.input)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.work₁)
  | .work₁, .input => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.work₁)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.input)
  | .work₁, .work₂ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.work₁)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.work₂)
  | _, _ => .halt

/-- Compile a legal stack move whose popped symbol is owned by buffer two. -/
private def compileMove₂ {Γ Δ Λ : Type} (fallback : Γ)
    (source target : Stack) (nextEmpty : Λ) (nextMoved : Γ → Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  let stmt
      (pop : (ControlState Γ → Option Γ → ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ))
      (push : (ControlState Γ → Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ)) :=
    pop setBuffer₂ <|
      _root_.Turing.TM2.Stmt.branch (fun state => state.buffer₂.isSome)
        (push (buffer₂Value fallback) <|
          _root_.Turing.TM2.Stmt.goto
            (fun state => nextMoved (buffer₂Value fallback state)))
        (_root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty))
  match source, target with
  | .input, .work₂ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.input)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.work₂)
  | .work₂, .input => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.work₂)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.input)
  | .work₂, .work₁ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.work₂)
      (_root_.Turing.TM2.Stmt.push (Γ := Alphabet Γ Δ) Stack.work₁)
  | _, _ => .halt

/-- Compile a buffer-one move when the symbol alphabet is empty. -/
private def compileEmptyMove₁ {Γ Δ Λ : Type} (source : Stack)
    (nextEmpty : Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  match source with
  | .input => _root_.Turing.TM2.Stmt.pop .input setBuffer₁ <|
      _root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty)
  | .work₁ => _root_.Turing.TM2.Stmt.pop .work₁ setBuffer₁ <|
      _root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty)
  | _ => .halt

/-- Compile a buffer-two move when the symbol alphabet is empty. -/
private def compileEmptyMove₂ {Γ Δ Λ : Type} (source : Stack)
    (nextEmpty : Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  match source with
  | .input => _root_.Turing.TM2.Stmt.pop .input setBuffer₂ <|
      _root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty)
  | .work₂ => _root_.Turing.TM2.Stmt.pop .work₂ setBuffer₂ <|
      _root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty)
  | _ => .halt

/-- Compile an input pop copied to both work stacks through buffer one. -/
private def compileCopy {Γ Δ Λ : Type} (fallback : Γ)
    (nextEmpty : Λ) (nextCopied : Γ → Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  _root_.Turing.TM2.Stmt.pop .input setBuffer₁ <|
    _root_.Turing.TM2.Stmt.branch (fun state => state.buffer₁.isSome)
      (_root_.Turing.TM2.Stmt.push .work₁ (buffer₁Value fallback) <|
        _root_.Turing.TM2.Stmt.push .work₂ (buffer₁Value fallback) <|
          _root_.Turing.TM2.Stmt.goto
            (fun state => nextCopied (buffer₁Value fallback state)))
      (_root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty))

/-- Compile the necessarily empty copy operation for an empty alphabet. -/
private def compileEmptyCopy {Γ Δ Λ : Type} (nextEmpty : Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  _root_.Turing.TM2.Stmt.pop .input setBuffer₁ <|
    _root_.Turing.TM2.Stmt.goto (fun _ => nextEmpty)

/-- Compile a typed pop whose result and continuation use buffer one. -/
private def compilePop₁ {Γ Δ Λ : Type} (source : Stack)
    (nextEmpty : Λ) (nextSome : Γ → Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  match source with
  | .input => _root_.Turing.TM2.Stmt.pop .input setBuffer₁ <|
      _root_.Turing.TM2.Stmt.goto
        (fun state => state.buffer₁.elim nextEmpty nextSome)
  | .work₁ => _root_.Turing.TM2.Stmt.pop .work₁ setBuffer₁ <|
      _root_.Turing.TM2.Stmt.goto
        (fun state => state.buffer₁.elim nextEmpty nextSome)
  | _ => .halt

/-- Compile a typed pop whose result and continuation use buffer two. -/
private def compilePop₂ {Γ Δ Λ : Type} (source : Stack)
    (nextEmpty : Λ) (nextSome : Γ → Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  match source with
  | .work₂ => _root_.Turing.TM2.Stmt.pop .work₂ setBuffer₂ <|
      _root_.Turing.TM2.Stmt.goto
        (fun state => state.buffer₂.elim nextEmpty nextSome)
  | _ => .halt

/-- Compile unary decrement, storing the zero/successor test separately. -/
private def compileDec {Γ Δ Λ : Type} (counter : Stack)
    (nextZero nextSucc : Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  let stmt (pop : (ControlState Γ → Option Unit → ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) →
        _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ)) :=
    pop setCounterTest <|
      _root_.Turing.TM2.Stmt.branch (fun state => state.test)
        (_root_.Turing.TM2.Stmt.goto (fun _ => nextSucc))
        (_root_.Turing.TM2.Stmt.goto (fun _ => nextZero))
  match counter with
  | .counter₁ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.counter₁)
  | .counter₂ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.counter₂)
  | .counter₃ => stmt
      (_root_.Turing.TM2.Stmt.pop (Γ := Alphabet Γ Δ) Stack.counter₃)
  | _ => .halt

/-- Compile one builder instruction to a single concrete TM2 statement.

The nonempty-alphabet split is local to instructions that push a buffered
symbol. When the input alphabet is empty, all input/work stacks are necessarily
empty and the compiled statement takes the empty continuation without
constructing a fictitious symbol.
-/
def compileOp {Γ Δ Λ : Type} [Fintype Γ] (op : Op Γ Δ Λ) :
    _root_.Turing.TM2.Stmt (Alphabet Γ Δ) Λ (ControlState Γ) :=
  by
  classical
  exact match op with
  | .pushOutput symbol next =>
      _root_.Turing.TM2.Stmt.push .output (fun _ => symbol) <|
        _root_.Turing.TM2.Stmt.goto (fun _ => next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₁ (Classical.choice h) .input .work₁ nextEmpty nextMoved
      else compileEmptyMove₁ .input nextEmpty
  | .moveWork₁Input nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₁ (Classical.choice h) .work₁ .input nextEmpty nextMoved
      else compileEmptyMove₁ .work₁ nextEmpty
  | .moveInputWork₂ nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₂ (Classical.choice h) .input .work₂ nextEmpty nextMoved
      else compileEmptyMove₂ .input nextEmpty
  | .moveWork₂Input nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₂ (Classical.choice h) .work₂ .input nextEmpty nextMoved
      else compileEmptyMove₂ .work₂ nextEmpty
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₁ (Classical.choice h) .work₁ .work₂ nextEmpty nextMoved
      else compileEmptyMove₁ .work₁ nextEmpty
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      if h : Nonempty Γ then
        compileMove₂ (Classical.choice h) .work₂ .work₁ nextEmpty nextMoved
      else compileEmptyMove₂ .work₂ nextEmpty
  | .copyInputWorks nextEmpty nextCopied =>
      if h : Nonempty Γ then
        compileCopy (Classical.choice h) nextEmpty nextCopied
      else compileEmptyCopy nextEmpty
  | .popInput nextEmpty nextSome => compilePop₁ .input nextEmpty nextSome
  | .popWork₁ nextEmpty nextSome => compilePop₁ .work₁ nextEmpty nextSome
  | .popWork₂ nextEmpty nextSome => compilePop₂ .work₂ nextEmpty nextSome
  | .inc₁ next =>
      _root_.Turing.TM2.Stmt.push .counter₁ (fun _ => ()) <|
        _root_.Turing.TM2.Stmt.goto (fun _ => next)
  | .inc₂ next =>
      _root_.Turing.TM2.Stmt.push .counter₂ (fun _ => ()) <|
        _root_.Turing.TM2.Stmt.goto (fun _ => next)
  | .inc₃ next =>
      _root_.Turing.TM2.Stmt.push .counter₃ (fun _ => ()) <|
        _root_.Turing.TM2.Stmt.goto (fun _ => next)
  | .dec₁ nextZero nextSucc => compileDec .counter₁ nextZero nextSucc
  | .dec₂ nextZero nextSucc => compileDec .counter₂ nextZero nextSucc
  | .dec₃ nextZero nextSucc => compileDec .counter₃ nextZero nextSucc
  | .jump next => _root_.Turing.TM2.Stmt.goto (fun _ => next)
  | .halt => _root_.Turing.TM2.Stmt.load (fun _ => initialControl) .halt

/-- Compile a finite builder program to a finite TM2. -/
def compile {Γ Δ : Type} [Fintype Γ] (P : Program Γ Δ) :
    _root_.Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Γ Δ
  Λ := P.Label
  main := P.main
  ΛFin := P.labelFintype
  σ := ControlState Γ
  initialState := initialControl
  m label := compileOp (P.op label)

/-- Encode an independent builder configuration fieldwise as a TM2
configuration. -/
def encodeCfg {Γ Δ : Type} {P : Program Γ Δ} (c : BuilderCfg P) :
    _root_.Turing.TM2.Cfg (Alphabet Γ Δ) P.Label (ControlState Γ) where
  l := c.label
  var := ⟨c.buffer₁, c.buffer₂, c.test⟩
  stk
    | .input => c.input
    | .output => c.output
    | .work₁ => c.work₁
    | .work₂ => c.work₂
    | .counter₁ => c.counter₁
    | .counter₂ => c.counter₂
    | .counter₃ => c.counter₃

/-- The independent initial configuration for a builder input. -/
def initialCfg {Γ Δ : Type} (P : Program Γ Δ) (input : List Γ) : BuilderCfg P where
  label := some P.main
  buffer₁ := none
  buffer₂ := none
  test := false
  input := input
  output := []
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

/-- The independent successful halt configuration for a builder output.

All non-output stacks are empty. A builder must therefore restore or clear
its scratch stacks before it can establish a successful output run.
-/
def haltCfg {Γ Δ : Type} (P : Program Γ Δ) (output : List Δ) : BuilderCfg P where
  label := none
  buffer₁ := none
  buffer₂ := none
  test := false
  input := []
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

/-- Encoding a builder's initial configuration gives the compiled TM2 initial
configuration exactly. -/
@[simp] theorem encodeCfg_initialCfg {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) (input : List Γ) :
    encodeCfg (initialCfg P input) = _root_.Turing.initList (compile P) input := by
  unfold encodeCfg initialCfg _root_.Turing.initList
  congr 1
  funext stack
  cases stack <;> simp [compile]

/-- Encoding a builder's successful halt configuration gives the compiled
TM2 halt configuration exactly. -/
@[simp] theorem encodeCfg_haltCfg {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) (output : List Δ) :
    encodeCfg (haltCfg P output) = _root_.Turing.haltList (compile P) output := by
  unfold encodeCfg haltCfg _root_.Turing.haltList
  congr 1
  funext stack
  cases stack <;> simp [compile]

/-- One compiled TM2 step agrees with the independent builder semantics. -/
theorem compile_step {Γ Δ : Type} [Fintype Γ] (P : Program Γ Δ)
    (c : BuilderCfg P) :
    (compile P).step (encodeCfg c) = (step P c).map encodeCfg := by
  classical
  rcases c with ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
    counter₁, counter₂, counter₃⟩
  cases label with
  | none => simp [compile, encodeCfg, step]
  | some label =>
      cases hop : P.op label <;>
        simp only [compile, encodeCfg, step, hop, stepOp,
          _root_.Turing.FinTM2.step, _root_.Turing.TM2.step]
      case pushOutput =>
        simp [compileOp, encodeCfg]
        congr 3
        funext stack
        cases stack <;> simp [Function.update]
      case moveInputWork₁ =>
        cases input with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₁, compileEmptyMove₁, setBuffer₁,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₁, setBuffer₁, buffer₁Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case moveWork₁Input =>
        cases work₁ with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₁, compileEmptyMove₁, setBuffer₁,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₁, setBuffer₁, buffer₁Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case moveInputWork₂ =>
        cases input with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₂, compileEmptyMove₂, setBuffer₂,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₂, setBuffer₂, buffer₂Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case moveWork₂Input =>
        cases work₂ with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₂, compileEmptyMove₂, setBuffer₂,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₂, setBuffer₂, buffer₂Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case moveWork₁Work₂ =>
        cases work₁ with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₁, compileEmptyMove₁, setBuffer₁,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₁, setBuffer₁, buffer₁Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case moveWork₂Work₁ =>
        cases work₂ with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileMove₂, compileEmptyMove₂, setBuffer₂,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileMove₂, setBuffer₂, buffer₂Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case copyInputWorks =>
        cases input with
        | nil =>
            by_cases h : Nonempty Γ <;>
              simp [compileOp, h, compileCopy, compileEmptyCopy, setBuffer₁,
                encodeCfg]
        | cons symbol rest =>
            have h : Nonempty Γ := ⟨symbol⟩
            simp [compileOp, h, compileCopy, setBuffer₁, buffer₁Value,
              encodeCfg]
            congr 3
            funext stack
            cases stack <;> simp [Function.update]
      case popInput =>
        cases input <;> simp [compileOp, compilePop₁, setBuffer₁, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case popWork₁ =>
        cases work₁ <;> simp [compileOp, compilePop₁, setBuffer₁, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case popWork₂ =>
        cases work₂ <;> simp [compileOp, compilePop₂, setBuffer₂, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case inc₁ =>
        simp [compileOp, encodeCfg]
        congr 3
        funext stack
        cases stack <;> simp [Function.update]
      case inc₂ =>
        simp [compileOp, encodeCfg]
        congr 3
        funext stack
        cases stack <;> simp [Function.update]
      case inc₃ =>
        simp [compileOp, encodeCfg]
        congr 3
        funext stack
        cases stack <;> simp [Function.update]
      case dec₁ =>
        cases counter₁ <;>
          simp [compileOp, compileDec, setCounterTest, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case dec₂ =>
        cases counter₂ <;>
          simp [compileOp, compileDec, setCounterTest, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case dec₃ =>
        cases counter₃ <;>
          simp [compileOp, compileDec, setCounterTest, encodeCfg]
        all_goals
          congr 3
          funext stack
          cases stack <;> simp [Function.update]
      case jump => simp [compileOp, encodeCfg]
      case halt => simp [compileOp, initialControl, encodeCfg]

/-! ## Multi-step compiler agreement -/

/-- Project the exact stored step count of a transitive bounded evaluation.

This wrapper insulates builder proofs from the implementation details and
field order of Mathlib's {name}`EvalsToInTime.trans` constructor. -/
@[simp] theorem evalsToInTime_trans_steps {σ : Type} (f : σ → Option σ)
    (m₁ m₂ : Nat) (a b : σ) (c : Option σ)
    (first : _root_.StateTransition.EvalsToInTime f a (some b) m₁)
    (second : _root_.StateTransition.EvalsToInTime f b c m₂) :
    (_root_.StateTransition.EvalsToInTime.trans f m₁ m₂ a b c
      first second).steps = second.steps + first.steps := rfl

/-- View the fieldwise encoding at the configuration type of this compiler output. -/
private def compiledCfg {Γ Δ : Type} [Fintype Γ] (P : Program Γ Δ)
    (c : BuilderCfg P) : (compile P).Cfg :=
  encodeCfg c

/-- Lift one-step compiler agreement through option-valued iteration. -/
private theorem compile_iterate {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) (iterations : Nat) (c : Option (BuilderCfg P)) :
    (flip Option.bind (compile P).step)^[iterations] (c.map (compiledCfg P)) =
      ((flip Option.bind (step P))^[iterations] c).map (compiledCfg P) := by
  induction iterations generalizing c with
  | zero => rfl
  | succ iterations ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          simp only [Option.map_some, flip, Option.bind_some]
          rw [show (compile P).step (compiledCfg P c) =
            (step P c).map (compiledCfg P) by
              change (compile P).step (encodeCfg c) =
                (step P c).map encodeCfg
              exact compile_step P c]
          exact ih (step P c)

/-- Transport a bounded multi-step builder run to the compiled TM2 without
changing its exact evaluation witness or time bound. -/
def compile_evalsToInTime {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) {c c' : BuilderCfg P} {bound : Nat}
    (run : _root_.StateTransition.EvalsToInTime
      (step P) c (some c') bound) :
    _root_.StateTransition.EvalsToInTime
      (compile P).step (encodeCfg c) (some (encodeCfg c')) bound := by
  refine ⟨⟨run.steps, ?_⟩, run.steps_le_m⟩
  change (flip Option.bind (compile P).step)^[run.steps]
    (compiledCfg P c) = some (compiledCfg P c')
  rw [show compiledCfg P c = (some c).map (compiledCfg P) by rfl,
    compile_iterate P run.steps (some c)]
  simpa using congrArg (Option.map (compiledCfg P)) run.evals_in_steps

/-- Compiling a bounded builder evaluation preserves its stored exact step
count, not only its advertised upper bound. -/
@[simp] theorem compile_evalsToInTime_steps {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) {c c' : BuilderCfg P} {bound : Nat}
    (run : _root_.StateTransition.EvalsToInTime
      (step P) c (some c') bound) :
    (compile_evalsToInTime P run).steps = run.steps := rfl

/-- A proposition-valued bounded run of the independent builder semantics. -/
def BuilderOutputs {Γ Δ : Type} (P : Program Γ Δ)
    (f : List Γ → List Δ) (steps : List Γ → Nat) : Prop :=
  ∀ input, Nonempty (_root_.StateTransition.EvalsToInTime
    (step P) (initialCfg P input) (some (haltCfg P (f input))) (steps input))

/-- Exact bounded execution statement for a compiled builder. -/
def Outputs {Γ Δ : Type} [Fintype Γ] (P : Program Γ Δ)
    (f : List Γ → List Δ) (steps : List Γ → Nat) : Prop :=
  ∀ input, Nonempty (_root_.Turing.TM2OutputsInTime (compile P) input
    (some (f input)) (steps input))

namespace Outputs

/-- Compile a bounded independent-semantics run into the corresponding exact
TM2 output run. -/
theorem of_builder_run {Γ Δ : Type} [Fintype Γ] {P : Program Γ Δ}
    {f : List Γ → List Δ} {steps : List Γ → Nat}
    (run : BuilderOutputs P f steps) : Outputs P f steps := by
  intro input
  rcases run input with ⟨builderRun⟩
  refine ⟨?_⟩
  have compiledRun := compile_evalsToInTime P builderRun
  simpa [_root_.Turing.TM2OutputsInTime] using compiledRun

end Outputs

/-- A polynomial upper envelope for a builder's exact step function. -/
structure PolyBound {Γ : Type} (steps : List Γ → Nat) where
  polynomial : Polynomial ℕ
  bound : ∀ input, steps input ≤ polynomial.eval input.length

/-- Package exact builder execution and its polynomial envelope as Mathlib's
machine-level polynomial-time computability witness. -/
noncomputable def ComputableInPolyTime {Γ Δ : Type} [Fintype Γ]
    (P : Program Γ Δ) (f : List Γ → List Δ) (steps : List Γ → Nat)
    (hout : Outputs P f steps) (hpoly : PolyBound steps) :
    _root_.Turing.TM2ComputableInPolyTime id id f where
  tm := compile P
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Δ
  time := hpoly.polynomial
  outputsFun := fun input => by
    simp only [compile, id_eq, Equiv.refl]
    simp only [List.map_id]
    have run := Classical.choice (hout input)
    exact ⟨run.toEvalsTo, le_trans run.steps_le_m (hpoly.bound input)⟩

end CLRS.Chapter34.Turing.PolyBuilder
