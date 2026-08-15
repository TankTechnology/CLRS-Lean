import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily

/-!
# Runtime arbitrary-list disjunction and conjunction serialization

One fixed controller emits a false seed and reads a runtime list of ordered OR
frames.  Canonical frames execute the exact tail-first gate order of
`CircuitBuilder.disjunctionGateTrace`, including sparse and repeated wires.
The same controller also has an AND-first entry used by pair lookups before
switching, without halting, to a family of target disjunctions.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime operands for one ordered OR gate. -/
structure AffineOrFinPairFrame where
  left : Nat
  right : Nat
deriving DecidableEq, Repr

/-- Delimiter-bearing input for one ordered OR call. -/
def encodeAffineOrFinPairFrame (frame : AffineOrFinPairFrame) :
    List UnaryFrameSym :=
  [.frameEnd] ++
    encodeUnaryFrame [frame.left, 0, frame.right + 1] ++
    [.frameEnd]

/-- Runtime input for a finite coordinate family. -/
def encodeAffineOrFinFrames (frames : List AffineOrFinPairFrame) :
    List UnaryFrameSym :=
  frames.flatMap encodeAffineOrFinPairFrame

/-- Exact forward gate stream for arbitrary explicit coordinate frames. -/
def affineOrFinGateStream (frames : List AffineOrFinPairFrame) :
    List CircuitSym :=
  .constFalseMark :: frames.flatMap fun frame =>
    affineOrGateStream frame.left frame.right

/-- Runtime operands for one ordered AND gate. -/
structure AffineAndFinPairFrame where
  left : Nat
  right : Nat
deriving DecidableEq, Repr

/-- AND frames use a distinct top-level marker.  The loader fields are
ordered as carry/right and source/left because the embedded kernel emits
`.and source carry`. -/
def encodeAffineAndFinPairFrame (frame : AffineAndFinPairFrame) :
    List UnaryFrameSym :=
  [.tick] ++ encodeUnaryFrame [frame.right, 0, frame.left] ++ [.frameEnd]

def encodeAffineAndFinFrames (frames : List AffineAndFinPairFrame) :
    List UnaryFrameSym :=
  frames.flatMap encodeAffineAndFinPairFrame

def affineAndFinGateStream (frames : List AffineAndFinPairFrame) :
    List CircuitSym :=
  frames.flatMap fun frame => affineAndGateStream frame.right frame.left

/-- Structural relabeling of a component instruction. -/
private def relabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
    Op Γ Δ Λ → Op Γ Δ Μ
  | .pushOutput symbol next => .pushOutput symbol (tag next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (tag next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (tag next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .inc₁ next => .inc₁ (tag next)
  | .inc₂ next => .inc₂ (tag next)
  | .inc₃ next => .inc₃ (tag next)
  | .dec₁ nextZero nextSucc => .dec₁ (tag nextZero) (tag nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (tag nextZero) (tag nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (tag nextZero) (tag nextSucc)
  | .jump next => .jump (tag next)
  | .halt => .halt

/-- Fixed finite-control phases of the complete finite-family disjunction
serializer. -/
inductive AffineOrFinLabel
  | seed | check | clearMarker
  | andCheck | andClearMarker
  | narrowSeed | narrowCheck | narrowClearMarker | narrowOrSeed
  | narrowNotClearMarker
  | familyCheck | familyOpenClear | familySeed | familyCloseClear
  | loader (label : UnaryTripleLoaderLabel)
  | andLoader (label : UnaryTripleLoaderLabel)
  | narrowLoader (label : UnaryTripleLoaderLabel)
  | narrowNotLoader (label : UnaryTripleLoaderLabel)
  | orSeed
  | orCore (label : AffineExactlyOneFamilyLabel)
  | andCore (label : AffineExactlyOneFamilyLabel)
  | narrowOrCore (label : AffineExactlyOneFamilyLabel)
  | narrowNotCore (label : AffineExactlyOneFamilyLabel)
  | andToFamilyClear
  | finish | invalid
deriving DecidableEq, Fintype

/-- One program handles every family length and every wire index; all such
values are supplied by the runtime frame. -/
def affineOrFinRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineOrFinLabel
  main := .seed
  op
    | .seed => .pushOutput .constFalseMark .check
    | .check => .popInput .finish fun
        | .frameEnd => .clearMarker
        | .separator => .familyCloseClear
        | _ => .invalid
    | .clearMarker =>
        .popWork₁ (.loader unaryTripleLoaderProgram.main) (fun _ => .invalid)
    | .loader .ready => .popWork₁ .orSeed (fun _ => .invalid)
    | .loader label => relabelOp .loader
        (unaryTripleLoaderProgram.op label)
    | .orSeed =>
        .pushWork₁ .tick (.orCore (.kernel (.suffixOr .next)))
    | .orCore .finish => .popWork₁ .check (fun _ => .invalid)
    | .orCore label => relabelOp .orCore
        (affineExactlyOneFamilyRevProgram.op label)
    | .andCheck => .popInput .finish fun
        | .tick => .andClearMarker
        | .separator => .andToFamilyClear
        | _ => .invalid
    | .andClearMarker =>
        .popWork₁ (.andLoader unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .andLoader .ready =>
        .popWork₁ (.andCore (.kernel (.conjunction .push)))
          (fun _ => .invalid)
    | .andLoader label => relabelOp .andLoader
        (unaryTripleLoaderProgram.op label)
    | .andCore .finish => .popWork₁ .andCheck (fun _ => .invalid)
    | .andCore label => relabelOp .andCore
        (affineExactlyOneFamilyRevProgram.op label)
    | .andToFamilyClear => .popWork₁ .familyCheck (fun _ => .invalid)
    | .narrowSeed => .pushOutput .constFalseMark .narrowCheck
    | .narrowCheck => .popInput .invalid fun
        | .frameEnd => .narrowClearMarker
        | .tick => .narrowNotClearMarker
        | _ => .invalid
    | .narrowClearMarker =>
        .popWork₁ (.narrowLoader unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .narrowLoader .ready => .popWork₁ .narrowOrSeed (fun _ => .invalid)
    | .narrowLoader label => relabelOp .narrowLoader
        (unaryTripleLoaderProgram.op label)
    | .narrowOrSeed =>
        .pushWork₁ .tick (.narrowOrCore (.kernel (.suffixOr .next)))
    | .narrowOrCore .finish => .popWork₁ .narrowCheck (fun _ => .invalid)
    | .narrowOrCore label => relabelOp .narrowOrCore
        (affineExactlyOneFamilyRevProgram.op label)
    | .narrowNotClearMarker =>
        .popWork₁ (.narrowNotLoader unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .narrowNotLoader .ready =>
        .popWork₁ (.narrowNotCore (.kernel (.singleNot .push)))
          (fun _ => .invalid)
    | .narrowNotLoader label => relabelOp .narrowNotLoader
        (unaryTripleLoaderProgram.op label)
    | .narrowNotCore .finish => .popWork₁ .finish (fun _ => .invalid)
    | .narrowNotCore label => relabelOp .narrowNotCore
        (affineExactlyOneFamilyRevProgram.op label)
    | .familyCheck => .popInput .finish fun
        | .separator => .familyOpenClear
        | _ => .invalid
    | .familyOpenClear => .popWork₁ .familySeed (fun _ => .invalid)
    | .familySeed => .pushOutput .constFalseMark .check
    | .familyCloseClear => .popWork₁ .familyCheck (fun _ => .invalid)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the disjunction controller. -/
def affineOrFinCfg (label : AffineOrFinLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineOrFinRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Clean public entry for one complete runtime family. -/
def affineOrFinLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .seed none none false input output [] [] [] [] []

/-- Clean family loop after the true seed has been emitted. -/
def affineOrFinCheckCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .check none none false input output [] [] [] [] []

/-- Clean loop header for a runtime family of ordered AND gates. -/
def affineAndFinLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .andCheck none none false input output [] [] [] [] []

/-- Clean entry for a false-seeded OR family followed by one NOT gate. -/
def affineOrThenNotLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .narrowSeed none none false input output [] [] [] [] []

def affineOrThenNotCheckCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .narrowCheck none none false input output [] [] [] [] []

/-- Redirectable clean exit after the last coordinate. -/
def affineOrFinFinishCfg (output : List CircuitSym) :
    BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .finish none none false [] output [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineOrFinLabel) (c : BuilderCfg P) :
    BuilderCfg affineOrFinRevProgram where
  label := c.label.map tag
  buffer₁ := c.buffer₁
  buffer₂ := c.buffer₂
  test := c.test
  input := c.input
  output := c.output
  work₁ := c.work₁
  work₂ := c.work₂
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

private def liftLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .loader c

private def liftAndLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .andLoader c

private def liftNarrowLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .narrowLoader c

private def liftNarrowNotLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .narrowNotLoader c

private def liftOrCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .orCore c

private def liftAndCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .andCore c

private def liftNarrowOrCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .narrowOrCore c

private def liftNarrowNotCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .narrowNotCore c

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineOrFinLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (relabelOp tag op) (relabelCfg tag c) =
      relabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelOp, relabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineOrFin_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineOrFinRevProgram.op (.loader label) =
      relabelOp .loader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_andLoader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineOrFinRevProgram.op (.andLoader label) =
      relabelOp .andLoader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_narrowLoader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineOrFinRevProgram.op (.narrowLoader label) =
      relabelOp .narrowLoader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_narrowNotLoader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineOrFinRevProgram.op (.narrowNotLoader label) =
      relabelOp .narrowNotLoader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_orCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineOrFinRevProgram.op (.orCore label) =
      relabelOp .orCore (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_andCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineOrFinRevProgram.op (.andCore label) =
      relabelOp .andCore (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_narrowOrCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineOrFinRevProgram.op (.narrowOrCore label) =
      relabelOp .narrowOrCore
        (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem affineOrFin_op_narrowNotCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineOrFinRevProgram.op (.narrowNotCore label) =
      relabelOp .narrowNotCore
        (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineOrFinRevProgram] <;> rfl

private theorem liftLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineOrFinRevProgram (liftLoaderCfg c) =
      Option.map liftLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftLoaderCfg c).label = c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_loader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .loader (unaryTripleLoaderProgram.op label) c)

private theorem liftAndLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineOrFinRevProgram (liftAndLoaderCfg c) =
      Option.map liftAndLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftAndLoaderCfg c).label = c.label.map .andLoader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_andLoader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .andLoader (unaryTripleLoaderProgram.op label) c)

private theorem liftNarrowLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineOrFinRevProgram (liftNarrowLoaderCfg c) =
      Option.map liftNarrowLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftNarrowLoaderCfg c).label = c.label.map .narrowLoader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_narrowLoader label hlabelExit]
      exact congrArg some (relabel_stepOp .narrowLoader
        (unaryTripleLoaderProgram.op label) c)

private theorem liftNarrowNotLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineOrFinRevProgram (liftNarrowNotLoaderCfg c) =
      Option.map liftNarrowNotLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftNarrowNotLoaderCfg c).label =
    c.label.map .narrowNotLoader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_narrowNotLoader label hlabelExit]
      exact congrArg some (relabel_stepOp .narrowNotLoader
        (unaryTripleLoaderProgram.op label) c)

private theorem liftOr_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineOrFinRevProgram (liftOrCfg c) =
      Option.map liftOrCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftOrCfg c).label = c.label.map .orCore by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_orCore label hlabelExit]
      exact congrArg some
        (relabel_stepOp .orCore
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftAnd_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineOrFinRevProgram (liftAndCfg c) =
      Option.map liftAndCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftAndCfg c).label = c.label.map .andCore by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_andCore label hlabelExit]
      exact congrArg some
        (relabel_stepOp .andCore
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftNarrowOr_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineOrFinRevProgram (liftNarrowOrCfg c) =
      Option.map liftNarrowOrCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftNarrowOrCfg c).label = c.label.map .narrowOrCore by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_narrowOrCore label hlabelExit]
      exact congrArg some (relabel_stepOp .narrowOrCore
        (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftNarrowNot_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineOrFinRevProgram (liftNarrowNotCfg c) =
      Option.map liftNarrowNotCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftNarrowNotCfg c).label =
    c.label.map .narrowNotCore by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineOrFin_op_narrowNotCore label hlabelExit]
      exact congrArg some (relabel_stepOp .narrowNotCore
        (affineExactlyOneFamilyRevProgram.op label) c)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem haltExit_no_return
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt) (a b : BuilderCfg P)
    (ha : a.label = some exit) (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (step P a) ≠ some b := by
  intro n
  let halted : BuilderCfg P :=
    { a with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step P a = some halted := by
    unfold step
    rw [ha]
    simp [hop, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step P))^[n] (step P halted) ≠ some b
      have hnone : step P halted = none := rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem lift_iterations_to_haltExit
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineOrFinRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineOrFinRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineOrFinRevProgram))^[n]
        (some (tr a)) = some (tr b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step P))^[n] (step P a) = some b at h
      change (flip Option.bind (step affineOrFinRevProgram))^[n]
        (step affineOrFinRevProgram (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineAndFin_loader_run (frame : AffineAndFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftAndLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [frame.right, 0, frame.left] ++
          .frameEnd :: tail) output [] [] [] [] []))
      (some (liftAndLoaderCfg (unaryTripleLoaderReadyCfg
        frame.right 0 frame.left (.frameEnd :: tail) output [] [])))
      (unaryTripleLoaderSteps frame.right 0 frame.left) := by
  have sourceRun := unaryTripleLoader_run
    frame.right 0 frame.left (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg frame.right 0 frame.left
      (.frameEnd :: tail) output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftAndLoaderCfg liftAndLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineAndFin_and_run (frame : AffineAndFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftAndCfg (affineExactlyOneFamilyAndReadyCfg
        frame.right frame.left tail output))
      (some (liftAndCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineAndGateStream frame.right frame.left).reverse ++ output))))
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.right frame.left) := by
  have sourceRun := affineExactlyOneFamily_and_runToFinish
    frame.right frame.left tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineAndGateStream frame.right frame.left).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftAndCfg liftAnd_step htarget sourceRun.steps sourceRun.evals_in_steps

private def affineOrFin_loader_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [frame.left, 0, frame.right + 1] ++
          .frameEnd :: tail) output [] [] [] [] []))
      (some (liftLoaderCfg (unaryTripleLoaderReadyCfg
        frame.left 0 (frame.right + 1) (.frameEnd :: tail)
        output [] [])))
      (unaryTripleLoaderSteps frame.left 0 (frame.right + 1)) := by
  have sourceRun := unaryTripleLoader_run
    frame.left 0 (frame.right + 1) (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg
      frame.left 0 (frame.right + 1) (.frameEnd :: tail)
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftLoaderCfg liftLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineOrFin_or_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftOrCfg (affineExactlyOneFamilyOrReadyCfg
        frame.left frame.right tail output))
      (some (liftOrCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineOrGateStream frame.left frame.right).reverse ++ output))))
      (affineExactlyOneFamilyOrUntilFinishSteps
        frame.left frame.right) := by
  have sourceRun := affineExactlyOneFamily_or_runToFinish
    frame.left frame.right tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineOrGateStream frame.left frame.right).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftOrCfg liftOr_step htarget sourceRun.steps sourceRun.evals_in_steps

private def affineOrThenNot_loader_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftNarrowLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [frame.left, 0, frame.right + 1] ++
          .frameEnd :: tail) output [] [] [] [] []))
      (some (liftNarrowLoaderCfg (unaryTripleLoaderReadyCfg
        frame.left 0 (frame.right + 1) (.frameEnd :: tail)
        output [] [])))
      (unaryTripleLoaderSteps frame.left 0 (frame.right + 1)) := by
  have sourceRun := unaryTripleLoader_run
    frame.left 0 (frame.right + 1) (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg
      frame.left 0 (frame.right + 1) (.frameEnd :: tail)
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftNarrowLoaderCfg liftNarrowLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineOrThenNot_or_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftNarrowOrCfg (affineExactlyOneFamilyOrReadyCfg
        frame.left frame.right tail output))
      (some (liftNarrowOrCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineOrGateStream frame.left frame.right).reverse ++ output))))
      (affineExactlyOneFamilyOrUntilFinishSteps
        frame.left frame.right) := by
  have sourceRun := affineExactlyOneFamily_or_runToFinish
    frame.left frame.right tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineOrGateStream frame.left frame.right).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftNarrowOrCfg liftNarrowOr_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineOrThenNot_notLoader_run (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftNarrowNotLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [0, 0, source] ++ .frameEnd :: tail)
        output [] [] [] [] []))
      (some (liftNarrowNotLoaderCfg
        (unaryTripleLoaderReadyCfg 0 0 source (.frameEnd :: tail)
          output [] [])))
      (unaryTripleLoaderSteps 0 0 source) := by
  have sourceRun := unaryTripleLoader_run
    0 0 source (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg 0 0 source
      (.frameEnd :: tail) output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftNarrowNotLoaderCfg liftNarrowNotLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineOrThenNot_not_run (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (liftNarrowNotCfg
        (affineExactlyOneFamilyNotReadyCfg source tail output))
      (some (liftNarrowNotCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineNotGateStream source).reverse ++ output))))
      (affineExactlyOneFamilyNotUntilFinishSteps source) := by
  have sourceRun := affineExactlyOneFamily_not_runToFinish
    source tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineNotGateStream source).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftNarrowNotCfg liftNarrowNot_step htarget sourceRun.steps
      sourceRun.evals_in_steps

/-! ## Arbitrary ordered AND families -/

def affineAndFinPairSteps (frame : AffineAndFinPairFrame) : Nat :=
  4 + unaryTripleLoaderSteps frame.right 0 frame.left +
    affineExactlyOneFamilyAndUntilFinishSteps frame.right frame.left

private def affineAndFinPair_run (frame : AffineAndFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (encodeAffineAndFinPairFrame frame ++ tail) output)
      (some (affineAndFinLoopCfg tail
        ((affineAndGateStream frame.right frame.left).reverse ++ output)))
      (affineAndFinPairSteps frame) := by
  let loaderInput :=
    encodeUnaryFrame [frame.right, 0, frame.left] ++ .frameEnd :: tail
  let gateOutput :=
    (affineAndGateStream frame.right frame.left).reverse ++ output
  let loaderStart := liftAndLoaderCfg
    (unaryTripleLoaderCfg .load₁ none loaderInput output [] [] [] [] [])
  let loaderReady := liftAndLoaderCfg
    (unaryTripleLoaderReadyCfg frame.right 0 frame.left
      (.frameEnd :: tail) output [] [])
  let andStart := liftAndCfg
    (affineExactlyOneFamilyAndReadyCfg
      frame.right frame.left tail output)
  let andDone := liftAndCfg
    (affineExactlyOneFamilyFinishCfg tail gateOutput)
  have hmarker : EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (.tick :: loaderInput) output)
      (some loaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hloader : EvalsToInTime (step affineOrFinRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps frame.right 0 frame.left) := by
    simpa [loaderStart, loaderReady, loaderInput] using
      affineAndFin_loader_run frame tail output
  have hnormalize : EvalsToInTime (step affineOrFinRevProgram)
      loaderReady (some andStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hand : EvalsToInTime (step affineOrFinRevProgram)
      andStart (some andDone)
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.right frame.left) := by
    simpa [andStart, andDone, gateOutput] using
      affineAndFin_and_run frame tail output
  have hloop : EvalsToInTime (step affineOrFinRevProgram)
      andDone (some (affineAndFinLoopCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineOrFinRevProgram) 2 _ _
    loaderStart _ hmarker hloader
  let t₂ := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    loaderReady _ t₁ hnormalize
  let t₃ := EvalsToInTime.trans (step affineOrFinRevProgram) _ _ _
    andStart _ t₂ hand
  let full := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    andDone _ t₃ hloop
  convert full using 1
  · simp [encodeAffineAndFinPairFrame, loaderInput, List.append_assoc]
  · unfold affineAndFinPairSteps
    omega

def affineAndFinBodySteps : List AffineAndFinPairFrame → Nat
  | [] => 0
  | frame :: rest => affineAndFinPairSteps frame + affineAndFinBodySteps rest

def affineAndFinFrames_runToCheck
    (frames : List AffineAndFinPairFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (encodeAffineAndFinFrames frames ++ tail) output)
      (some (affineAndFinLoopCfg tail
        ((affineAndFinGateStream frames).reverse ++ output)))
      (affineAndFinBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        (affineAndGateStream frame.right frame.left).reverse ++ output
      have hframe := affineAndFinPair_run frame
        (encodeAffineAndFinFrames rest ++ tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineAndFinPairSteps frame) (affineAndFinBodySteps rest) _
        (affineAndFinLoopCfg
          (encodeAffineAndFinFrames rest ++ tail) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineAndFinFrames, List.append_assoc]
      · simp [affineAndFinGateStream, frameOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineAndFinBodySteps]
        omega

def affineAndFinUntilFinishSteps (frames : List AffineAndFinPairFrame) : Nat :=
  affineAndFinBodySteps frames + 1

def affineAndFin_runToFinish (frames : List AffineAndFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (encodeAffineAndFinFrames frames) output)
      (some (affineOrFinFinishCfg
        ((affineAndFinGateStream frames).reverse ++ output)))
      (affineAndFinUntilFinishSteps frames) := by
  have hframes := affineAndFinFrames_runToCheck frames [] output
  let gateOutput := (affineAndFinGateStream frames).reverse ++ output
  have hfinish : EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg [] gateOutput)
      (some (affineOrFinFinishCfg gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineAndFinBodySteps frames) 1 _
    (affineAndFinLoopCfg [] gateOutput) _
    (by simpa [gateOutput] using hframes) hfinish
  simpa [affineAndFinUntilFinishSteps, gateOutput, Nat.add_comm] using full

def affineAndFinRevSteps (frames : List AffineAndFinPairFrame) : Nat :=
  affineAndFinUntilFinishSteps frames + 1

def affineAndFin_run (frames : List AffineAndFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (encodeAffineAndFinFrames frames) output)
      (some (haltCfg affineOrFinRevProgram
        ((affineAndFinGateStream frames).reverse ++ output)))
      (affineAndFinRevSteps frames) := by
  let gateOutput := (affineAndFinGateStream frames).reverse ++ output
  have hfinish := affineAndFin_runToFinish frames output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineAndFinUntilFinishSteps frames) 1 _
    (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [affineAndFinRevSteps, gateOutput, Nat.add_comm] using full

def affineAndFinCanonicalFrames
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire)) :
    List AffineAndFinPairFrame :=
  pairs.map fun pair => { left := pair.1, right := pair.2 }

theorem affineAndFinCanonicalGateStream_eq_trace
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire)) :
    affineAndFinGateStream (affineAndFinCanonicalFrames pairs) =
      pairs.flatMap fun pair => encodeCircuitGate (.and pair.1 pair.2) := by
  unfold affineAndFinGateStream affineAndFinCanonicalFrames
  rw [List.flatMap_map]
  rfl

def affineAndFinCanonical_run
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire))
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (encodeAffineAndFinFrames (affineAndFinCanonicalFrames pairs)) output)
      (some (haltCfg affineOrFinRevProgram
        (((pairs.flatMap fun pair => encodeCircuitGate
          (.and pair.1 pair.2))).reverse ++ output)))
      (affineAndFinRevSteps (affineAndFinCanonicalFrames pairs)) := by
  simpa [affineAndFinCanonicalGateStream_eq_trace] using
    affineAndFin_run (affineAndFinCanonicalFrames pairs) output

/-- Exact cost of one marked OR frame. -/
def affineOrFinPairSteps (frame : AffineOrFinPairFrame) : Nat :=
  5 + unaryTripleLoaderSteps frame.left 0 (frame.right + 1) +
    affineExactlyOneFamilyOrUntilFinishSteps frame.left frame.right

private def affineOrFinPair_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinPairFrame frame ++ tail) output)
      (some (affineOrFinCheckCfg tail
        ((affineOrGateStream frame.left frame.right).reverse ++ output)))
      (affineOrFinPairSteps frame) := by
  let loaderInput :=
    encodeUnaryFrame [frame.left, 0, frame.right + 1] ++ .frameEnd :: tail
  let gateOutput :=
    (affineOrGateStream frame.left frame.right).reverse ++ output
  let loaderStart := liftLoaderCfg
    (unaryTripleLoaderCfg .load₁ none loaderInput output [] [] [] [] [])
  let loaderReady := liftLoaderCfg
    (unaryTripleLoaderReadyCfg frame.left 0 (frame.right + 1)
      (.frameEnd :: tail) output [] [])
  let orSeedCfg := affineOrFinCfg .orSeed none none false
    (.frameEnd :: tail) output [] []
    (List.replicate frame.left ()) []
    (List.replicate (frame.right + 1) ())
  let orStart := liftOrCfg
    (affineExactlyOneFamilyOrReadyCfg
      frame.left frame.right tail output)
  let orDone := liftOrCfg
    (affineExactlyOneFamilyFinishCfg tail gateOutput)
  have hmarker : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (.frameEnd :: loaderInput) output)
      (some loaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hloader : EvalsToInTime (step affineOrFinRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps frame.left 0 (frame.right + 1)) := by
    simpa [loaderStart, loaderReady, loaderInput] using
      affineOrFin_loader_run frame tail output
  have hnormalize : EvalsToInTime (step affineOrFinRevProgram)
      loaderReady (some orSeedCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      orSeedCfg (some orStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hor : EvalsToInTime (step affineOrFinRevProgram)
      orStart (some orDone)
      (affineExactlyOneFamilyOrUntilFinishSteps
        frame.left frame.right) := by
    simpa [orStart, orDone, gateOutput] using
      affineOrFin_or_run frame tail output
  have hloop : EvalsToInTime (step affineOrFinRevProgram)
      orDone (some (affineOrFinCheckCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineOrFinRevProgram) 2 _ _
    loaderStart _ hmarker hloader
  let t₂ := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    loaderReady _ t₁ hnormalize
  let t₃ := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    orSeedCfg _ t₂ hseed
  let t₄ := EvalsToInTime.trans (step affineOrFinRevProgram) _ _ _
    orStart _ t₃ hor
  let full := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    orDone _ t₄ hloop
  convert full using 1
  · simp [encodeAffineOrFinPairFrame, loaderInput, List.append_assoc]
  · unfold affineOrFinPairSteps
    omega

def affineOrFinFoldSteps : List AffineOrFinPairFrame → Nat
  | [] => 1
  | frame :: rest => affineOrFinPairSteps frame + affineOrFinFoldSteps rest

/-- Exact cost of a frame sequence when execution stops at the outer check
instead of consuming the following input symbol. -/
def affineOrFinBodySteps : List AffineOrFinPairFrame → Nat
  | [] => 0
  | frame :: rest => affineOrFinPairSteps frame + affineOrFinBodySteps rest

theorem affineOrFinFoldSteps_eq_body_add_one
    (frames : List AffineOrFinPairFrame) :
    affineOrFinFoldSteps frames = affineOrFinBodySteps frames + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineOrFinFoldSteps, affineOrFinBodySteps, ih]
      omega

/-- Execute explicit OR frames while preserving an arbitrary unary suffix and
stop before the outer check consumes its first symbol. -/
def affineOrFinFrames_runToCheck
    (frames : List AffineOrFinPairFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinFrames frames ++ tail) output)
      (some (affineOrFinCheckCfg tail
        (((frames.flatMap fun frame =>
          affineOrGateStream frame.left frame.right)).reverse ++ output)))
      (affineOrFinBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        (affineOrGateStream frame.left frame.right).reverse ++ output
      have hframe := affineOrFinPair_run frame
        (encodeAffineOrFinFrames rest ++ tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineOrFinPairSteps frame) (affineOrFinBodySteps rest) _
        (affineOrFinCheckCfg
          (encodeAffineOrFinFrames rest ++ tail) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineOrFinFrames, List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineOrFinBodySteps]
        omega

private def affineOrFinFrames_run (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinFrames frames) output)
      (some (affineOrFinFinishCfg
        (((frames.flatMap fun frame =>
          affineOrGateStream frame.left frame.right)).reverse ++ output)))
      (affineOrFinFoldSteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        (affineOrGateStream frame.left frame.right).reverse ++ output
      have hframe := affineOrFinPair_run frame
        (encodeAffineOrFinFrames rest) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineOrFinPairSteps frame) (affineOrFinFoldSteps rest) _
        (affineOrFinCheckCfg (encodeAffineOrFinFrames rest) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineOrFinFrames, List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineOrFinFoldSteps]
        omega

/-! ## Seed-free arbitrary OR sequences -/

/-- Exact forward stream of an arbitrary OR sequence without an initial false
seed.  This is the contextual form needed by stack pop. -/
def affineOrFinNoSeedGateStream (frames : List AffineOrFinPairFrame) :
    List CircuitSym :=
  frames.flatMap fun frame => affineOrGateStream frame.left frame.right

/-- Seed-free OR execution up to a suffix-preserving outer boundary. -/
def affineOrFinNoSeed_runToCheck (frames : List AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinFrames frames ++ tail) output)
      (some (affineOrFinCheckCfg tail
        ((affineOrFinNoSeedGateStream frames).reverse ++ output)))
      (affineOrFinBodySteps frames) := by
  simpa [affineOrFinNoSeedGateStream] using
    affineOrFinFrames_runToCheck frames tail output

/-- Exact runtime of the seed-free OR sequence through public halt. -/
def affineOrFinNoSeedRevSteps (frames : List AffineOrFinPairFrame) : Nat :=
  affineOrFinFoldSteps frames + 1

/-- Starting directly at the clean OR check state executes every explicit OR
frame without adding a false seed. -/
def affineOrFinNoSeed_run (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinFrames frames) output)
      (some (haltCfg affineOrFinRevProgram
        ((affineOrFinNoSeedGateStream frames).reverse ++ output)))
      (affineOrFinNoSeedRevSteps frames) := by
  let gateOutput := (affineOrFinNoSeedGateStream frames).reverse ++ output
  have hfinish := affineOrFinFrames_run frames output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineOrFinFoldSteps frames) 1 _ (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput, affineOrFinNoSeedGateStream] using hfinish) hhalt
  simpa [affineOrFinNoSeedRevSteps, gateOutput, Nat.add_comm] using full

/-- Contextual seed-free execution through the redirectable finish label. -/
def affineOrFinNoSeed_runToFinish (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffineOrFinFrames frames) output)
      (some (affineOrFinFinishCfg
        ((affineOrFinNoSeedGateStream frames).reverse ++ output)))
      (affineOrFinFoldSteps frames) := by
  simpa [affineOrFinNoSeedGateStream] using
    affineOrFinFrames_run frames output

def affineOrFinUntilFinishSteps (frames : List AffineOrFinPairFrame) : Nat :=
  affineOrFinFoldSteps frames + 1

/-- Execute an arbitrary ordered OR family with one fixed program. -/
def affineOrFin_runToFinish (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg (encodeAffineOrFinFrames frames) output)
      (some (affineOrFinFinishCfg
        ((affineOrFinGateStream frames).reverse ++ output)))
      (affineOrFinUntilFinishSteps frames) := by
  let seeded := .constFalseMark :: output
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg (encodeAffineOrFinFrames frames) output)
      (some (affineOrFinCheckCfg
        (encodeAffineOrFinFrames frames) seeded)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hframes := affineOrFinFrames_run frames seeded
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    1 (affineOrFinFoldSteps frames) _
    (affineOrFinCheckCfg (encodeAffineOrFinFrames frames) seeded) _
    hseed hframes
  convert full using 1
  · simp [affineOrFinGateStream, seeded, List.reverse_append,
      List.append_assoc]
  · simp [affineOrFinUntilFinishSteps]

/-- False-seeded OR execution up to a suffix-preserving outer boundary. -/
def affineOrFin_runToCheck (frames : List AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg (encodeAffineOrFinFrames frames ++ tail) output)
      (some (affineOrFinCheckCfg tail
        ((affineOrFinGateStream frames).reverse ++ output)))
      (1 + affineOrFinBodySteps frames) := by
  let seeded := .constFalseMark :: output
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg (encodeAffineOrFinFrames frames ++ tail) output)
      (some (affineOrFinCheckCfg
        (encodeAffineOrFinFrames frames ++ tail) seeded)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hframes := affineOrFinFrames_runToCheck frames tail seeded
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    1 (affineOrFinBodySteps frames) _
    (affineOrFinCheckCfg
      (encodeAffineOrFinFrames frames ++ tail) seeded) _
    hseed hframes
  convert full using 1
  · simp [affineOrFinGateStream, seeded, List.reverse_append,
      List.append_assoc]
  · omega

/-! ## Canonical frames and semantic trace agreement -/

def affineOrFinCanonicalFrames (start : Nat) :
    List CircuitBuilder.Wire → List AffineOrFinPairFrame
  | [] => []
  | wire :: rest =>
      affineOrFinCanonicalFrames start rest ++
        [{ left := wire
           right := (CircuitBuilder.disjunctionGateTrace start rest).wire }]

private def disjunctionBodyGateTrace (start : Nat) :
    List CircuitBuilder.Wire → List CircuitGate
  | [] => []
  | wire :: rest =>
      disjunctionBodyGateTrace start rest ++
        [.or wire (CircuitBuilder.disjunctionGateTrace start rest).wire]

private theorem disjunctionGateTrace_eq_body (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (CircuitBuilder.disjunctionGateTrace start wires).gates =
        [.const false] ++ disjunctionBodyGateTrace start wires := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        disjunctionBodyGateTrace, ih, List.append_assoc]

private theorem affineOrFinCanonicalBodyStream_eq_trace (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (affineOrFinCanonicalFrames start wires).flatMap (fun frame =>
        affineOrGateStream frame.left frame.right) =
      (disjunctionBodyGateTrace start wires).flatMap encodeCircuitGate := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      rw [show affineOrFinCanonicalFrames start (wire :: rest) =
        affineOrFinCanonicalFrames start rest ++
          [{ left := wire
             right := (CircuitBuilder.disjunctionGateTrace start rest).wire }] by
        rfl]
      rw [List.flatMap_append, ih]
      simp [disjunctionBodyGateTrace, affineOrGateStream,
        List.append_assoc]

/-- Canonical frames reproduce the exact ordered semantic disjunction trace. -/
theorem affineOrFinCanonicalGateStream_eq_trace (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    affineOrFinGateStream (affineOrFinCanonicalFrames start wires) =
      (CircuitBuilder.disjunctionGateTrace start wires).gates.flatMap
        encodeCircuitGate := by
  unfold affineOrFinGateStream
  rw [affineOrFinCanonicalBodyStream_eq_trace,
    disjunctionGateTrace_eq_body]
  simp [List.flatMap_append, encodeCircuitGate]

def affineOrFinRevSteps (frames : List AffineOrFinPairFrame) : Nat :=
  affineOrFinUntilFinishSteps frames + 1

def affineOrFin_run (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg (encodeAffineOrFinFrames frames) output)
      (some (haltCfg affineOrFinRevProgram
        ((affineOrFinGateStream frames).reverse ++ output)))
      (affineOrFinRevSteps frames) := by
  let gateOutput := (affineOrFinGateStream frames).reverse ++ output
  have hfinish := affineOrFin_runToFinish frames output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineOrFinUntilFinishSteps frames) 1 _
    (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  convert full using 1 <;> simp [affineOrFinRevSteps, gateOutput] <;> omega

def affineOrFinCanonical_run (start : Nat)
    (wires : List CircuitBuilder.Wire) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg
        (encodeAffineOrFinFrames
          (affineOrFinCanonicalFrames start wires)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionGateTrace start wires).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrFinRevSteps
        (affineOrFinCanonicalFrames start wires)) := by
  simpa [affineOrFinCanonicalGateStream_eq_trace] using
    affineOrFin_run (affineOrFinCanonicalFrames start wires) output

@[simp] theorem encodeAffineOrFinPairFrame_length
    (frame : AffineOrFinPairFrame) :
    (encodeAffineOrFinPairFrame frame).length =
      frame.left + frame.right + 6 := by
  simp [encodeAffineOrFinPairFrame, encodeUnaryFrame_length]
  omega

theorem affineOrFinPair_steps_le (frame : AffineOrFinPairFrame) :
    affineOrFinPairSteps frame ≤
      100 * (encodeAffineOrFinPairFrame frame).length := by
  simp [affineOrFinPairSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyOrUntilFinishSteps, affineOrRevCoreSteps,
    encodeAffineOrFinPairFrame_length]
  omega

theorem affineOrFinFold_steps_le (frames : List AffineOrFinPairFrame) :
    affineOrFinFoldSteps frames ≤
      100 * (encodeAffineOrFinFrames frames).length + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := affineOrFinPair_steps_le frame
      simp only [encodeAffineOrFinFrames] at ih
      simp only [affineOrFinFoldSteps, encodeAffineOrFinFrames,
        List.flatMap_cons, List.length_append]
      omega

/-- The seed-free controller remains linear in its explicit runtime input. -/
theorem affineOrFinNoSeedRev_steps_le
    (frames : List AffineOrFinPairFrame) :
    affineOrFinNoSeedRevSteps frames ≤
      100 * (encodeAffineOrFinFrames frames).length + 2 := by
  have h := affineOrFinFold_steps_le frames
  simp [affineOrFinNoSeedRevSteps]
  omega

theorem affineOrFinRev_steps_le (frames : List AffineOrFinPairFrame) :
    affineOrFinRevSteps frames ≤
      100 * (encodeAffineOrFinFrames frames).length + 3 := by
  have h := affineOrFinFold_steps_le frames
  simp [affineOrFinRevSteps, affineOrFinUntilFinishSteps]
  omega

/-! ## Non-halting families of arbitrary disjunctions -/

abbrev AffineOrFinGroup := List AffineOrFinPairFrame

/-- A group is delimited by separators; individual OR frames remain delimited
by `frameEnd`, so empty groups are unambiguous. -/
def encodeAffineOrFinGroup (group : AffineOrFinGroup) :
    List UnaryFrameSym :=
  .separator :: encodeAffineOrFinFrames group ++ [.separator]

def encodeAffineOrFinGroups (groups : List AffineOrFinGroup) :
    List UnaryFrameSym :=
  groups.flatMap encodeAffineOrFinGroup

def affineOrFinFamilyGateStream (groups : List AffineOrFinGroup) :
    List CircuitSym :=
  groups.flatMap affineOrFinGateStream

def affineOrFinFamilyLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineOrFinRevProgram :=
  affineOrFinCfg .familyCheck none none false input output [] [] [] [] []

def affineOrFinGroupSteps (group : AffineOrFinGroup) : Nat :=
  affineOrFinBodySteps group + 5

private def affineOrFinGroup_run (group : AffineOrFinGroup)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg (encodeAffineOrFinGroup group ++ tail) output)
      (some (affineOrFinFamilyLoopCfg tail
        ((affineOrFinGateStream group).reverse ++ output)))
      (affineOrFinGroupSteps group) := by
  let seeded := .constFalseMark :: output
  let frameInput := encodeAffineOrFinFrames group ++ .separator :: tail
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg (.separator :: frameInput) output)
      (some (affineOrFinCheckCfg frameInput seeded)) 3 :=
    ⟨⟨3, rfl⟩, le_rfl⟩
  have hframes := affineOrFinFrames_runToCheck group
    (.separator :: tail) seeded
  have hend : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (.separator :: tail)
        ((group.flatMap fun frame =>
          affineOrGateStream frame.left frame.right).reverse ++ seeded))
      (some (affineOrFinFamilyLoopCfg tail
        ((group.flatMap fun frame =>
          affineOrGateStream frame.left frame.right).reverse ++ seeded))) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let throughFrames := EvalsToInTime.trans (step affineOrFinRevProgram)
    3 (affineOrFinBodySteps group) _
    (affineOrFinCheckCfg frameInput seeded) _ hseed
    (by simpa [frameInput] using hframes)
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ 2 _
    (affineOrFinCheckCfg (.separator :: tail)
      ((group.flatMap fun frame =>
        affineOrGateStream frame.left frame.right).reverse ++ seeded)) _
    throughFrames hend
  convert full using 1
  · simp [encodeAffineOrFinGroup, frameInput, List.append_assoc]
  · simp [affineOrFinGateStream, seeded, List.reverse_append,
      List.append_assoc]
  · simp [affineOrFinGroupSteps]
    omega

def affineOrFinFamilyFoldSteps : List AffineOrFinGroup → Nat
  | [] => 1
  | group :: rest =>
      affineOrFinGroupSteps group + affineOrFinFamilyFoldSteps rest

/-- Exact family cost when execution stops before inspecting the suffix. -/
def affineOrFinFamilyBodySteps : List AffineOrFinGroup → Nat
  | [] => 0
  | group :: rest =>
      affineOrFinGroupSteps group + affineOrFinFamilyBodySteps rest

theorem affineOrFinFamilyFoldSteps_eq_body_add_one
    (groups : List AffineOrFinGroup) :
    affineOrFinFamilyFoldSteps groups =
      affineOrFinFamilyBodySteps groups + 1 := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp [affineOrFinFamilyFoldSteps, affineOrFinFamilyBodySteps, ih]
      omega

/-- Execute a family of independent disjunctions while preserving an arbitrary
unary suffix and stop at the family boundary. -/
def affineOrFinGroups_runToCheck (groups : List AffineOrFinGroup)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups groups ++ tail) output)
      (some (affineOrFinFamilyLoopCfg tail
        ((affineOrFinFamilyGateStream groups).reverse ++ output)))
      (affineOrFinFamilyBodySteps groups) := by
  induction groups generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons group rest ih =>
      let groupOutput := (affineOrFinGateStream group).reverse ++ output
      have hgroup := affineOrFinGroup_run group
        (encodeAffineOrFinGroups rest ++ tail) output
      have hrest := ih groupOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineOrFinGroupSteps group) (affineOrFinFamilyBodySteps rest) _
        (affineOrFinFamilyLoopCfg
          (encodeAffineOrFinGroups rest ++ tail) groupOutput) _
        hgroup hrest
      convert full using 1
      · simp [encodeAffineOrFinGroups, List.append_assoc]
      · simp [affineOrFinFamilyGateStream, groupOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineOrFinFamilyBodySteps]
        omega

private def affineOrFinGroups_run (groups : List AffineOrFinGroup)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg (encodeAffineOrFinGroups groups) output)
      (some (affineOrFinFinishCfg
        ((affineOrFinFamilyGateStream groups).reverse ++ output)))
      (affineOrFinFamilyFoldSteps groups) := by
  induction groups generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons group rest ih =>
      let groupOutput := (affineOrFinGateStream group).reverse ++ output
      have hgroup := affineOrFinGroup_run group
        (encodeAffineOrFinGroups rest) output
      have hrest := ih groupOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineOrFinGroupSteps group) (affineOrFinFamilyFoldSteps rest) _
        (affineOrFinFamilyLoopCfg
          (encodeAffineOrFinGroups rest) groupOutput) _ hgroup hrest
      convert full using 1
      · simp [encodeAffineOrFinGroups, List.append_assoc]
      · simp [affineOrFinFamilyGateStream, groupOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineOrFinFamilyFoldSteps]
        omega

def affineOrFinFamilyUntilFinishSteps
    (groups : List AffineOrFinGroup) : Nat :=
  affineOrFinFamilyFoldSteps groups

/-- Execute any runtime family of independent false-seeded disjunctions
without halting between fibers. -/
def affineOrFinFamily_runToFinish (groups : List AffineOrFinGroup)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg (encodeAffineOrFinGroups groups) output)
      (some (affineOrFinFinishCfg
        ((affineOrFinFamilyGateStream groups).reverse ++ output)))
      (affineOrFinFamilyUntilFinishSteps groups) := by
  simpa [affineOrFinFamilyUntilFinishSteps] using
    affineOrFinGroups_run groups output

def affineOrFinCanonicalGroupsFrom : Nat →
    List (List CircuitBuilder.Wire) → List AffineOrFinGroup
  | _, [] => []
  | start, wires :: rest =>
      let head := CircuitBuilder.disjunctionGateTrace start wires
      affineOrFinCanonicalFrames start wires ::
        affineOrFinCanonicalGroupsFrom (start + head.gates.length) rest

theorem affineOrFinCanonicalFamilyGateStream_eq_trace (start : Nat) :
    ∀ families : List (List CircuitBuilder.Wire),
      affineOrFinFamilyGateStream
          (affineOrFinCanonicalGroupsFrom start families) =
        (CircuitBuilder.disjunctionFamilyGateTrace start families).flatMap
          encodeCircuitGate := by
  intro families
  induction families generalizing start with
  | nil => rfl
  | cons wires rest ih =>
      simp only [affineOrFinCanonicalGroupsFrom,
        affineOrFinFamilyGateStream, List.flatMap_cons,
        CircuitBuilder.disjunctionFamilyGateTrace, List.flatMap_append]
      rw [affineOrFinCanonicalGateStream_eq_trace]
      change _ ++ affineOrFinFamilyGateStream
          (affineOrFinCanonicalGroupsFrom
            (start + (CircuitBuilder.disjunctionGateTrace start wires).gates.length)
            rest) = _
      rw [ih]

def affineOrFinFamilyRevSteps (groups : List AffineOrFinGroup) : Nat :=
  affineOrFinFamilyUntilFinishSteps groups + 1

def affineOrFinFamilyCanonical_run (start : Nat)
    (families : List (List CircuitBuilder.Wire))
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups
          (affineOrFinCanonicalGroupsFrom start families)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionFamilyGateTrace start families).flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrFinFamilyRevSteps
        (affineOrFinCanonicalGroupsFrom start families)) := by
  let groups := affineOrFinCanonicalGroupsFrom start families
  let gateOutput := (affineOrFinFamilyGateStream groups).reverse ++ output
  have hfinish := affineOrFinFamily_runToFinish groups output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineOrFinFamilyUntilFinishSteps groups) 1 _
    (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [groups, gateOutput, affineOrFinFamilyRevSteps,
    affineOrFinCanonicalFamilyGateStream_eq_trace, Nat.add_comm] using full

@[simp] theorem encodeAffineOrFinGroup_length (group : AffineOrFinGroup) :
    (encodeAffineOrFinGroup group).length =
      (encodeAffineOrFinFrames group).length + 2 := by
  simp [encodeAffineOrFinGroup]

theorem affineOrFinBody_steps_le (group : AffineOrFinGroup) :
    affineOrFinBodySteps group ≤
      100 * (encodeAffineOrFinFrames group).length := by
  induction group with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := affineOrFinPair_steps_le frame
      simp only [encodeAffineOrFinFrames] at ih
      simp only [affineOrFinBodySteps, encodeAffineOrFinFrames,
        List.flatMap_cons, List.length_append]
      omega

theorem affineOrFinGroup_steps_le (group : AffineOrFinGroup) :
    affineOrFinGroupSteps group ≤
      100 * (encodeAffineOrFinGroup group).length := by
  have h := affineOrFinBody_steps_le group
  simp [affineOrFinGroupSteps, encodeAffineOrFinGroup_length]
  omega

theorem affineOrFinFamilyFold_steps_le (groups : List AffineOrFinGroup) :
    affineOrFinFamilyFoldSteps groups ≤
      100 * (encodeAffineOrFinGroups groups).length + 1 := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have hgroup := affineOrFinGroup_steps_le group
      simp only [encodeAffineOrFinGroups] at ih
      simp only [affineOrFinFamilyFoldSteps, encodeAffineOrFinGroups,
        List.flatMap_cons, List.length_append]
      omega

theorem affineOrFinFamilyRev_steps_le (groups : List AffineOrFinGroup) :
    affineOrFinFamilyRevSteps groups ≤
      100 * (encodeAffineOrFinGroups groups).length + 2 := by
  have h := affineOrFinFamilyFold_steps_le groups
  simp [affineOrFinFamilyRevSteps,
    affineOrFinFamilyUntilFinishSteps]
  omega

/-! ## Continuous AND-then-OR-family execution -/

def encodeAffineAndThenOrInput (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) : List UnaryFrameSym :=
  encodeAffineAndFinFrames andFrames ++
    .separator :: encodeAffineOrFinGroups orGroups

def affineAndThenOrGateStream (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) : List CircuitSym :=
  affineAndFinGateStream andFrames ++ affineOrFinFamilyGateStream orGroups

def affineAndThenOrUntilFinishSteps
    (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) : Nat :=
  affineAndFinBodySteps andFrames + 2 + affineOrFinFamilyFoldSteps orGroups

/-- Execute an arbitrary AND phase and switch at one explicit separator to
an arbitrary family of independent disjunctions, without an intermediate
halt. -/
def affineAndThenOr_runToFinish (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (encodeAffineAndThenOrInput andFrames orGroups) output)
      (some (affineOrFinFinishCfg
        ((affineAndThenOrGateStream andFrames orGroups).reverse ++ output)))
      (affineAndThenOrUntilFinishSteps andFrames orGroups) := by
  let andOutput := (affineAndFinGateStream andFrames).reverse ++ output
  have hands := affineAndFinFrames_runToCheck andFrames
    (.separator :: encodeAffineOrFinGroups orGroups) output
  have hswitch : EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (.separator :: encodeAffineOrFinGroups orGroups) andOutput)
      (some (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups orGroups) andOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  have hors := affineOrFinGroups_run orGroups andOutput
  let throughSwitch := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineAndFinBodySteps andFrames) 2 _
    (affineAndFinLoopCfg
      (.separator :: encodeAffineOrFinGroups orGroups) andOutput) _
    (by simpa [encodeAffineAndThenOrInput, andOutput,
      List.append_assoc] using hands) hswitch
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ (affineOrFinFamilyFoldSteps orGroups) _
    (affineOrFinFamilyLoopCfg
      (encodeAffineOrFinGroups orGroups) andOutput) _
    throughSwitch hors
  convert full using 1
  · simp [encodeAffineAndThenOrInput, List.append_assoc]
  · simp [affineAndThenOrGateStream, andOutput,
      List.reverse_append, List.append_assoc]
  · simp [affineAndThenOrUntilFinishSteps]
    omega

/-- Continuous AND-then-OR-family execution that preserves an arbitrary unary
suffix and stops at the final family boundary. -/
def affineAndThenOr_runToCheck (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (encodeAffineAndThenOrInput andFrames orGroups ++ tail) output)
      (some (affineOrFinFamilyLoopCfg tail
        ((affineAndThenOrGateStream andFrames orGroups).reverse ++ output)))
      (affineAndFinBodySteps andFrames + 2 +
        affineOrFinFamilyBodySteps orGroups) := by
  let andOutput := (affineAndFinGateStream andFrames).reverse ++ output
  have hands := affineAndFinFrames_runToCheck andFrames
    (.separator :: encodeAffineOrFinGroups orGroups ++ tail) output
  have hswitch : EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (.separator :: encodeAffineOrFinGroups orGroups ++ tail) andOutput)
      (some (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups orGroups ++ tail) andOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  have hors := affineOrFinGroups_runToCheck orGroups tail andOutput
  let throughSwitch := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineAndFinBodySteps andFrames) 2 _
    (affineAndFinLoopCfg
      (.separator :: encodeAffineOrFinGroups orGroups ++ tail) andOutput) _
    (by simpa [encodeAffineAndThenOrInput, andOutput,
      List.append_assoc] using hands) hswitch
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ (affineOrFinFamilyBodySteps orGroups) _
    (affineOrFinFamilyLoopCfg
      (encodeAffineOrFinGroups orGroups ++ tail) andOutput) _
    throughSwitch hors
  convert full using 1
  · simp [encodeAffineAndThenOrInput, List.append_assoc]
  · simp [affineAndThenOrGateStream, andOutput,
      List.reverse_append, List.append_assoc]
  · omega

def affineAndThenOrRevSteps (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) : Nat :=
  affineAndThenOrUntilFinishSteps andFrames orGroups + 1

def affineAndThenOr_run (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (encodeAffineAndThenOrInput andFrames orGroups) output)
      (some (haltCfg affineOrFinRevProgram
        ((affineAndThenOrGateStream andFrames orGroups).reverse ++ output)))
      (affineAndThenOrRevSteps andFrames orGroups) := by
  let gateOutput :=
    (affineAndThenOrGateStream andFrames orGroups).reverse ++ output
  have hfinish := affineAndThenOr_runToFinish andFrames orGroups output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineAndThenOrUntilFinishSteps andFrames orGroups) 1 _
    (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [affineAndThenOrRevSteps, gateOutput, Nat.add_comm] using full

def affineAndThenOrCanonicalGroups (start : Nat)
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire))
    (families : List (List CircuitBuilder.Wire)) : List AffineOrFinGroup :=
  affineOrFinCanonicalGroupsFrom (start + pairs.length) families

theorem affineAndThenOrCanonicalGateStream_eq_trace (start : Nat)
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire))
    (families : List (List CircuitBuilder.Wire)) :
    affineAndThenOrGateStream (affineAndFinCanonicalFrames pairs)
        (affineAndThenOrCanonicalGroups start pairs families) =
      ((pairs.map fun pair => CircuitGate.and pair.1 pair.2) ++
        CircuitBuilder.disjunctionFamilyGateTrace
          (start + pairs.length) families).flatMap encodeCircuitGate := by
  rw [affineAndThenOrGateStream,
    affineAndFinCanonicalGateStream_eq_trace,
    affineAndThenOrCanonicalGroups,
    affineOrFinCanonicalFamilyGateStream_eq_trace,
    List.flatMap_append]
  rw [List.flatMap_map]

def affineAndThenOrCanonical_run (start : Nat)
    (pairs : List (CircuitBuilder.Wire × CircuitBuilder.Wire))
    (families : List (List CircuitBuilder.Wire))
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg
        (encodeAffineAndThenOrInput (affineAndFinCanonicalFrames pairs)
          (affineAndThenOrCanonicalGroups start pairs families)) output)
      (some (haltCfg affineOrFinRevProgram
        (((((pairs.map fun pair => CircuitGate.and pair.1 pair.2) ++
          CircuitBuilder.disjunctionFamilyGateTrace
            (start + pairs.length) families).flatMap
              encodeCircuitGate)).reverse ++ output)))
      (affineAndThenOrRevSteps (affineAndFinCanonicalFrames pairs)
        (affineAndThenOrCanonicalGroups start pairs families)) := by
  simpa [affineAndThenOrCanonicalGateStream_eq_trace] using
    affineAndThenOr_run (affineAndFinCanonicalFrames pairs)
      (affineAndThenOrCanonicalGroups start pairs families) output

@[simp] theorem encodeAffineAndFinPairFrame_length
    (frame : AffineAndFinPairFrame) :
    (encodeAffineAndFinPairFrame frame).length =
      frame.left + frame.right + 5 := by
  simp [encodeAffineAndFinPairFrame, encodeUnaryFrame_length]
  omega

theorem affineAndFinPair_steps_le (frame : AffineAndFinPairFrame) :
    affineAndFinPairSteps frame ≤
      100 * (encodeAffineAndFinPairFrame frame).length := by
  simp [affineAndFinPairSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyAndUntilFinishSteps, affineAndRevCoreSteps,
    encodeAffineAndFinPairFrame_length]
  omega

theorem affineAndFinBody_steps_le (frames : List AffineAndFinPairFrame) :
    affineAndFinBodySteps frames ≤
      100 * (encodeAffineAndFinFrames frames).length := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := affineAndFinPair_steps_le frame
      simp only [encodeAffineAndFinFrames] at ih
      simp only [affineAndFinBodySteps, encodeAffineAndFinFrames,
        List.flatMap_cons, List.length_append]
      omega

theorem affineAndFinRev_steps_le (frames : List AffineAndFinPairFrame) :
    affineAndFinRevSteps frames ≤
      100 * (encodeAffineAndFinFrames frames).length + 2 := by
  have h := affineAndFinBody_steps_le frames
  simp [affineAndFinRevSteps, affineAndFinUntilFinishSteps]
  omega

theorem affineAndThenOrRev_steps_le
    (andFrames : List AffineAndFinPairFrame)
    (orGroups : List AffineOrFinGroup) :
    affineAndThenOrRevSteps andFrames orGroups ≤
      100 * (encodeAffineAndThenOrInput andFrames orGroups).length + 2 := by
  have hands := affineAndFinBody_steps_le andFrames
  have hors := affineOrFinFamilyFold_steps_le orGroups
  simp [affineAndThenOrRevSteps, affineAndThenOrUntilFinishSteps,
    encodeAffineAndThenOrInput]
  omega

/-! ## Continuous false-seeded OR followed by NOT -/

private def affineOrThenNotPair_run (frame : AffineOrFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotCheckCfg
        (encodeAffineOrFinPairFrame frame ++ tail) output)
      (some (affineOrThenNotCheckCfg tail
        ((affineOrGateStream frame.left frame.right).reverse ++ output)))
      (affineOrFinPairSteps frame) := by
  let loaderInput :=
    encodeUnaryFrame [frame.left, 0, frame.right + 1] ++ .frameEnd :: tail
  let gateOutput :=
    (affineOrGateStream frame.left frame.right).reverse ++ output
  let loaderStart := liftNarrowLoaderCfg
    (unaryTripleLoaderCfg .load₁ none loaderInput output [] [] [] [] [])
  let loaderReady := liftNarrowLoaderCfg
    (unaryTripleLoaderReadyCfg frame.left 0 (frame.right + 1)
      (.frameEnd :: tail) output [] [])
  let orSeedCfg := affineOrFinCfg .narrowOrSeed none none false
    (.frameEnd :: tail) output [] []
    (List.replicate frame.left ()) []
    (List.replicate (frame.right + 1) ())
  let orStart := liftNarrowOrCfg
    (affineExactlyOneFamilyOrReadyCfg
      frame.left frame.right tail output)
  let orDone := liftNarrowOrCfg
    (affineExactlyOneFamilyFinishCfg tail gateOutput)
  have hmarker : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotCheckCfg (.frameEnd :: loaderInput) output)
      (some loaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hloader : EvalsToInTime (step affineOrFinRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps frame.left 0 (frame.right + 1)) := by
    simpa [loaderStart, loaderReady, loaderInput] using
      affineOrThenNot_loader_run frame tail output
  have hnormalize : EvalsToInTime (step affineOrFinRevProgram)
      loaderReady (some orSeedCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      orSeedCfg (some orStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hor : EvalsToInTime (step affineOrFinRevProgram)
      orStart (some orDone)
      (affineExactlyOneFamilyOrUntilFinishSteps
        frame.left frame.right) := by
    simpa [orStart, orDone, gateOutput] using
      affineOrThenNot_or_run frame tail output
  have hloop : EvalsToInTime (step affineOrFinRevProgram)
      orDone (some (affineOrThenNotCheckCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineOrFinRevProgram) 2 _ _
    loaderStart _ hmarker hloader
  let t₂ := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    loaderReady _ t₁ hnormalize
  let t₃ := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    orSeedCfg _ t₂ hseed
  let t₄ := EvalsToInTime.trans (step affineOrFinRevProgram) _ _ _
    orStart _ t₃ hor
  let full := EvalsToInTime.trans (step affineOrFinRevProgram) _ 1 _
    orDone _ t₄ hloop
  convert full using 1
  · simp [encodeAffineOrFinPairFrame, loaderInput, List.append_assoc]
  · unfold affineOrFinPairSteps
    omega

private def affineOrThenNotFrames_runToCheck
    (frames : List AffineOrFinPairFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotCheckCfg (encodeAffineOrFinFrames frames ++ tail) output)
      (some (affineOrThenNotCheckCfg tail
        (((frames.flatMap fun frame =>
          affineOrGateStream frame.left frame.right)).reverse ++ output)))
      (affineOrFinBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        (affineOrGateStream frame.left frame.right).reverse ++ output
      have hframe := affineOrThenNotPair_run frame
        (encodeAffineOrFinFrames rest ++ tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineOrFinRevProgram)
        (affineOrFinPairSteps frame) (affineOrFinBodySteps rest) _
        (affineOrThenNotCheckCfg
          (encodeAffineOrFinFrames rest ++ tail) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineOrFinFrames, List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineOrFinBodySteps]
        omega

def encodeAffineOrThenNotInput (frames : List AffineOrFinPairFrame)
    (source : Nat) : List UnaryFrameSym :=
  encodeAffineOrFinFrames frames ++
    .tick :: encodeUnaryFrame [0, 0, source] ++ [.frameEnd]

def affineOrThenNotGateStream (frames : List AffineOrFinPairFrame)
    (source : Nat) : List CircuitSym :=
  affineOrFinGateStream frames ++ affineNotGateStream source

def affineOrThenNotUntilFinishSteps
    (frames : List AffineOrFinPairFrame) (source : Nat) : Nat :=
  affineOrFinBodySteps frames + unaryTripleLoaderSteps 0 0 source +
    affineExactlyOneFamilyNotUntilFinishSteps source + 5

def affineOrThenNot_runToFinish (frames : List AffineOrFinPairFrame)
    (source : Nat) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotLoopCfg (encodeAffineOrThenNotInput frames source) output)
      (some (affineOrFinFinishCfg
        ((affineOrThenNotGateStream frames source).reverse ++ output)))
      (affineOrThenNotUntilFinishSteps frames source) := by
  let seeded := .constFalseMark :: output
  let notInput := encodeUnaryFrame [0, 0, source] ++ [.frameEnd]
  have hseed : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotLoopCfg
        (encodeAffineOrFinFrames frames ++ .tick :: notInput) output)
      (some (affineOrThenNotCheckCfg
        (encodeAffineOrFinFrames frames ++ .tick :: notInput) seeded)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hframes := affineOrThenNotFrames_runToCheck frames
    (.tick :: notInput) seeded
  let orOutput := (affineOrFinGateStream frames).reverse ++ output
  have horOutput :
      ((frames.flatMap fun frame =>
          affineOrGateStream frame.left frame.right).reverse ++ seeded) =
        orOutput := by
    simp [seeded, orOutput, affineOrFinGateStream,
      List.reverse_append, List.append_assoc]
  have hframes' := hframes
  rw [horOutput] at hframes'
  let loaderStart := liftNarrowNotLoaderCfg
    (unaryTripleLoaderCfg .load₁ none notInput orOutput [] [] [] [] [])
  let loaderReady := liftNarrowNotLoaderCfg
    (unaryTripleLoaderReadyCfg 0 0 source [.frameEnd] orOutput [] [])
  let notStart := liftNarrowNotCfg
    (affineExactlyOneFamilyNotReadyCfg source [] orOutput)
  let gateOutput :=
    (affineNotGateStream source).reverse ++ orOutput
  let notDone := liftNarrowNotCfg
    (affineExactlyOneFamilyFinishCfg [] gateOutput)
  have hmarker : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotCheckCfg (.tick :: notInput) orOutput)
      (some loaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hloader : EvalsToInTime (step affineOrFinRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps 0 0 source) := by
    simpa [loaderStart, loaderReady, notInput] using
      affineOrThenNot_notLoader_run source [] orOutput
  have hnormalize : EvalsToInTime (step affineOrFinRevProgram)
      loaderReady (some notStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hnot : EvalsToInTime (step affineOrFinRevProgram)
      notStart (some notDone)
      (affineExactlyOneFamilyNotUntilFinishSteps source) := by
    simpa [notStart, notDone, gateOutput] using
      affineOrThenNot_not_run source [] orOutput
  have hfinish : EvalsToInTime (step affineOrFinRevProgram)
      notDone (some (affineOrFinFinishCfg gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineOrFinRevProgram)
    1 (affineOrFinBodySteps frames) _
    (affineOrThenNotCheckCfg
      (encodeAffineOrFinFrames frames ++ .tick :: notInput) seeded) _
    hseed hframes'
  let t₂ := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ 2 _ (affineOrThenNotCheckCfg (.tick :: notInput) orOutput) _
    t₁ hmarker
  let t₃ := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ (unaryTripleLoaderSteps 0 0 source) _ loaderStart _ t₂ hloader
  let t₄ := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ 1 _ loaderReady _ t₃ hnormalize
  let t₅ := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ (affineExactlyOneFamilyNotUntilFinishSteps source) _
    notStart _ t₄ hnot
  let full := EvalsToInTime.trans (step affineOrFinRevProgram)
    _ 1 _ notDone _ t₅ hfinish
  convert full using 1
  · simp [encodeAffineOrThenNotInput, notInput, List.append_assoc]
  · simp [affineOrThenNotGateStream, affineOrFinGateStream,
      gateOutput, orOutput, List.reverse_append, List.append_assoc]
  · simp [affineOrThenNotUntilFinishSteps]
    omega

def affineOrThenNotRevSteps (frames : List AffineOrFinPairFrame)
    (source : Nat) : Nat :=
  affineOrThenNotUntilFinishSteps frames source + 1

def affineOrThenNot_run (frames : List AffineOrFinPairFrame)
    (source : Nat) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotLoopCfg (encodeAffineOrThenNotInput frames source) output)
      (some (haltCfg affineOrFinRevProgram
        ((affineOrThenNotGateStream frames source).reverse ++ output)))
      (affineOrThenNotRevSteps frames source) := by
  let gateOutput := (affineOrThenNotGateStream frames source).reverse ++ output
  have hfinish := affineOrThenNot_runToFinish frames source output
  have hhalt : EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFinishCfg gateOutput)
      (some (haltCfg affineOrFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have full := EvalsToInTime.trans (step affineOrFinRevProgram)
    (affineOrThenNotUntilFinishSteps frames source) 1 _
    (affineOrFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [affineOrThenNotRevSteps, gateOutput, Nat.add_comm] using full

theorem affineOrThenNotGateStream_eq_trace (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    let disjunction := CircuitBuilder.disjunctionGateTrace start wires
    affineOrThenNotGateStream (affineOrFinCanonicalFrames start wires)
        disjunction.wire =
      (disjunction.gates ++ [CircuitGate.not disjunction.wire]).flatMap
        encodeCircuitGate := by
  dsimp only
  rw [affineOrThenNotGateStream,
    affineOrFinCanonicalGateStream_eq_trace, List.flatMap_append]
  simp [affineNotGateStream]

def affineOrThenNotCanonical_run (start : Nat)
    (wires : List CircuitBuilder.Wire) (output : List CircuitSym) :
    let disjunction := CircuitBuilder.disjunctionGateTrace start wires
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotLoopCfg
        (encodeAffineOrThenNotInput
          (affineOrFinCanonicalFrames start wires) disjunction.wire) output)
      (some (haltCfg affineOrFinRevProgram
        ((((disjunction.gates ++ [CircuitGate.not disjunction.wire]).flatMap
          encodeCircuitGate)).reverse ++ output)))
      (affineOrThenNotRevSteps
        (affineOrFinCanonicalFrames start wires) disjunction.wire) := by
  dsimp only
  simpa [affineOrThenNotGateStream_eq_trace] using
    affineOrThenNot_run (affineOrFinCanonicalFrames start wires)
      (CircuitBuilder.disjunctionGateTrace start wires).wire output

theorem affineOrThenNotRev_steps_le (frames : List AffineOrFinPairFrame)
    (source : Nat) :
    affineOrThenNotRevSteps frames source ≤
      100 * (encodeAffineOrThenNotInput frames source).length + 2 := by
  have hframes := affineOrFinBody_steps_le frames
  simp [affineOrThenNotRevSteps, affineOrThenNotUntilFinishSteps,
    encodeAffineOrThenNotInput, unaryTripleLoaderSteps,
    affineExactlyOneFamilyNotUntilFinishSteps, affineNotRevCoreSteps,
    encodeUnaryFrame_length]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
