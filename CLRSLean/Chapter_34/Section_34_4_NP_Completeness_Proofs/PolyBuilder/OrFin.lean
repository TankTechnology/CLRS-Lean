import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily

/-!
# Runtime arbitrary-list disjunction serialization

One fixed controller emits a false seed and reads a runtime list of ordered OR
frames.  Canonical frames execute the exact tail-first gate order of
`CircuitBuilder.disjunctionGateTrace`, including sparse and repeated wires.
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
  | loader (label : UnaryTripleLoaderLabel)
  | orSeed
  | orCore (label : AffineExactlyOneFamilyLabel)
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

private def liftOrCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineOrFinRevProgram := relabelCfg .orCore c

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

private theorem affineOrFin_op_orCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineOrFinRevProgram.op (.orCore label) =
      relabelOp .orCore (affineExactlyOneFamilyRevProgram.op label) := by
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

theorem affineOrFinRev_steps_le (frames : List AffineOrFinPairFrame) :
    affineOrFinRevSteps frames ≤
      100 * (encodeAffineOrFinFrames frames).length + 3 := by
  have h := affineOrFinFold_steps_le frames
  simp [affineOrFinRevSteps, affineOrFinUntilFinishSteps]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
