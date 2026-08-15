import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader

/-!
# Runtime family of arbitrary NOT gates

One fixed controller reads a delimiter-bearing runtime list of source wires
and reuses the established contextual NOT serializer for every element.  The
source list is operand data; it is not copied target circuit bytes.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- One source wire, preceded by a family marker and followed by the kernel's
explicit local boundary. -/
def encodeAffineNotFamilySource (source : Nat) : List UnaryFrameSym :=
  [.tick] ++ encodeUnaryFrame [0, 0, source] ++ [.frameEnd]

def encodeAffineNotFamilySources (sources : List Nat) : List UnaryFrameSym :=
  sources.flatMap encodeAffineNotFamilySource

def affineNotFamilyGateStream (sources : List Nat) : List CircuitSym :=
  sources.flatMap affineNotGateStream

theorem affineNotFamilyGateStream_eq_trace (sources : List Nat) :
    affineNotFamilyGateStream sources =
      (sources.map CircuitGate.not).flatMap encodeCircuitGate := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      change affineNotGateStream source ++ affineNotFamilyGateStream rest =
        encodeCircuitGate (.not source) ++
          (rest.map CircuitGate.not).flatMap encodeCircuitGate
      rw [show affineNotGateStream source =
        encodeCircuitGate (.not source) by rfl, ih]

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

inductive AffineNotFamilyLabel
  | check | clearMarker
  | loader (label : UnaryTripleLoaderLabel)
  | core (label : AffineExactlyOneFamilyLabel)
  | finish | invalid
deriving DecidableEq, Fintype

/-- Fixed finite controller for every finite source list. -/
def affineNotFamilyRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineNotFamilyLabel
  main := .check
  op
    | .check => .popInput .finish fun
        | .tick => .clearMarker
        | .frameEnd => .finish
        | .separator => .invalid
    | .clearMarker =>
        .popWork₁ (.loader unaryTripleLoaderProgram.main) (fun _ => .invalid)
    | .loader .ready =>
        .popWork₁ (.core (.kernel (.singleNot .push))) (fun _ => .invalid)
    | .loader label => relabelOp .loader (unaryTripleLoaderProgram.op label)
    | .core .finish => .popWork₁ .check (fun _ => .invalid)
    | .core label => relabelOp .core
        (affineExactlyOneFamilyRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

def affineNotFamilyCfg (label : AffineNotFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineNotFamilyRevProgram where
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

def affineNotFamilyLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineNotFamilyRevProgram :=
  affineNotFamilyCfg .check none none false input output [] [] [] [] []

def affineNotFamilyFinishCfg (output : List CircuitSym) :
    BuilderCfg affineNotFamilyRevProgram :=
  affineNotFamilyCfg .finish none none false [] output [] [] [] [] []

/-- Redirectable finish that has consumed an explicit family boundary and
preserves the runtime suffix for an enclosing controller. -/
def affineNotFamilyFinishInputCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineNotFamilyRevProgram :=
  affineNotFamilyCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineNotFamilyLabel) (c : BuilderCfg P) :
    BuilderCfg affineNotFamilyRevProgram where
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
    BuilderCfg affineNotFamilyRevProgram := relabelCfg .loader c

private def liftCoreCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineNotFamilyRevProgram := relabelCfg .core c

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineNotFamilyLabel)
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

private theorem affineNotFamily_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineNotFamilyRevProgram.op (.loader label) =
      relabelOp .loader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineNotFamilyRevProgram] <;> rfl

private theorem affineNotFamily_op_core
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineNotFamilyRevProgram.op (.core label) =
      relabelOp .core (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineNotFamilyRevProgram] <;> rfl

private theorem liftLoader_step (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineNotFamilyRevProgram (liftLoaderCfg c) =
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
      rw [affineNotFamily_op_loader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .loader (unaryTripleLoaderProgram.op label) c)

private theorem liftCore_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineNotFamilyRevProgram (liftCoreCfg c) =
      Option.map liftCoreCfg (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftCoreCfg c).label = c.label.map .core by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineNotFamily_op_core label hlabelExit]
      exact congrArg some (relabel_stepOp .core
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
    (tr : BuilderCfg P → BuilderCfg affineNotFamilyRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineNotFamilyRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineNotFamilyRevProgram))^[n]
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
      change (flip Option.bind (step affineNotFamilyRevProgram))^[n]
        (step affineNotFamilyRevProgram (tr a)) = some (tr b)
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

private def affineNotFamily_loader_run (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (liftLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [0, 0, source] ++ .frameEnd :: tail)
        output [] [] [] [] []))
      (some (liftLoaderCfg (unaryTripleLoaderReadyCfg
        0 0 source (.frameEnd :: tail) output [] [])))
      (unaryTripleLoaderSteps 0 0 source) := by
  have sourceRun := unaryTripleLoader_run
    0 0 source (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg 0 0 source
      (.frameEnd :: tail) output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftLoaderCfg liftLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineNotFamily_core_run (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (liftCoreCfg (affineExactlyOneFamilyNotReadyCfg source tail output))
      (some (liftCoreCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineNotGateStream source).reverse ++ output))))
      (affineExactlyOneFamilyNotUntilFinishSteps source) := by
  have sourceRun := affineExactlyOneFamily_not_runToFinish source tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineNotGateStream source).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftCoreCfg liftCore_step htarget sourceRun.steps sourceRun.evals_in_steps

def affineNotFamilySourceSteps (source : Nat) : Nat :=
  4 + unaryTripleLoaderSteps 0 0 source +
    affineExactlyOneFamilyNotUntilFinishSteps source

private def affineNotFamilySource_run (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg
        (encodeAffineNotFamilySource source ++ tail) output)
      (some (affineNotFamilyLoopCfg tail
        ((affineNotGateStream source).reverse ++ output)))
      (affineNotFamilySourceSteps source) := by
  let loaderInput :=
    encodeUnaryFrame [0, 0, source] ++ .frameEnd :: tail
  let gateOutput := (affineNotGateStream source).reverse ++ output
  let loaderStart := liftLoaderCfg
    (unaryTripleLoaderCfg .load₁ none loaderInput output [] [] [] [] [])
  let loaderReady := liftLoaderCfg
    (unaryTripleLoaderReadyCfg 0 0 source (.frameEnd :: tail) output [] [])
  let coreStart := liftCoreCfg
    (affineExactlyOneFamilyNotReadyCfg source tail output)
  let coreDone := liftCoreCfg
    (affineExactlyOneFamilyFinishCfg tail gateOutput)
  have hmarker : EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg (.tick :: loaderInput) output)
      (some loaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hloader : EvalsToInTime (step affineNotFamilyRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps 0 0 source) := by
    simpa [loaderStart, loaderReady, loaderInput] using
      affineNotFamily_loader_run source tail output
  have hnormalize : EvalsToInTime (step affineNotFamilyRevProgram)
      loaderReady (some coreStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcore : EvalsToInTime (step affineNotFamilyRevProgram)
      coreStart (some coreDone)
      (affineExactlyOneFamilyNotUntilFinishSteps source) := by
    simpa [coreStart, coreDone, gateOutput] using
      affineNotFamily_core_run source tail output
  have hloop : EvalsToInTime (step affineNotFamilyRevProgram)
      coreDone (some (affineNotFamilyLoopCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineNotFamilyRevProgram) 2 _ _
    loaderStart _ hmarker hloader
  let t₂ := EvalsToInTime.trans (step affineNotFamilyRevProgram) _ 1 _
    loaderReady _ t₁ hnormalize
  let t₃ := EvalsToInTime.trans (step affineNotFamilyRevProgram) _ _ _
    coreStart _ t₂ hcore
  let full := EvalsToInTime.trans (step affineNotFamilyRevProgram) _ 1 _
    coreDone _ t₃ hloop
  convert full using 1
  · simp [encodeAffineNotFamilySource, loaderInput, List.append_assoc]
  · simp [affineNotFamilySourceSteps]
    omega

def affineNotFamilyBodySteps : List Nat → Nat
  | [] => 0
  | source :: rest =>
      affineNotFamilySourceSteps source + affineNotFamilyBodySteps rest

def affineNotFamilySources_runToCheck (sources : List Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg
        (encodeAffineNotFamilySources sources ++ tail) output)
      (some (affineNotFamilyLoopCfg tail
        ((affineNotFamilyGateStream sources).reverse ++ output)))
      (affineNotFamilyBodySteps sources) := by
  induction sources generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons source rest ih =>
      let gateOutput := (affineNotGateStream source).reverse ++ output
      have hsource := affineNotFamilySource_run source
        (encodeAffineNotFamilySources rest ++ tail) output
      have hrest := ih gateOutput
      let full := EvalsToInTime.trans (step affineNotFamilyRevProgram)
        (affineNotFamilySourceSteps source) (affineNotFamilyBodySteps rest) _
        (affineNotFamilyLoopCfg
          (encodeAffineNotFamilySources rest ++ tail) gateOutput) _
        hsource hrest
      convert full using 1
      · simp [encodeAffineNotFamilySources, List.append_assoc]
      · simp [affineNotFamilyGateStream, gateOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineNotFamilyBodySteps]
        omega

def affineNotFamilyUntilFinishSteps (sources : List Nat) : Nat :=
  affineNotFamilyBodySteps sources + 1

/-- Contextual execution through an explicit `frameEnd`, preserving the
unconsumed suffix and stopping before the component halt instruction. -/
def affineNotFamily_runToFinishWithTail (sources : List Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg
        (encodeAffineNotFamilySources sources ++ .frameEnd :: tail) output)
      (some (affineNotFamilyFinishInputCfg tail
        ((affineNotFamilyGateStream sources).reverse ++ output)))
      (affineNotFamilyUntilFinishSteps sources) := by
  have hbody := affineNotFamilySources_runToCheck sources
    (.frameEnd :: tail) output
  let gateOutput := (affineNotFamilyGateStream sources).reverse ++ output
  have hfinish : EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg (.frameEnd :: tail) gateOutput)
      (some (affineNotFamilyFinishInputCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineNotFamilyRevProgram)
    (affineNotFamilyBodySteps sources) 1 _
    (affineNotFamilyLoopCfg (.frameEnd :: tail) gateOutput) _
    (by simpa [gateOutput] using hbody) hfinish
  simpa [affineNotFamilyUntilFinishSteps, gateOutput, Nat.add_comm] using full

def affineNotFamily_runToFinish (sources : List Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg (encodeAffineNotFamilySources sources) output)
      (some (affineNotFamilyFinishCfg
        ((affineNotFamilyGateStream sources).reverse ++ output)))
      (affineNotFamilyUntilFinishSteps sources) := by
  have hbody := affineNotFamilySources_runToCheck sources [] output
  let gateOutput := (affineNotFamilyGateStream sources).reverse ++ output
  have hfinish : EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg [] gateOutput)
      (some (affineNotFamilyFinishCfg gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineNotFamilyRevProgram)
    (affineNotFamilyBodySteps sources) 1 _
    (affineNotFamilyLoopCfg [] gateOutput) _
    (by simpa [gateOutput] using hbody) hfinish
  simpa [affineNotFamilyUntilFinishSteps, gateOutput, Nat.add_comm] using full

def affineNotFamilyRevSteps (sources : List Nat) : Nat :=
  affineNotFamilyUntilFinishSteps sources + 1

def affineNotFamily_run (sources : List Nat) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg (encodeAffineNotFamilySources sources) output)
      (some (haltCfg affineNotFamilyRevProgram
        ((affineNotFamilyGateStream sources).reverse ++ output)))
      (affineNotFamilyRevSteps sources) := by
  let gateOutput := (affineNotFamilyGateStream sources).reverse ++ output
  have hfinish := affineNotFamily_runToFinish sources output
  have hhalt : EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyFinishCfg gateOutput)
      (some (haltCfg affineNotFamilyRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineNotFamilyRevProgram)
    (affineNotFamilyUntilFinishSteps sources) 1 _
    (affineNotFamilyFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [affineNotFamilyRevSteps, gateOutput, Nat.add_comm] using full

private theorem sourceSteps_le (source : Nat) :
    affineNotFamilySourceSteps source ≤
      20 * (encodeAffineNotFamilySource source).length := by
  simp [affineNotFamilySourceSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyNotUntilFinishSteps, affineNotRevCoreSteps,
    encodeAffineNotFamilySource, encodeUnaryFrame, encodeUnaryFrameBlock]
  omega

private theorem bodySteps_le (sources : List Nat) :
    affineNotFamilyBodySteps sources ≤
      20 * (encodeAffineNotFamilySources sources).length := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      have hs := sourceSteps_le source
      have ih' : affineNotFamilyBodySteps rest ≤
          20 * (List.flatMap encodeAffineNotFamilySource rest).length := by
        simpa [encodeAffineNotFamilySources] using ih
      simp only [affineNotFamilyBodySteps, encodeAffineNotFamilySources,
        List.flatMap_cons, List.length_append]
      omega

theorem affineNotFamilyRev_steps_le (sources : List Nat) :
    affineNotFamilyRevSteps sources ≤
      20 * (encodeAffineNotFamilySources sources).length + 2 := by
  have h := bodySteps_le sources
  simp [affineNotFamilyRevSteps, affineNotFamilyUntilFinishSteps]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
