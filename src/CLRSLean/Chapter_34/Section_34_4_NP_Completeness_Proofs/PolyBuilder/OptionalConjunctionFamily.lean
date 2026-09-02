import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

/-!
# Runtime family of optional conjunction frames

Each entry either executes one complete tail-first conjunction or appends no
gates.  The branch is selected by a runtime marker in one fixed program.  A
distinct final marker makes consecutive zero-gate entries unambiguous.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

def encodeAffineOptionalConjunctionEntry :
    Option AffineConjunctionFrame → List UnaryFrameSym
  | none => [.separator]
  | some frame => .tick :: encodeAffineConjunctionFrame frame

def encodeAffineOptionalConjunctionEntries
    (frames : List (Option AffineConjunctionFrame)) : List UnaryFrameSym :=
  frames.flatMap encodeAffineOptionalConjunctionEntry

/-- The explicit final marker is not an entry and cannot be confused with a
zero-gate branch. -/
def encodeAffineOptionalConjunctionFamily
    (frames : List (Option AffineConjunctionFrame)) : List UnaryFrameSym :=
  encodeAffineOptionalConjunctionEntries frames ++ [.frameEnd]

def affineOptionalConjunctionEntryGateStream :
    Option AffineConjunctionFrame → List CircuitSym
  | none => []
  | some frame => affineConjunctionGateStream frame

def affineOptionalConjunctionFamilyGateStream
    (frames : List (Option AffineConjunctionFrame)) : List CircuitSym :=
  frames.flatMap affineOptionalConjunctionEntryGateStream

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

inductive AffineOptionalConjunctionFamilyLabel
  | check | clearNone | clearSome
  | conjunction (label : AffineConjunctionLabel)
  | finish | invalid
deriving DecidableEq, Fintype

def affineOptionalConjunctionFamilyRevProgram :
    Program UnaryFrameSym CircuitSym where
  Label := AffineOptionalConjunctionFamilyLabel
  main := .check
  op
    | .check => .popInput .invalid fun
        | .separator => .clearNone
        | .tick => .clearSome
        | .frameEnd => .finish
    | .clearNone => .popWork₁ .check (fun _ => .invalid)
    | .clearSome => .popWork₁
        (.conjunction affineConjunctionRevProgram.main) (fun _ => .invalid)
    | .conjunction .finish => .popWork₁ .check (fun _ => .invalid)
    | .conjunction label => relabelOp .conjunction
        (affineConjunctionRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

def affineOptionalConjunctionFamilyCfg
    (label : AffineOptionalConjunctionFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineOptionalConjunctionFamilyRevProgram where
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

def affineOptionalConjunctionFamilyLoopCfg
    (input : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineOptionalConjunctionFamilyRevProgram :=
  affineOptionalConjunctionFamilyCfg .check none none false input output
    [] [] [] [] []

def affineOptionalConjunctionFamilyFinishCfg (output : List CircuitSym) :
    BuilderCfg affineOptionalConjunctionFamilyRevProgram :=
  affineOptionalConjunctionFamilyCfg .finish (some .frameEnd) none false []
    output [] [] [] [] []

def affineOptionalConjunctionFamilyFinishInputCfg
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineOptionalConjunctionFamilyRevProgram :=
  affineOptionalConjunctionFamilyCfg .finish (some .frameEnd) none false tail
    output [] [] [] [] []

private def liftCfg (c : BuilderCfg affineConjunctionRevProgram) :
    BuilderCfg affineOptionalConjunctionFamilyRevProgram where
  label := c.label.map .conjunction
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

private theorem relabel_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineConjunctionLabel)
    (c : BuilderCfg affineConjunctionRevProgram) :
    stepOp (relabelOp AffineOptionalConjunctionFamilyLabel.conjunction op)
        (liftCfg c) = liftCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelOp, liftCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem outer_op_conjunction
    (label : AffineConjunctionLabel) (hexit : label ≠ .finish) :
    affineOptionalConjunctionFamilyRevProgram.op (.conjunction label) =
      relabelOp .conjunction (affineConjunctionRevProgram.op label) := by
  cases label <;>
    simp_all [affineOptionalConjunctionFamilyRevProgram] <;> rfl

private theorem lift_step (c : BuilderCfg affineConjunctionRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineOptionalConjunctionFamilyRevProgram (liftCfg c) =
      Option.map liftCfg (step affineConjunctionRevProgram c) := by
  unfold step
  rw [show (liftCfg c).label = c.label.map .conjunction by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [outer_op_conjunction label hlabelExit]
      exact congrArg some
        (relabel_stepOp (affineConjunctionRevProgram.op label) c)

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
    (a b : BuilderCfg affineConjunctionRevProgram)
    (ha : a.label = some .finish) (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineConjunctionRevProgram))^[n]
      (step affineConjunctionRevProgram a) ≠ some b := by
  intro n
  let halted : BuilderCfg affineConjunctionRevProgram :=
    { a with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step affineConjunctionRevProgram a = some halted := by
    unfold step
    rw [ha]
    simp [affineConjunctionRevProgram, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step affineConjunctionRevProgram))^[n]
        (step affineConjunctionRevProgram halted) ≠ some b
      have hnone : step affineConjunctionRevProgram halted = none := rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem lift_iterations_to_finish {a b :
    BuilderCfg affineConjunctionRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineConjunctionRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineOptionalConjunctionFamilyRevProgram))^[n]
        (some (liftCfg a)) = some (liftCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineConjunctionRevProgram))^[n]
        (step affineConjunctionRevProgram a) = some b at h
      change (flip Option.bind
        (step affineOptionalConjunctionFamilyRevProgram))^[n]
        (step affineOptionalConjunctionFamilyRevProgram (liftCfg a)) =
          some (liftCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact haltExit_no_return a b ha hb n h
      cases hsource : step affineConjunctionRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := lift_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def lift_runToFinish (frame : AffineConjunctionFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (liftCfg (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame ++ tail) output))
      (some (liftCfg (affineConjunctionFinishCfg tail
        ((affineConjunctionGateStream frame).reverse ++ output))))
      (affineConjunctionUntilFinishSteps frame) := by
  have sourceRun := affineConjunction_runToFinish frame tail output
  have htarget : (affineConjunctionFinishCfg tail
      ((affineConjunctionGateStream frame).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_finish htarget sourceRun.steps
    sourceRun.evals_in_steps

def affineOptionalConjunctionEntrySteps :
    Option AffineConjunctionFrame → Nat
  | none => 2
  | some frame => affineConjunctionUntilFinishSteps frame + 3

private def entry_run (optionalFrame : Option AffineConjunctionFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionEntry optionalFrame ++ tail) output)
      (some (affineOptionalConjunctionFamilyLoopCfg tail
        ((affineOptionalConjunctionEntryGateStream optionalFrame).reverse ++
          output)))
      (affineOptionalConjunctionEntrySteps optionalFrame) := by
  cases optionalFrame with
  | none => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | some frame =>
      let coreStart := liftCfg (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame ++ tail) output)
      let gateOutput := (affineConjunctionGateStream frame).reverse ++ output
      let coreDone := liftCfg (affineConjunctionFinishCfg tail gateOutput)
      have hstart : EvalsToInTime
          (step affineOptionalConjunctionFamilyRevProgram)
          (affineOptionalConjunctionFamilyLoopCfg
            (.tick :: encodeAffineConjunctionFrame frame ++ tail) output)
          (some coreStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have hcore : EvalsToInTime
          (step affineOptionalConjunctionFamilyRevProgram)
          coreStart (some coreDone)
          (affineConjunctionUntilFinishSteps frame) := by
        simpa [coreStart, coreDone, gateOutput] using
          lift_runToFinish frame tail output
      have hloop : EvalsToInTime
          (step affineOptionalConjunctionFamilyRevProgram)
          coreDone
          (some (affineOptionalConjunctionFamilyLoopCfg tail gateOutput)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let t₁ := EvalsToInTime.trans
        (step affineOptionalConjunctionFamilyRevProgram) 2 _ _
        coreStart _ hstart hcore
      let full := EvalsToInTime.trans
        (step affineOptionalConjunctionFamilyRevProgram) _ 1 _
        coreDone _ t₁ hloop
      convert full using 1
      · simp [encodeAffineOptionalConjunctionEntry]
      · simp [affineOptionalConjunctionEntryGateStream, gateOutput]
      · simp [affineOptionalConjunctionEntrySteps]
        omega

def affineOptionalConjunctionFamilyBodySteps :
    List (Option AffineConjunctionFrame) → Nat
  | [] => 0
  | frame :: rest => affineOptionalConjunctionEntrySteps frame +
      affineOptionalConjunctionFamilyBodySteps rest

private def entries_runToCheck (frames : List (Option AffineConjunctionFrame))
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionEntries frames ++ tail) output)
      (some (affineOptionalConjunctionFamilyLoopCfg tail
        ((affineOptionalConjunctionFamilyGateStream frames).reverse ++ output)))
      (affineOptionalConjunctionFamilyBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let gateOutput :=
        (affineOptionalConjunctionEntryGateStream frame).reverse ++ output
      have hframe := entry_run frame
        (encodeAffineOptionalConjunctionEntries rest ++ tail) output
      have hrest := ih gateOutput
      let full := EvalsToInTime.trans
        (step affineOptionalConjunctionFamilyRevProgram)
        (affineOptionalConjunctionEntrySteps frame)
        (affineOptionalConjunctionFamilyBodySteps rest) _
        (affineOptionalConjunctionFamilyLoopCfg
          (encodeAffineOptionalConjunctionEntries rest ++ tail) gateOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineOptionalConjunctionEntries, List.append_assoc]
      · simp [affineOptionalConjunctionFamilyGateStream, gateOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineOptionalConjunctionFamilyBodySteps]
        omega

def affineOptionalConjunctionFamilyUntilFinishSteps
    (frames : List (Option AffineConjunctionFrame)) : Nat :=
  affineOptionalConjunctionFamilyBodySteps frames + 1

/-- Contextual execution through the explicit family terminator, preserving
the suffix for the next generator phase. -/
def affineOptionalConjunctionFamily_runToFinishWithTail
    (frames : List (Option AffineConjunctionFrame))
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily frames ++ tail) output)
      (some (affineOptionalConjunctionFamilyFinishInputCfg tail
        ((affineOptionalConjunctionFamilyGateStream frames).reverse ++ output)))
      (affineOptionalConjunctionFamilyUntilFinishSteps frames) := by
  have hbody := entries_runToCheck frames (.frameEnd :: tail) output
  let gateOutput :=
    (affineOptionalConjunctionFamilyGateStream frames).reverse ++ output
  have hfinish : EvalsToInTime
      (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg (.frameEnd :: tail) gateOutput)
      (some (affineOptionalConjunctionFamilyFinishInputCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step affineOptionalConjunctionFamilyRevProgram)
    (affineOptionalConjunctionFamilyBodySteps frames) 1 _
    (affineOptionalConjunctionFamilyLoopCfg (.frameEnd :: tail) gateOutput) _
    (by simpa [gateOutput] using hbody) hfinish
  simpa [encodeAffineOptionalConjunctionFamily,
    affineOptionalConjunctionFamilyUntilFinishSteps, gateOutput,
    List.append_assoc, Nat.add_comm] using full

def affineOptionalConjunctionFamilyRevSteps
    (frames : List (Option AffineConjunctionFrame)) : Nat :=
  affineOptionalConjunctionFamilyUntilFinishSteps frames + 1

def affineOptionalConjunctionFamily_run
    (frames : List (Option AffineConjunctionFrame))
    (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily frames) output)
      (some (haltCfg affineOptionalConjunctionFamilyRevProgram
        ((affineOptionalConjunctionFamilyGateStream frames).reverse ++ output)))
      (affineOptionalConjunctionFamilyRevSteps frames) := by
  have hbody := entries_runToCheck frames [.frameEnd] output
  let gateOutput :=
    (affineOptionalConjunctionFamilyGateStream frames).reverse ++ output
  have hfinish : EvalsToInTime
      (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg [.frameEnd] gateOutput)
      (some (affineOptionalConjunctionFamilyFinishCfg gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hhalt : EvalsToInTime
      (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyFinishCfg gateOutput)
      (some (haltCfg affineOptionalConjunctionFamilyRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans
    (step affineOptionalConjunctionFamilyRevProgram)
    (affineOptionalConjunctionFamilyBodySteps frames) 1 _
    (affineOptionalConjunctionFamilyLoopCfg [.frameEnd] gateOutput) _
    (by simpa [gateOutput] using hbody) hfinish
  let full := EvalsToInTime.trans
    (step affineOptionalConjunctionFamilyRevProgram) _ 1 _
    (affineOptionalConjunctionFamilyFinishCfg gateOutput) _ t₁ hhalt
  simpa [encodeAffineOptionalConjunctionFamily,
    affineOptionalConjunctionFamilyRevSteps,
    affineOptionalConjunctionFamilyUntilFinishSteps,
    gateOutput, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

private theorem entrySteps_le (frame : Option AffineConjunctionFrame) :
    affineOptionalConjunctionEntrySteps frame ≤
      1005 * (encodeAffineOptionalConjunctionEntry frame).length ^ 2 := by
  cases frame with
  | none => norm_num [affineOptionalConjunctionEntrySteps,
      encodeAffineOptionalConjunctionEntry]
  | some frame =>
      have h := affineConjunctionRev_steps_le frame
      simp only [affineConjunctionRevSteps] at h
      let n := (encodeAffineConjunctionFrame frame).length
      have hn : 1 ≤ n := by
        simp [n]
        omega
      change affineConjunctionUntilFinishSteps frame + 3 ≤
        1005 * (n + 1) ^ 2
      calc
        affineConjunctionUntilFinishSteps frame + 3 =
            (affineConjunctionUntilFinishSteps frame + 1) + 2 := by omega
        _ ≤ (1000 * n ^ 2 + 2) + 2 := by
          exact Nat.add_le_add_right h 2
        _ ≤ 1005 * (n + 1) ^ 2 := by nlinarith

private theorem bodySteps_le (frames : List (Option AffineConjunctionFrame)) :
    affineOptionalConjunctionFamilyBodySteps frames ≤
      1005 * (encodeAffineOptionalConjunctionEntries frames).length ^ 2 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := entrySteps_le frame
      let a := (encodeAffineOptionalConjunctionEntry frame).length
      let b := (encodeAffineOptionalConjunctionEntries rest).length
      have hsquare : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
        rw [show (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b by ring]
        omega
      have hcalc : affineOptionalConjunctionEntrySteps frame +
          affineOptionalConjunctionFamilyBodySteps rest ≤
          1005 * (a + b) ^ 2 := by
        calc
          affineOptionalConjunctionEntrySteps frame +
              affineOptionalConjunctionFamilyBodySteps rest ≤
            1005 * a ^ 2 + 1005 * b ^ 2 :=
              Nat.add_le_add hframe ih
          _ = 1005 * (a ^ 2 + b ^ 2) := by ring
          _ ≤ 1005 * (a + b) ^ 2 := Nat.mul_le_mul_left 1005 hsquare
      simpa [affineOptionalConjunctionFamilyBodySteps,
        encodeAffineOptionalConjunctionEntries, a, b] using hcalc

theorem affineOptionalConjunctionFamilyRev_steps_le
    (frames : List (Option AffineConjunctionFrame)) :
    affineOptionalConjunctionFamilyRevSteps frames ≤
      1005 * (encodeAffineOptionalConjunctionFamily frames).length ^ 2 + 2 := by
  have h := bodySteps_le frames
  let n := (encodeAffineOptionalConjunctionEntries frames).length
  have hn : n ≤ n + 1 := by omega
  have hsquare : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left hn 2
  have hcalc : affineOptionalConjunctionFamilyBodySteps frames + 1 + 1 ≤
      1005 * (n + 1) ^ 2 + 2 := by
    calc
      affineOptionalConjunctionFamilyBodySteps frames + 1 + 1 =
          affineOptionalConjunctionFamilyBodySteps frames + 2 := by omega
      _ ≤ 1005 * n ^ 2 + 2 := Nat.add_le_add_right h 2
      _ ≤ 1005 * (n + 1) ^ 2 + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 1005 hsquare) 2
  simpa [affineOptionalConjunctionFamilyRevSteps,
    affineOptionalConjunctionFamilyUntilFinishSteps,
    encodeAffineOptionalConjunctionFamily, n] using hcalc

end CLRS.Chapter34.Turing.PolyBuilder
