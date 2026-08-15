import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRow

/-!
# Fixed controller for a runtime family of complete validity rows

Each row is preceded by one tick, so the outer family terminator cannot be
confused with the first delimiter of a row whose one-hot family is empty.
The row controller's clean finish label is redirected back to the family
loop. Thus the finite control is independent of the tableau height.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Explicit runtime input for an arbitrary family of complete rows. -/
def encodeAffineValidityRowFamily :
    List AffineValidityRowFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      .tick :: (encodeAffineValidityRowFrame frame ++
        encodeAffineValidityRowFamily rest)

/-- Standalone family input, including the final outer terminator. -/
def encodeAffineValidityRowFamilyInput
    (frames : List AffineValidityRowFrame) : List UnaryFrameSym :=
  encodeAffineValidityRowFamily frames ++ [.frameEnd]

/-- Exact forward byte stream of an arbitrary family of complete rows. -/
def affineValidityRowFamilyGateStream :
    List AffineValidityRowFrame → List CircuitSym
  | [] => []
  | frame :: rest =>
      affineValidityRowGateStream frame ++
        affineValidityRowFamilyGateStream rest

/-- The recursive family stream is ordinary flatMap over row frames. -/
theorem affineValidityRowFamilyGateStream_eq_flatMap
    (frames : List AffineValidityRowFrame) :
    affineValidityRowFamilyGateStream frames =
      frames.flatMap affineValidityRowGateStream := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineValidityRowFamilyGateStream, ih]

/-- Disjoint finite-control phases of the runtime row-family controller. -/
inductive AffineValidityRowFamilyLabel
  | load | clearMarker
  | row (label : AffineValidityRowLabel)
  | finish | invalid
deriving DecidableEq, Fintype

private def relabelRowOp :
    Op UnaryFrameSym CircuitSym AffineValidityRowLabel →
      Op UnaryFrameSym CircuitSym AffineValidityRowFamilyLabel
  | .pushOutput symbol next => .pushOutput symbol (.row next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.row next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.row next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.row nextEmpty) (fun symbol => .row (nextMoved symbol))
  | .inc₁ next => .inc₁ (.row next)
  | .inc₂ next => .inc₂ (.row next)
  | .inc₃ next => .inc₃ (.row next)
  | .dec₁ nextZero nextSucc => .dec₁ (.row nextZero) (.row nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.row nextZero) (.row nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.row nextZero) (.row nextSucc)
  | .jump next => .jump (.row next)
  | .halt => .halt

private abbrev rowExit : affineValidityRowRevProgram.Label :=
  .tail (.conjunction .finish)

/-- One fixed program for every runtime list of validity rows. -/
def affineValidityRowFamilyRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineValidityRowFamilyLabel
  main := .load
  op
    | .load => .popInput .invalid fun
        | .tick => .clearMarker
        | .separator => .invalid
        | .frameEnd => .finish
    | .clearMarker =>
        .popWork₁ (.row affineValidityRowRevProgram.main) (fun _ => .invalid)
    | .row (.tail (.conjunction .finish)) =>
        .popWork₁ .load (fun _ => .invalid)
    | .row label => relabelRowOp (affineValidityRowRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the row-family controller. -/
def affineValidityRowFamilyCfg (label : AffineValidityRowFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineValidityRowFamilyRevProgram where
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

/-- Clean loop-header configuration. -/
def affineValidityRowFamilyLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) :
    BuilderCfg affineValidityRowFamilyRevProgram :=
  affineValidityRowFamilyCfg .load none none false input output
    [] [] [] [] []

/-- Redirectable clean exit after the outer family terminator. -/
def affineValidityRowFamilyFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    BuilderCfg affineValidityRowFamilyRevProgram :=
  affineValidityRowFamilyCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

private def liftRowCfg (c : BuilderCfg affineValidityRowRevProgram) :
    BuilderCfg affineValidityRowFamilyRevProgram where
  label := c.label.map .row
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

private theorem relabelRow_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineValidityRowLabel)
    (c : BuilderCfg affineValidityRowRevProgram) :
    stepOp (relabelRowOp op) (liftRowCfg c) =
      liftRowCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelRowOp, liftRowCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineValidityRowFamily_op_row
    (label : AffineValidityRowLabel) (hexit : label ≠ rowExit) :
    affineValidityRowFamilyRevProgram.op (.row label) =
      relabelRowOp (affineValidityRowRevProgram.op label) := by
  cases label with
  | oneHot label => rfl
  | loader label => rfl
  | boolEq label => rfl
  | invalid => rfl
  | tail label =>
      cases label with
      | stack label => rfl
      | invalid => rfl
      | conjunction label =>
          cases label <;> simp_all [rowExit, affineValidityRowFamilyRevProgram]

private theorem liftRow_step (c : BuilderCfg affineValidityRowRevProgram)
    (hexit : c.label ≠ some rowExit) :
    step affineValidityRowFamilyRevProgram (liftRowCfg c) =
      Option.map liftRowCfg (step affineValidityRowRevProgram c) := by
  unfold step
  rw [show (liftRowCfg c).label = c.label.map .row by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ rowExit := by
        intro h
        apply hexit
        rw [hlabel, h]
      simp only [Option.map_some]
      rw [affineValidityRowFamily_op_row label hlabelExit]
      exact congrArg some
        (relabelRow_stepOp (affineValidityRowRevProgram.op label) c)

private theorem iterate_bind_none {P : Program UnaryFrameSym CircuitSym}
    (n : Nat) :
    (flip Option.bind (step P))^[n] (none : Option (BuilderCfg P)) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem rowExit_no_return
    (a b : BuilderCfg affineValidityRowRevProgram)
    (ha : a.label = some rowExit) (hb : b.label = some rowExit)
    (n : Nat) :
    (flip Option.bind (step affineValidityRowRevProgram))^[n]
        (step affineValidityRowRevProgram a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg affineValidityRowRevProgram :=
    { label := none, buffer₁ := none, buffer₂ := none, test := false
      input := input, output := output, work₁ := work₁, work₂ := work₂
      counter₁ := counter₁, counter₂ := counter₂,
      counter₃ := counter₃ }
  have hstep : step affineValidityRowRevProgram
      { label := some rowExit, buffer₁ := buffer₁, buffer₂ := buffer₂,
        test := test, input := input, output := output, work₁ := work₁,
        work₂ := work₂, counter₁ := counter₁,
        counter₂ := counter₂, counter₃ := counter₃ } = some halted := rfl
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step affineValidityRowRevProgram))^[n]
        (step affineValidityRowRevProgram halted) ≠ some b
      have hnone : step affineValidityRowRevProgram halted = none := rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem liftRow_iterations_to_finish
    {a b : BuilderCfg affineValidityRowRevProgram}
    (hb : b.label = some rowExit) : ∀ n : Nat,
    (flip Option.bind (step affineValidityRowRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineValidityRowFamilyRevProgram))^[n]
        (some (liftRowCfg a)) = some (liftRowCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineValidityRowRevProgram))^[n]
        (step affineValidityRowRevProgram a) = some b at h
      change (flip Option.bind (step affineValidityRowFamilyRevProgram))^[n]
        (step affineValidityRowFamilyRevProgram (liftRowCfg a)) =
          some (liftRowCfg b)
      have haexit : a.label ≠ some rowExit := by
        intro ha
        exact rowExit_no_return a b ha hb n h
      cases hsource : step affineValidityRowRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftRow_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

/-- Cost of the marker prelude, one complete row, and the loop-back step. -/
def affineValidityRowFamilyFrameSteps
    (frame : AffineValidityRowFrame) : Nat :=
  affineValidityRowUntilFinishSteps frame + 3

/-- Execute one marked row and return to the clean family loop header. -/
def affineValidityRowFamily_runOne (frame : AffineValidityRowFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (.tick :: (encodeAffineValidityRowFrame frame ++ tail)) output)
      (some (affineValidityRowFamilyLoopCfg tail
        ((affineValidityRowGateStream frame).reverse ++ output)))
      (affineValidityRowFamilyFrameSteps frame) := by
  have hstart : EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (.tick :: (encodeAffineValidityRowFrame frame ++ tail)) output)
      (some (liftRowCfg (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame ++ tail) output))) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  have sourceRun := affineValidityRow_runToFinish frame tail output
  have htarget : (affineValidityRowFinishCfg tail
      ((affineValidityRowGateStream frame).reverse ++ output)).label =
        some rowExit := rfl
  have hrow : EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (liftRowCfg (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame ++ tail) output))
      (some (liftRowCfg (affineValidityRowFinishCfg tail
        ((affineValidityRowGateStream frame).reverse ++ output))))
      (affineValidityRowUntilFinishSteps frame) := by
    refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
    exact liftRow_iterations_to_finish htarget sourceRun.steps
      sourceRun.evals_in_steps
  let gateOutput := (affineValidityRowGateStream frame).reverse ++ output
  have hloop : EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (liftRowCfg (affineValidityRowFinishCfg tail gateOutput))
      (some (affineValidityRowFamilyLoopCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughRow := EvalsToInTime.trans
    (step affineValidityRowFamilyRevProgram) 2
    (affineValidityRowUntilFinishSteps frame) _ _ _ hstart hrow
  let full := EvalsToInTime.trans
    (step affineValidityRowFamilyRevProgram)
    (affineValidityRowUntilFinishSteps frame + 2) 1
    _ (liftRowCfg (affineValidityRowFinishCfg tail gateOutput)) _
    throughRow hloop
  convert full using 1 <;>
    simp [affineValidityRowFamilyFrameSteps] <;> omega

/-- Runtime through the redirectable outer family terminator. -/
def affineValidityRowFamilyUntilFinishSteps :
    List AffineValidityRowFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineValidityRowFamilyFrameSteps frame +
        affineValidityRowFamilyUntilFinishSteps rest

/-- Execute every row and stop at the clean outer finish label. -/
def affineValidityRowFamily_runToFinish
    (frames : List AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (encodeAffineValidityRowFamily frames ++ .frameEnd :: tail) output)
      (some (affineValidityRowFamilyFinishCfg tail
        ((affineValidityRowFamilyGateStream frames).reverse ++ output)))
      (affineValidityRowFamilyUntilFinishSteps frames) := by
  induction frames generalizing output with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let gateOutput := (affineValidityRowGateStream frame).reverse ++ output
      have hfirst := affineValidityRowFamily_runOne frame
        (encodeAffineValidityRowFamily rest ++ .frameEnd :: tail) output
      have hrest := ih gateOutput
      let full := EvalsToInTime.trans
        (step affineValidityRowFamilyRevProgram)
        (affineValidityRowFamilyFrameSteps frame)
        (affineValidityRowFamilyUntilFinishSteps rest)
        _ (affineValidityRowFamilyLoopCfg
          (encodeAffineValidityRowFamily rest ++ .frameEnd :: tail) gateOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineValidityRowFamily, List.append_assoc]
      · simp [affineValidityRowFamilyGateStream, gateOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineValidityRowFamilyUntilFinishSteps]
        omega

/-- Standalone runtime, including the final halt instruction. -/
def affineValidityRowFamilyRevSteps
    (frames : List AffineValidityRowFrame) : Nat :=
  affineValidityRowFamilyUntilFinishSteps frames + 1

/-- Standalone exact execution of a runtime-length family of rows. -/
def affineValidityRowFamily_run (frames : List AffineValidityRowFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (encodeAffineValidityRowFamilyInput frames) output)
      (some (haltCfg affineValidityRowFamilyRevProgram
        ((affineValidityRowFamilyGateStream frames).reverse ++ output)))
      (affineValidityRowFamilyRevSteps frames) := by
  let gateOutput :=
    (affineValidityRowFamilyGateStream frames).reverse ++ output
  have hfinish := affineValidityRowFamily_runToFinish frames [] output
  have hhalt : EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyFinishCfg [] gateOutput)
      (some (haltCfg affineValidityRowFamilyRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step affineValidityRowFamilyRevProgram)
    (affineValidityRowFamilyUntilFinishSteps frames) 1
    _ (affineValidityRowFamilyFinishCfg [] gateOutput) _ hfinish hhalt
  convert full using 1 <;>
    simp [encodeAffineValidityRowFamilyInput,
      affineValidityRowFamilyRevSteps, Nat.add_comm] <;> omega

/-- One marked row is bounded quadratically by its exact marked encoding. -/
theorem affineValidityRowFamilyFrame_steps_le
    (frame : AffineValidityRowFrame) :
    affineValidityRowFamilyFrameSteps frame ≤
      2600 * (1 + (encodeAffineValidityRowFrame frame).length) ^ 2 := by
  have hrow := affineValidityRowRev_steps_le frame
  have hrow' : affineValidityRowUntilFinishSteps frame + 1 ≤
      2500 * (encodeAffineValidityRowFrame frame).length ^ 2 + 20 := by
    simpa [affineValidityRowRevSteps] using hrow
  have hsquare : (encodeAffineValidityRowFrame frame).length ^ 2 ≤
      (1 + (encodeAffineValidityRowFrame frame).length) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hscaled := Nat.mul_le_mul_left 2500 hsquare
  have hpositive0 :
      0 < (1 + (encodeAffineValidityRowFrame frame).length) ^ 2 :=
    pow_pos (by omega) 2
  have hpositive :
      1 ≤ (1 + (encodeAffineValidityRowFrame frame).length) ^ 2 := by omega
  have hmargin :
      2500 * (encodeAffineValidityRowFrame frame).length ^ 2 + 22 ≤
        2600 * (1 + (encodeAffineValidityRowFrame frame).length) ^ 2 := by
    omega
  unfold affineValidityRowFamilyFrameSteps
  omega

/-- The whole row family is quadratic in its exact delimiter-bearing input. -/
theorem affineValidityRowFamilyRev_steps_le
    (frames : List AffineValidityRowFrame) :
    affineValidityRowFamilyRevSteps frames ≤
      2600 * (encodeAffineValidityRowFamilyInput frames).length ^ 2 + 2 := by
  induction frames with
  | nil =>
      simp [affineValidityRowFamilyRevSteps,
        affineValidityRowFamilyUntilFinishSteps,
        encodeAffineValidityRowFamilyInput, encodeAffineValidityRowFamily]
  | cons frame rest ih =>
      have hframe := affineValidityRowFamilyFrame_steps_le frame
      let a := 1 + (encodeAffineValidityRowFrame frame).length
      let b := (encodeAffineValidityRowFamilyInput rest).length
      have hsquare : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
        calc
          a ^ 2 + b ^ 2 ≤ a ^ 2 + b ^ 2 + 2 * a * b := by omega
          _ = (a + b) ^ 2 := by ring
      have hlength :
          (encodeAffineValidityRowFamilyInput (frame :: rest)).length =
            a + b := by
        simp [a, b, encodeAffineValidityRowFamilyInput,
          encodeAffineValidityRowFamily, List.append_assoc]
        omega
      change affineValidityRowFamilyFrameSteps frame +
          affineValidityRowFamilyUntilFinishSteps rest + 1 ≤ _
      have hrest : affineValidityRowFamilyUntilFinishSteps rest + 1 ≤
          2600 * b ^ 2 + 2 := by
        simpa [affineValidityRowFamilyRevSteps, b] using ih
      have hframe' : affineValidityRowFamilyFrameSteps frame ≤
          2600 * a ^ 2 := by
        simpa [a] using hframe
      rw [hlength]
      calc
        affineValidityRowFamilyFrameSteps frame +
              affineValidityRowFamilyUntilFinishSteps rest + 1 ≤
            2600 * a ^ 2 + (2600 * b ^ 2 + 2) := by
          rw [Nat.add_assoc]
          exact Nat.add_le_add hframe' hrest
        _ = 2600 * (a ^ 2 + b ^ 2) + 2 := by ring
        _ ≤ 2600 * (a + b) ^ 2 + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2600 hsquare) 2

end CLRS.Chapter34.Turing.PolyBuilder
