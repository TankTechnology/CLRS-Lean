import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CellFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr

/-!
# Fixed controller for one complete stack-validity block

One runtime stack frame contains the affine suffix-OR parameters followed by
an arbitrary framed cell family.  A single fixed finite controller loads the
mask counters, executes the suffix-OR kernel, redirects its clean halt label
to the established cell-family controller, and halts only after every cell.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime data for one mask followed by all cells of the same stack. -/
structure AffineStackFrame where
  start : Nat
  base : Nat
  count : Nat
  cells : List AffineCellFrame
deriving DecidableEq, Repr

/-- The mask loader stores `(count, start, base + count)` directly in the
three registers expected by `affineSuffixOrBodyCfg`. -/
def encodeAffineStackFrame (frame : AffineStackFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.count, frame.start, frame.base + frame.count] ++
    encodeAffineCellFamily frame.cells ++ [.frameEnd]

/-- Exact forward stream of one complete stack-validity block. -/
def affineStackGateStream (frame : AffineStackFrame) : List CircuitSym :=
  affineSuffixOrGateStream frame.start frame.base frame.count ++
    affineCellFamilyGateStream frame.cells

/-- Fixed phases of the initial three-field mask loader. -/
inductive AffineStackLoadLabel
  | load₁ | inc₁
  | load₂ | inc₂
  | load₃ | inc₃
  | clearBuffer | moveCount | seedMask
deriving DecidableEq, Fintype

/-- Grouped labels keep both reused controllers behind one constructor each. -/
inductive AffineStackLabel
  | load (phase : AffineStackLoadLabel)
  | mask (label : SequentialExactlyOneLabel)
  | cells (label : AffineCellFamilyLabel)
  | finish | invalid
deriving DecidableEq, Fintype

private def liftMaskOp :
    Op Unit CircuitSym SequentialExactlyOneLabel →
      Op UnaryFrameSym CircuitSym AffineStackLabel
  | .pushOutput symbol next => .pushOutput symbol (.mask next)
  | .pushWork₁ _ next => .pushWork₁ .tick (.mask next)
  | .pushWork₂ _ next => .pushWork₂ .tick (.mask next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .popInput nextEmpty nextMoved =>
      .popInput (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.mask nextEmpty) (fun _ => .mask (nextMoved ()))
  | .inc₁ next => .inc₁ (.mask next)
  | .inc₂ next => .inc₂ (.mask next)
  | .inc₃ next => .inc₃ (.mask next)
  | .dec₁ nextZero nextSucc => .dec₁ (.mask nextZero) (.mask nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.mask nextZero) (.mask nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.mask nextZero) (.mask nextSucc)
  | .jump next => .jump (.mask next)
  | .halt => .halt

private def liftCellFamilyOp :
    Op UnaryFrameSym CircuitSym AffineCellFamilyLabel →
      Op UnaryFrameSym CircuitSym AffineStackLabel
  | .pushOutput symbol next => .pushOutput symbol (.cells next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.cells next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.cells next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.cells nextEmpty) (fun symbol => .cells (nextMoved symbol))
  | .inc₁ next => .inc₁ (.cells next)
  | .inc₂ next => .inc₂ (.cells next)
  | .inc₃ next => .inc₃ (.cells next)
  | .dec₁ nextZero nextSucc => .dec₁ (.cells nextZero) (.cells nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.cells nextZero) (.cells nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.cells nextZero) (.cells nextSucc)
  | .jump next => .jump (.cells next)
  | .halt => .halt

/-- One fixed program for every choice of mask indices, height, and cell
family.  All such values occur only in the framed input. -/
def affineStackRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineStackLabel
  main := .load .load₁
  op
    | .load .load₁ => .popInput .finish fun
        | .tick => .load .inc₁
        | .separator => .load .load₂
        | .frameEnd => .finish
    | .load .inc₁ => .pushWork₂ .tick (.load .load₁)
    | .load .load₂ => .popInput .invalid fun
        | .tick => .load .inc₂
        | .separator => .load .load₃
        | .frameEnd => .invalid
    | .load .inc₂ => .inc₁ (.load .load₂)
    | .load .load₃ => .popInput .invalid fun
        | .tick => .load .inc₃
        | .separator => .load .clearBuffer
        | .frameEnd => .invalid
    | .load .inc₃ => .inc₃ (.load .load₃)
    | .load .clearBuffer =>
        .popWork₁ (.load .moveCount) (fun _ => .invalid)
    | .load .moveCount =>
        .moveWork₂Work₁ (.load .seedMask) (fun _ => .load .moveCount)
    | .load .seedMask =>
        .pushOutput .constFalseMark (.mask (.suffixOr .next))
    | .mask .halt => .jump (.cells (.load .load₁))
    | .mask label => liftMaskOp (sequentialExactlyOneRevProgram.op label)
    | .cells .finish =>
        .popWork₁ (.load .load₁) (fun _ => .invalid)
    | .cells label => liftCellFamilyOp (affineCellFamilyRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the stack controller. -/
def affineStackCfg (label : AffineStackLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) : BuilderCfg affineStackRevProgram where
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

/-- Clean entry configuration for a complete framed stack. -/
def affineStackLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineStackRevProgram :=
  affineStackCfg (.load .load₁) none none false input output
    [] [] [] [] []

private def liftCellFamilyCfg
    (c : BuilderCfg affineCellFamilyRevProgram) :
    BuilderCfg affineStackRevProgram where
  label := c.label.map .cells
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

private theorem liftCellFamily_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineCellFamilyLabel)
    (c : BuilderCfg affineCellFamilyRevProgram) :
    stepOp (liftCellFamilyOp op) (liftCellFamilyCfg c) =
      liftCellFamilyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [liftCellFamilyOp, liftCellFamilyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineStack_op_cells
    (label : AffineCellFamilyLabel) (hlabel : label ≠ .finish) :
    affineStackRevProgram.op (.cells label) =
      liftCellFamilyOp (affineCellFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineStackRevProgram]

private theorem liftCellFamily_step
    (c : BuilderCfg affineCellFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineStackRevProgram (liftCellFamilyCfg c) =
      Option.map liftCellFamilyCfg (step affineCellFamilyRevProgram c) := by
  unfold step
  rw [show (liftCellFamilyCfg c).label = c.label.map .cells by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineStack_op_cells label hlabelExit]
      change some
          (stepOp (liftCellFamilyOp (affineCellFamilyRevProgram.op label))
            (liftCellFamilyCfg c)) =
        some (liftCellFamilyCfg
          (stepOp (affineCellFamilyRevProgram.op label) c))
      exact congrArg some
        (liftCellFamily_stepOp (affineCellFamilyRevProgram.op label) c)

private def affineStackCellFamilyFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineStackRevProgram :=
  affineStackCfg (.cells .finish) (some .frameEnd) none false tail output
    [] [] [] [] []

private theorem cellFamily_iterate_bind_none (n : Nat) :
    (flip Option.bind (step affineCellFamilyRevProgram))^[n]
      (none : Option (BuilderCfg affineCellFamilyRevProgram)) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem cellFamily_finish_no_return
    (a b : BuilderCfg affineCellFamilyRevProgram)
    (ha : a.label = some .finish) (hb : b.label = some .finish)
    (n : Nat) :
    (flip Option.bind (step affineCellFamilyRevProgram))^[n]
        (step affineCellFamilyRevProgram a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg affineCellFamilyRevProgram := {
    label := none
    buffer₁ := none
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := work₁
    work₂ := work₂
    counter₁ := counter₁
    counter₂ := counter₂
    counter₃ := counter₃ }
  have hstep : step affineCellFamilyRevProgram
      { label := some AffineCellFamilyLabel.finish
        buffer₁ := buffer₁, buffer₂ := buffer₂, test := test
        input := input, output := output, work₁ := work₁, work₂ := work₂
        counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := rfl
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineCellFamilyRevProgram))^[n]
          (step affineCellFamilyRevProgram halted) ≠ some b
      have hnone :
          step affineCellFamilyRevProgram halted = none := rfl
      rw [hnone, cellFamily_iterate_bind_none]
      simp

private theorem liftCellFamily_iterations_to_finish
    {a b : BuilderCfg affineCellFamilyRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineCellFamilyRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineStackRevProgram))^[n]
        (some (liftCellFamilyCfg a)) = some (liftCellFamilyCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change
        (flip Option.bind (step affineCellFamilyRevProgram))^[n]
          (step affineCellFamilyRevProgram a) = some b at h
      change
        (flip Option.bind (step affineStackRevProgram))^[n]
          (step affineStackRevProgram (liftCellFamilyCfg a)) =
            some (liftCellFamilyCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact cellFamily_finish_no_return a b ha hb n h
      cases hstep : step affineCellFamilyRevProgram a with
      | none =>
          rw [hstep, cellFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftCellFamily_step a haexit
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih h

private def affineStackCellFamily_runToFinish
    (frames : List AffineCellFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (liftCellFamilyCfg
        (affineCellFamilyLoopCfg
          (encodeAffineCellFamily frames ++ .frameEnd :: tail) output))
      (some (affineStackCellFamilyFinishCfg tail
        ((affineCellFamilyGateStream frames).reverse ++ output)))
      (affineCellFamilyUntilEndSteps frames) := by
  have sourceRun := affineCellFamily_runToFinish frames tail output
  have htarget : (affineCellFamilyFinishCfg tail
      ((affineCellFamilyGateStream frames).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have lifted := liftCellFamily_iterations_to_finish htarget
    sourceRun.steps sourceRun.evals_in_steps
  have hfinishLift : liftCellFamilyCfg
      (affineCellFamilyFinishCfg tail
        ((affineCellFamilyGateStream frames).reverse ++ output)) =
      affineStackCellFamilyFinishCfg tail
        ((affineCellFamilyGateStream frames).reverse ++ output) := rfl
  rw [hfinishLift] at lifted
  exact lifted

private def liftMaskCfg (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram) :
    BuilderCfg affineStackRevProgram where
  label := c.label.map .mask
  buffer₁ := c.buffer₁.map fun _ => .tick
  buffer₂ := c.buffer₂.map fun _ => .tick
  test := c.test
  input := c.input.map (fun _ => .tick) ++ tail
  output := c.output
  work₁ := c.work₁.map fun _ => .tick
  work₂ := c.work₂.map fun _ => .tick
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

private def isAffineSuffixOrCont : SequentialExactlyOneCont → Prop
  | .suffixOrCarry | .suffixOrWire => True
  | _ => False

private def isAffineSuffixOrKernelLabel :
    SequentialExactlyOneLabel → Prop
  | .encode _ cont | .save _ cont | .pushArg _ cont | .pushEnd _ cont
  | .restore _ cont | .restoreInc _ cont | .resume cont =>
      isAffineSuffixOrCont cont
  | .suffixOr _ | .clear₁ | .clear₂ | .clear₃ | .halt
  | .invalid => True
  | _ => False

private def isAffineSuffixOrKernelCfg
    (c : BuilderCfg sequentialExactlyOneRevProgram) : Prop :=
  match c.label with
  | none => True
  | some label => isAffineSuffixOrKernelLabel label

private def preservesMaskTail :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .moveInputWork₁ .. | .moveWork₁Input ..
  | .moveInputWork₂ .. | .moveWork₂Input ..
  | .copyInputWorks .. | .popInput .. => False
  | _ => True

private theorem liftMask_stepOp (tail : List UnaryFrameSym)
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hsafe : preservesMaskTail op) :
    stepOp (liftMaskOp op) (liftMaskCfg tail c) =
      liftMaskCfg tail (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => rfl
  | pushWork₁ => rfl
  | pushWork₂ => rfl
  | moveInputWork₁ => simp [preservesMaskTail] at hsafe
  | moveWork₁Input => simp [preservesMaskTail] at hsafe
  | moveInputWork₂ => simp [preservesMaskTail] at hsafe
  | moveWork₂Input => simp [preservesMaskTail] at hsafe
  | moveWork₁Work₂ => cases work₁ <;> rfl
  | moveWork₂Work₁ => cases work₂ <;> rfl
  | copyInputWorks => simp [preservesMaskTail] at hsafe
  | popInput => simp [preservesMaskTail] at hsafe
  | popWork₁ => cases work₁ <;> rfl
  | popWork₂ => cases work₂ <;> rfl
  | inc₁ => rfl
  | inc₂ => rfl
  | inc₃ => rfl
  | dec₁ => cases counter₁ <;> rfl
  | dec₂ => cases counter₂ <;> rfl
  | dec₃ => cases counter₃ <;> rfl
  | jump => rfl
  | halt => rfl

private theorem affineSuffixOrKernel_op_preservesMaskTail
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineSuffixOrKernelLabel label) :
    preservesMaskTail (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont => cases register <;> trivial
  | restoreInc register cont => cases register <;> trivial
  | resume cont =>
      cases cont <;> simp_all [isAffineSuffixOrKernelLabel,
        isAffineSuffixOrCont, preservesMaskTail,
        sequentialExactlyOneRevProgram]
  | suffixOr phase => cases phase <;> trivial
  | _ =>
      simp_all [isAffineSuffixOrKernelLabel, isAffineSuffixOrCont,
        preservesMaskTail, sequentialExactlyOneRevProgram]

private theorem affineStack_op_mask
    (label : SequentialExactlyOneLabel) (hlabel : label ≠ .halt) :
    affineStackRevProgram.op (.mask label) =
      liftMaskOp (sequentialExactlyOneRevProgram.op label) := by
  cases label <;> simp_all [affineStackRevProgram]

private theorem liftMask_step (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineSuffixOrKernelCfg c)
    (hexit : c.label ≠ some .halt) :
    step affineStackRevProgram (liftMaskCfg tail c) =
      Option.map (liftMaskCfg tail)
        (step sequentialExactlyOneRevProgram c) := by
  unfold step
  rw [show (liftMaskCfg tail c).label = c.label.map .mask by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelKernel : isAffineSuffixOrKernelLabel label := by
        simpa [isAffineSuffixOrKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineStack_op_mask label hlabelExit]
      exact congrArg some (liftMask_stepOp tail
        (sequentialExactlyOneRevProgram.op label) c
        (affineSuffixOrKernel_op_preservesMaskTail label hlabelKernel))

private def staysInAffineSuffixOrKernel :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .pushOutput _ next | .pushWork₁ _ next | .pushWork₂ _ next
  | .inc₁ next | .inc₂ next | .inc₃ next | .jump next =>
      isAffineSuffixOrKernelLabel next
  | .moveInputWork₁ nextEmpty nextMoved
  | .moveWork₁Input nextEmpty nextMoved
  | .moveInputWork₂ nextEmpty nextMoved
  | .moveWork₂Input nextEmpty nextMoved
  | .moveWork₁Work₂ nextEmpty nextMoved
  | .moveWork₂Work₁ nextEmpty nextMoved
  | .copyInputWorks nextEmpty nextMoved
  | .popInput nextEmpty nextMoved
  | .popWork₁ nextEmpty nextMoved
  | .popWork₂ nextEmpty nextMoved =>
      isAffineSuffixOrKernelLabel nextEmpty ∧
        ∀ symbol, isAffineSuffixOrKernelLabel (nextMoved symbol)
  | .dec₁ nextZero nextSucc | .dec₂ nextZero nextSucc
  | .dec₃ nextZero nextSucc =>
      isAffineSuffixOrKernelLabel nextZero ∧
        isAffineSuffixOrKernelLabel nextSucc
  | .halt => True

private theorem stepOp_staysInAffineSuffixOrKernel
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hop : staysInAffineSuffixOrKernel op) :
    isAffineSuffixOrKernelCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | pushWork₁ => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | pushWork₂ => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | moveInputWork₁ => cases input <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | moveWork₁Input => cases work₁ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | moveInputWork₂ => cases input <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | moveWork₂Input => cases work₂ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | moveWork₁Work₂ => cases work₁ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | moveWork₂Work₁ => cases work₂ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | copyInputWorks => cases input <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | popInput => cases input <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | popWork₁ => cases work₁ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | popWork₂ => cases work₂ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | inc₁ => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | inc₂ => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | inc₃ => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | dec₁ => cases counter₁ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | dec₂ => cases counter₂ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | dec₃ => cases counter₃ <;> simp_all [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp]
  | jump => simpa [staysInAffineSuffixOrKernel,
      isAffineSuffixOrKernelCfg, stepOp] using hop
  | halt => trivial

private theorem affineSuffixOrKernel_op_stays
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineSuffixOrKernelLabel label) (hexit : label ≠ .halt) :
    staysInAffineSuffixOrKernel
      (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont => cases register <;> exact ⟨hkernel, hkernel⟩
  | save register cont => exact hkernel
  | pushArg register cont => exact hkernel
  | pushEnd register cont => exact hkernel
  | restore register cont => exact ⟨hkernel, fun _ => hkernel⟩
  | restoreInc register cont => cases register <;> exact hkernel
  | resume cont =>
      cases cont <;> simp_all [isAffineSuffixOrKernelLabel,
        isAffineSuffixOrCont, staysInAffineSuffixOrKernel,
        sequentialExactlyOneRevProgram]
  | suffixOr phase =>
      cases phase <;> simp [staysInAffineSuffixOrKernel,
        sequentialExactlyOneRevProgram, isAffineSuffixOrKernelLabel,
        isAffineSuffixOrCont]
  | clear₁ => trivial
  | clear₂ => trivial
  | clear₃ => trivial
  | halt => simp at hexit
  | invalid => trivial
  | _ => simp [isAffineSuffixOrKernelLabel] at hkernel

private theorem affineSuffixOrKernel_step_closed
    (c c' : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineSuffixOrKernelCfg c)
    (hexit : c.label ≠ some .halt)
    (hstep : step sequentialExactlyOneRevProgram c = some c') :
    isAffineSuffixOrKernelCfg c' := by
  unfold step at hstep
  cases hlabel : c.label with
  | none => simp [hlabel] at hstep
  | some label =>
      have hlabelKernel : isAffineSuffixOrKernelLabel label := by
        simpa [isAffineSuffixOrKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      rw [hlabel] at hstep
      injection hstep with hc'
      subst c'
      exact stepOp_staysInAffineSuffixOrKernel
        (sequentialExactlyOneRevProgram.op label) c
        (affineSuffixOrKernel_op_stays label hlabelKernel hlabelExit)

private theorem stack_iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem suffixOr_halt_no_return
    (c target : BuilderCfg sequentialExactlyOneRevProgram)
    (hc : c.label = some .halt) (htarget : target.label = some .halt) :
    ∀ n : Nat,
      (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
        (step sequentialExactlyOneRevProgram c) ≠ some target := by
  intro n
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at hc
  subst label
  let halted : BuilderCfg sequentialExactlyOneRevProgram := {
    label := none
    buffer₁ := none
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := work₁
    work₂ := work₂
    counter₁ := counter₁
    counter₂ := counter₂
    counter₃ := counter₃ }
  have hstep : step sequentialExactlyOneRevProgram
      { label := some SequentialExactlyOneLabel.halt
        buffer₁ := buffer₁, buffer₂ := buffer₂, test := test
        input := input, output := output, work₁ := work₁, work₂ := work₂
        counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := rfl
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, htarget] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
          (step sequentialExactlyOneRevProgram halted) ≠ some target
      have hnone : step sequentialExactlyOneRevProgram halted = none := rfl
      rw [hnone, stack_iterate_bind_none]
      simp

private theorem liftMask_iterations (tail : List UnaryFrameSym)
    {a b : BuilderCfg sequentialExactlyOneRevProgram}
    (ha : isAffineSuffixOrKernelCfg a) (hb : b.label = some .halt) :
    ∀ n : Nat,
      (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
          (some a) = some b →
        (flip Option.bind (step affineStackRevProgram))^[n]
          (some (liftMaskCfg tail a)) = some (liftMaskCfg tail b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
          (step sequentialExactlyOneRevProgram a) = some b at h
      change
        (flip Option.bind (step affineStackRevProgram))^[n]
          (step affineStackRevProgram (liftMaskCfg tail a)) =
            some (liftMaskCfg tail b)
      have haexit : a.label ≠ some .halt := by
        intro haHalt
        exact suffixOr_halt_no_return a b haHalt hb n h
      cases hstep : step sequentialExactlyOneRevProgram a with
      | none =>
          rw [hstep, stack_iterate_bind_none] at h
          contradiction
      | some c =>
          have hc := affineSuffixOrKernel_step_closed a c ha haexit hstep
          have hsim := liftMask_step tail a ha haexit
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih hc h

/-- Mask-kernel entry after the runtime triple has been loaded and the false
seed byte has been prepended. -/
def affineStackMaskReadyCfg (start base count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineStackRevProgram :=
  affineStackCfg (.mask (.suffixOr .next)) none none false tail
    (.constFalseMark :: output) (List.replicate count .tick) []
    (List.replicate start ()) [] (List.replicate (base + count) ())

/-- Clean redirect point after the suffix-OR mask kernel. -/
def affineStackMaskCoreExitCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineStackRevProgram :=
  affineStackCfg (.mask .halt) none none false tail output
    [] [] [] [] []

/-- The established suffix-OR core transports to the stack controller while
leaving every framed cell untouched. -/
def affineStackMaskCore_run (start base count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackMaskReadyCfg start base count tail output)
      (some (affineStackMaskCoreExitCfg tail
        ((affineSuffixOrGateStream start base count).reverse ++ output)))
      (affineSuffixOrRevCoreSteps start base count) := by
  let source := affineSuffixOrBodyCfg start base count output
  let target := sequentialExactlyOneCfg .halt none none false []
    ((affineSuffixOrGateStream start base count).reverse ++ output)
    [] [] [] [] []
  have hrun := affineSuffixOrRev_runToHaltLabel start base count output
  have hsource : isAffineSuffixOrKernelCfg source := by
    simp [source, affineSuffixOrBodyCfg, sequentialExactlyOneCfg,
      isAffineSuffixOrKernelCfg, isAffineSuffixOrKernelLabel]
  have htarget : target.label = some .halt := rfl
  refine ⟨⟨hrun.steps, ?_⟩, hrun.steps_le_m⟩
  have hlift := liftMask_iterations tail hsource htarget
    hrun.steps hrun.evals_in_steps
  have hsourceLift : liftMaskCfg tail source =
      affineStackMaskReadyCfg start base count tail output := by
    simp only [source, liftMaskCfg, affineStackMaskReadyCfg,
      affineSuffixOrBodyCfg, affineStackCfg, sequentialExactlyOneCfg,
      List.map_replicate, List.map_nil, List.nil_append, Option.map_some,
      Option.map_none]
    rfl
  have htargetLift : liftMaskCfg tail target =
      affineStackMaskCoreExitCfg tail
        ((affineSuffixOrGateStream start base count).reverse ++ output) := rfl
  rw [← hsourceLift, ← htargetLift]
  exact hlift

/-- Exact mask-prelude cost: scan three fields, clear the last input buffer,
move the preserved count from work₂ to work₁, and emit the false seed. -/
def affineStackMaskLoadSteps (start base count : Nat) : Nat :=
  2 * start + 2 * base + 5 * count + 6

private theorem stack_replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem stackLoadFirst_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
      (some (affineStackCfg (.load .load₁) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineStackCfg (.load .load₂) (some .separator) buffer₂ test
        tail output work₁ (List.replicate value .tick ++ work₂)
        first second third) := by
  induction value generalizing buffer₁ test work₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
          (some (affineStackCfg (.load .load₁) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁
            (.tick :: work₂) first second third)) = _
      simpa only [List.replicate_succ,
        stack_replicate_append_cons, List.cons_append] using
        ih (some .tick) test (.tick :: work₂)

private theorem stackLoadSecond_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
      (some (affineStackCfg (.load .load₂) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineStackCfg (.load .load₃) (some .separator) buffer₂ test
        tail output work₁ work₂
        (List.replicate value () ++ first) second third) := by
  induction value generalizing buffer₁ test first with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
          (some (affineStackCfg (.load .load₂) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            (() :: first) second third)) = _
      simpa only [List.replicate_succ,
        stack_replicate_append_cons, List.cons_append] using
        ih (some .tick) test (() :: first)

private theorem stackLoadThird_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
      (some (affineStackCfg (.load .load₃) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineStackCfg (.load .clearBuffer) (some .separator) buffer₂ test
        tail output work₁ work₂ first second
        (List.replicate value () ++ third)) := by
  induction value generalizing buffer₁ test third with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineStackRevProgram))^[2 * value + 1]
          (some (affineStackCfg (.load .load₃) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first second (() :: third))) = _
      simpa only [List.replicate_succ,
        stack_replicate_append_cons, List.cons_append] using
        ih (some .tick) test (() :: third)

private theorem stackMoveCount_eval (count : Nat)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ : List UnaryFrameSym) (first third : List Unit) :
    (flip Option.bind (step affineStackRevProgram))^[count + 1]
      (some (affineStackCfg (.load .moveCount) none buffer₂ test tail output
        work₁ (List.replicate count .tick) first [] third)) =
      some (affineStackCfg (.load .seedMask) none none test tail output
        (List.replicate count .tick ++ work₁) [] first [] third) := by
  induction count generalizing buffer₂ work₁ with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineStackRevProgram))^[count + 1]
          (some (affineStackCfg (.load .moveCount) none (some .tick) test
            tail output (.tick :: work₁) (List.replicate count .tick)
            first [] third)) = _
      simpa only [List.replicate_succ,
        stack_replicate_append_cons, List.cons_append] using
        ih (some .tick) (.tick :: work₁)

/-- Load one mask frame and enter the linked suffix-OR kernel, preserving the
entire encoded cell family. -/
def affineStackMask_load (start base count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg
        (encodeUnaryFrame [count, start, base + count] ++ tail) output)
      (some (affineStackMaskReadyCfg start base count tail output))
      (affineStackMaskLoadSteps start base count) := by
  let afterFirst := affineStackCfg (.load .load₂) (some .separator) none
    false
    (encodeUnaryFrameBlock start ++
      encodeUnaryFrameBlock (base + count) ++ tail)
    output [] (List.replicate count .tick) [] [] []
  have hfirst : EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg
        (encodeUnaryFrame [count, start, base + count] ++ tail) output)
      (some afterFirst) (2 * count + 1) := by
    refine ⟨⟨2 * count + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, affineStackLoopCfg, encodeUnaryFrame,
      List.append_assoc] using
      stackLoadFirst_eval count none none false
        (encodeUnaryFrameBlock start ++
          encodeUnaryFrameBlock (base + count) ++ tail)
        output [] [] [] [] []
  let afterSecond := affineStackCfg (.load .load₃) (some .separator) none
    false (encodeUnaryFrameBlock (base + count) ++ tail) output []
    (List.replicate count .tick) (List.replicate start ()) [] []
  have hsecond : EvalsToInTime (step affineStackRevProgram)
      afterFirst (some afterSecond) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, afterSecond, List.append_assoc] using
      stackLoadSecond_eval start (some .separator) none false
        (encodeUnaryFrameBlock (base + count) ++ tail) output []
        (List.replicate count .tick) [] [] []
  let beforeClear := affineStackCfg (.load .clearBuffer) (some .separator)
    none false tail output [] (List.replicate count .tick)
    (List.replicate start ()) [] (List.replicate (base + count) ())
  have hthird : EvalsToInTime (step affineStackRevProgram)
      afterSecond (some beforeClear) (2 * (base + count) + 1) := by
    refine ⟨⟨2 * (base + count) + 1, ?_⟩, le_rfl⟩
    simpa [afterSecond, beforeClear] using
      stackLoadThird_eval (base + count) (some .separator) none false tail
        output [] (List.replicate count .tick)
        (List.replicate start ()) [] []
  let beforeMove := affineStackCfg (.load .moveCount) none none false tail
    output [] (List.replicate count .tick) (List.replicate start ()) []
    (List.replicate (base + count) ())
  have hclear : EvalsToInTime (step affineStackRevProgram)
      beforeClear (some beforeMove) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeSeed := affineStackCfg (.load .seedMask) none none false tail
    output (List.replicate count .tick) [] (List.replicate start ()) []
    (List.replicate (base + count) ())
  have hmove : EvalsToInTime (step affineStackRevProgram)
      beforeMove (some beforeSeed) (count + 1) := by
    refine ⟨⟨count + 1, ?_⟩, le_rfl⟩
    simpa [beforeMove, beforeSeed] using
      stackMoveCount_eval count none false tail output []
        (List.replicate start ()) (List.replicate (base + count) ())
  have hseed : EvalsToInTime (step affineStackRevProgram)
      beforeSeed
      (some (affineStackMaskReadyCfg start base count tail output)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineStackRevProgram)
    (2 * count + 1) (2 * start + 1) _ afterFirst _ hfirst hsecond
  let t₂ := EvalsToInTime.trans (step affineStackRevProgram)
    _ (2 * (base + count) + 1) _ afterSecond _ t₁ hthird
  let t₃ := EvalsToInTime.trans (step affineStackRevProgram)
    _ 1 _ beforeClear _ t₂ hclear
  let t₄ := EvalsToInTime.trans (step affineStackRevProgram)
    _ (count + 1) _ beforeMove _ t₃ hmove
  let full := EvalsToInTime.trans (step affineStackRevProgram)
    _ 1 _ beforeSeed _ t₄ hseed
  convert full using 1
  simp [affineStackMaskLoadSteps]
  omega

/-- Exact running time of one mask-plus-cells stack frame, returning to the
clean outer loop header instead of halting. -/
def affineStackFrameRevSteps (frame : AffineStackFrame) : Nat :=
  affineStackMaskLoadSteps frame.start frame.base frame.count +
    affineSuffixOrRevCoreSteps frame.start frame.base frame.count + 1 +
    affineCellFamilyUntilEndSteps frame.cells + 1

/-- Execute one complete stack-validity block and return to the clean outer
loop header with all later stack frames untouched. -/
def affineStack_runOne (frame : AffineStackFrame)
    (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg (encodeAffineStackFrame frame ++ tail) output)
      (some (affineStackLoopCfg tail
        ((affineStackGateStream frame).reverse ++ output)))
      (affineStackFrameRevSteps frame) := by
  let cellTail :=
    encodeAffineCellFamily frame.cells ++ .frameEnd :: tail
  have hload := affineStackMask_load frame.start frame.base frame.count
    cellTail output
  have hmask := affineStackMaskCore_run frame.start frame.base frame.count
    cellTail output
  let maskOutput :=
    (affineSuffixOrGateStream frame.start frame.base frame.count).reverse ++
      output
  let cellsEntry := liftCellFamilyCfg
    (affineCellFamilyLoopCfg cellTail maskOutput)
  have hjump : EvalsToInTime (step affineStackRevProgram)
      (affineStackMaskCoreExitCfg cellTail maskOutput)
      (some cellsEntry) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcells := affineStackCellFamily_runToFinish frame.cells tail maskOutput
  let cellOutput :=
    (affineCellFamilyGateStream frame.cells).reverse ++ maskOutput
  have hcontinue : EvalsToInTime (step affineStackRevProgram)
      (affineStackCellFamilyFinishCfg tail cellOutput)
      (some (affineStackLoopCfg tail cellOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineStackRevProgram)
    (affineStackMaskLoadSteps frame.start frame.base frame.count)
    (affineSuffixOrRevCoreSteps frame.start frame.base frame.count)
    _ (affineStackMaskReadyCfg frame.start frame.base frame.count
      cellTail output) _ hload hmask
  let t₂ := EvalsToInTime.trans (step affineStackRevProgram)
    _ 1 _ (affineStackMaskCoreExitCfg cellTail maskOutput) _ t₁ hjump
  let t₃ := EvalsToInTime.trans (step affineStackRevProgram)
    _ (affineCellFamilyUntilEndSteps frame.cells) _ cellsEntry _ t₂ hcells
  let full := EvalsToInTime.trans (step affineStackRevProgram)
    _ 1 _ (affineStackCellFamilyFinishCfg tail cellOutput) _ t₃ hcontinue
  convert full using 1
  · simp [encodeAffineStackFrame, cellTail, List.append_assoc]
  · simp [affineStackGateStream, maskOutput,
      cellOutput, List.reverse_append, List.append_assoc]
  · simp [affineStackFrameRevSteps]
    omega

/-- Runtime input for any finite sequence of complete stack frames. -/
def encodeAffineStackFamily : List AffineStackFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineStackFrame frame ++ encodeAffineStackFamily rest

/-- Exact forward byte stream of any finite stack family. -/
def affineStackFamilyGateStream : List AffineStackFrame → List CircuitSym
  | [] => []
  | frame :: rest =>
      affineStackGateStream frame ++ affineStackFamilyGateStream rest

/-- The recursive stack-family stream is ordinary `flatMap` over frames. -/
theorem affineStackFamilyGateStream_eq_flatMap
    (frames : List AffineStackFrame) :
    affineStackFamilyGateStream frames =
      frames.flatMap affineStackGateStream := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineStackFamilyGateStream, ih]

/-- Exact outer-family cost, including the final empty-input check and halt. -/
def affineStackFamilyRevSteps : List AffineStackFrame → Nat
  | [] => 2
  | frame :: rest =>
      affineStackFrameRevSteps frame + affineStackFamilyRevSteps rest

/-- Exact outer-family cost through an explicit `frameEnd` terminator, stopping
at the clean redirectable finish label instead of executing its halt. -/
def affineStackFamilyUntilTerminatorSteps : List AffineStackFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineStackFrameRevSteps frame +
        affineStackFamilyUntilTerminatorSteps rest

/-- Redirectable endpoint after consuming the explicit outer-family
terminator.  The terminator remains in `buffer₁` so a parent controller can
clear it in one checked bridge step. -/
def affineStackFamilyTerminatorCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineStackRevProgram :=
  affineStackCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

/-- Execute an arbitrary stack family through a delimiter-bearing outer
terminator while preserving the input owned by a following controller. -/
def affineStackFamily_runToTerminator (frames : List AffineStackFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg
        (encodeAffineStackFamily frames ++ .frameEnd :: tail) output)
      (some (affineStackFamilyTerminatorCfg tail
        ((affineStackFamilyGateStream frames).reverse ++ output)))
      (affineStackFamilyUntilTerminatorSteps frames) := by
  induction frames generalizing output with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput := (affineStackGateStream frame).reverse ++ output
      have hfirst := affineStack_runOne frame
        (encodeAffineStackFamily rest ++ .frameEnd :: tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineStackRevProgram)
        (affineStackFrameRevSteps frame)
        (affineStackFamilyUntilTerminatorSteps rest)
        _ (affineStackLoopCfg
          (encodeAffineStackFamily rest ++ .frameEnd :: tail) frameOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineStackFamily, List.append_assoc]
      · simp [affineStackFamilyGateStream, frameOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineStackFamilyUntilTerminatorSteps]
        omega

/-- Empty outer family terminates successfully without changing output. -/
def affineStackFamily_empty_run (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg [] output)
      (some (haltCfg affineStackRevProgram output)) 2 :=
  ⟨⟨2, rfl⟩, le_rfl⟩

/-- Execute an arbitrary runtime-length family of complete stack blocks with
one fixed finite controller. -/
def affineStackFamily_run (frames : List AffineStackFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg (encodeAffineStackFamily frames) output)
      (some (haltCfg affineStackRevProgram
        ((affineStackFamilyGateStream frames).reverse ++ output)))
      (affineStackFamilyRevSteps frames) := by
  induction frames generalizing output with
  | nil =>
      simpa [encodeAffineStackFamily, affineStackFamilyGateStream,
        affineStackFamilyRevSteps] using affineStackFamily_empty_run output
  | cons frame rest ih =>
      let frameOutput := (affineStackGateStream frame).reverse ++ output
      have hfirst := affineStack_runOne frame
        (encodeAffineStackFamily rest) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineStackRevProgram)
        (affineStackFrameRevSteps frame) (affineStackFamilyRevSteps rest)
        _ (affineStackLoopCfg (encodeAffineStackFamily rest) frameOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineStackFamily]
      · simp [affineStackFamilyGateStream, frameOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineStackFamilyRevSteps]
        omega

/-- Exact standalone cost of one complete stack block. -/
def affineStackRevSteps (frame : AffineStackFrame) : Nat :=
  affineStackFamilyRevSteps [frame]

/-- Execute one complete stack-validity block without halting between its
suffix-OR mask and its runtime-length cell family. -/
def affineStack_run (frame : AffineStackFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineStackRevProgram)
      (affineStackLoopCfg (encodeAffineStackFrame frame) output)
      (some (haltCfg affineStackRevProgram
        ((affineStackGateStream frame).reverse ++ output)))
      (affineStackRevSteps frame) := by
  simpa [affineStackRevSteps, encodeAffineStackFamily,
    affineStackFamilyGateStream] using affineStackFamily_run [frame] output

/-- Exact length of the explicit stack frame. -/
@[simp] theorem encodeAffineStackFrame_length (frame : AffineStackFrame) :
    (encodeAffineStackFrame frame).length =
      frame.start + frame.base + 2 * frame.count + 4 +
        (encodeAffineCellFamily frame.cells).length := by
  simp [encodeAffineStackFrame, encodeUnaryFrame_length]
  omega

/-- One complete stack frame returns to the outer loop in time quadratic in
its explicit encoding. -/
theorem affineStackFrameRev_steps_le (frame : AffineStackFrame) :
    affineStackFrameRevSteps frame ≤
      400 * (encodeAffineStackFrame frame).length ^ 2 := by
  let maskLen := frame.start + frame.base + 2 * frame.count + 3
  let cellLen := (encodeAffineCellFamily frame.cells).length
  have hcoreLeFull :
      affineSuffixOrRevCoreSteps frame.start frame.base frame.count ≤
        affineSuffixOrRevSteps frame.start frame.base frame.count := by
    simp [affineSuffixOrRevCoreSteps, affineSuffixOrRevSteps]
  have hmask := le_trans hcoreLeFull
    (affineSuffixOrRev_steps_le frame.start frame.base frame.count)
  have harg : frame.start + frame.base + frame.count + 1 ≤ maskLen := by
    simp [maskLen]
    omega
  have hargMul := Nat.mul_le_mul harg harg
  have hargSquare :
      (frame.start + frame.base + frame.count + 1) ^ 2 ≤ maskLen ^ 2 := by
    simpa [pow_two] using hargMul
  have hmask' :
      affineSuffixOrRevCoreSteps frame.start frame.base frame.count ≤
        25 * maskLen ^ 2 :=
    le_trans hmask (Nat.mul_le_mul_left 25 hargSquare)
  have hload :
      affineStackMaskLoadSteps frame.start frame.base frame.count ≤
        maskLen ^ 2 := by
    simp [affineStackMaskLoadSteps, maskLen]
    nlinarith
  have hcells := affineCellFamilyUntilEnd_steps_le frame.cells
  change affineCellFamilyUntilEndSteps frame.cells ≤
    250 * cellLen ^ 2 + 1 at hcells
  have hsquare : maskLen ^ 2 + cellLen ^ 2 ≤
      (maskLen + cellLen) ^ 2 := by
    calc
      maskLen ^ 2 + cellLen ^ 2 ≤
          maskLen ^ 2 + cellLen ^ 2 + 2 * maskLen * cellLen := by omega
      _ = (maskLen + cellLen) ^ 2 := by ring
  have hcombine :
      26 * maskLen ^ 2 + 250 * cellLen ^ 2 ≤
        300 * (maskLen + cellLen) ^ 2 := by
    calc
      26 * maskLen ^ 2 + 250 * cellLen ^ 2 ≤
          250 * maskLen ^ 2 + 250 * cellLen ^ 2 := by omega
      _ = 250 * (maskLen ^ 2 + cellLen ^ 2) := by ring
      _ ≤ 250 * (maskLen + cellLen) ^ 2 :=
        Nat.mul_le_mul_left 250 hsquare
      _ ≤ 300 * (maskLen + cellLen) ^ 2 := by omega
  have hmain : affineStackFrameRevSteps frame ≤
      300 * (maskLen + cellLen) ^ 2 + 3 := by
    simp only [affineStackFrameRevSteps]
    calc
      affineStackMaskLoadSteps frame.start frame.base frame.count +
            affineSuffixOrRevCoreSteps frame.start frame.base frame.count + 1 +
            affineCellFamilyUntilEndSteps frame.cells + 1 ≤
          maskLen ^ 2 + 25 * maskLen ^ 2 + 1 +
            (250 * cellLen ^ 2 + 1) + 1 := by omega
      _ = 26 * maskLen ^ 2 + 250 * cellLen ^ 2 + 3 := by ring
      _ ≤ 300 * (maskLen + cellLen) ^ 2 + 3 :=
        Nat.add_le_add_right hcombine 3
  rw [encodeAffineStackFrame_length]
  change affineStackFrameRevSteps frame ≤
    400 * (maskLen + 1 + cellLen) ^ 2
  calc
    affineStackFrameRevSteps frame ≤
        300 * (maskLen + cellLen) ^ 2 + 3 := hmain
    _ ≤ 400 * (maskLen + 1 + cellLen) ^ 2 := by nlinarith

/-- The entire runtime-length stack family has one uniform quadratic bound. -/
theorem affineStackFamilyRev_steps_le (frames : List AffineStackFrame) :
    affineStackFamilyRevSteps frames ≤
      400 * (encodeAffineStackFamily frames).length ^ 2 + 2 := by
  induction frames with
  | nil => simp [affineStackFamilyRevSteps, encodeAffineStackFamily]
  | cons frame rest ih =>
      have hframe := affineStackFrameRev_steps_le frame
      simp only [affineStackFamilyRevSteps, encodeAffineStackFamily,
        List.length_append]
      have hsquare :
          (encodeAffineStackFrame frame).length ^ 2 +
              (encodeAffineStackFamily rest).length ^ 2 ≤
            ((encodeAffineStackFrame frame).length +
              (encodeAffineStackFamily rest).length) ^ 2 := by
        calc
          (encodeAffineStackFrame frame).length ^ 2 +
                (encodeAffineStackFamily rest).length ^ 2 ≤
              (encodeAffineStackFrame frame).length ^ 2 +
                (encodeAffineStackFamily rest).length ^ 2 +
                2 * (encodeAffineStackFrame frame).length *
                  (encodeAffineStackFamily rest).length := by omega
          _ = ((encodeAffineStackFrame frame).length +
              (encodeAffineStackFamily rest).length) ^ 2 := by ring
      calc
        affineStackFrameRevSteps frame + affineStackFamilyRevSteps rest ≤
            400 * (encodeAffineStackFrame frame).length ^ 2 +
              (400 * (encodeAffineStackFamily rest).length ^ 2 + 2) :=
          Nat.add_le_add hframe ih
        _ = 400 * ((encodeAffineStackFrame frame).length ^ 2 +
              (encodeAffineStackFamily rest).length ^ 2) + 2 := by ring
        _ ≤ 400 * ((encodeAffineStackFrame frame).length +
              (encodeAffineStackFamily rest).length) ^ 2 + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 400 hsquare) 2

/-- Stopping at the explicit outer terminator costs no more than the existing
standalone family run. -/
theorem affineStackFamilyUntilTerminatorSteps_le
    (frames : List AffineStackFrame) :
    affineStackFamilyUntilTerminatorSteps frames ≤
      400 * (encodeAffineStackFamily frames).length ^ 2 + 2 := by
  have hle : affineStackFamilyUntilTerminatorSteps frames ≤
      affineStackFamilyRevSteps frames := by
    induction frames with
    | nil => simp [affineStackFamilyUntilTerminatorSteps,
        affineStackFamilyRevSteps]
    | cons frame rest ih =>
        simp only [affineStackFamilyUntilTerminatorSteps,
          affineStackFamilyRevSteps]
        omega
  exact hle.trans (affineStackFamilyRev_steps_le frames)

/-- The standalone one-stack interface is a specialization of the family
controller and inherits its quadratic bound. -/
theorem affineStackRev_steps_le (frame : AffineStackFrame) :
    affineStackRevSteps frame ≤
      400 * (encodeAffineStackFrame frame).length ^ 2 + 2 := by
  simpa [affineStackRevSteps, encodeAffineStackFamily] using
    affineStackFamilyRev_steps_le [frame]

end CLRS.Chapter34.Turing.PolyBuilder
