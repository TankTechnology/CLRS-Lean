import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Not
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Fixed controller for a framed family of affine exactly-one blocks

Each runtime frame stores `(start, start + 2, rowBase, count)` in delimiter-
bearing unary.  The first three fields restore the affine kernel registers;
the last field both extends `rowBase` to `rowBase + count` and records `count`
on `work₁`.  Empty input terminates successfully, while the kernel's clean
halt label is redirected to the next frame.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Fixed finite-control phases of the four-field frame prelude. -/
inductive AffineExactlyOneFamilyLoadLabel
  | load₁ | inc₁
  | load₂ | inc₂
  | load₃ | inc₃
  | load₄ | inc₄ | pushCount
  | clearBuffer | transferCount | pushFalse₁ | pushFalse₂
deriving DecidableEq, Fintype

/-- Grouped finite control keeps the already large exactly-one kernel beneath one
constructor and avoids derived-`Fintype` nested-sum depth failures. -/
inductive AffineExactlyOneFamilyLabel
  | load (phase : AffineExactlyOneFamilyLoadLabel)
  | kernel (label : SequentialExactlyOneLabel)
  | andClear | finish | invalid
deriving DecidableEq, Fintype

/-- Relabel one established exactly-one instruction onto the framed input
alphabet.  Unit scratch symbols become frame `tick`s.  The kernel never reads
the persistent input while executing an accepted affine run. -/
private def liftExactlyOneKernelOp :
    Op Unit CircuitSym SequentialExactlyOneLabel →
      Op UnaryFrameSym CircuitSym AffineExactlyOneFamilyLabel
  | .pushOutput symbol next => .pushOutput symbol (.kernel next)
  | .pushWork₁ _ next => .pushWork₁ .tick (.kernel next)
  | .pushWork₂ _ next => .pushWork₂ .tick (.kernel next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.kernel nextEmpty) (fun _ => .kernel (nextMoved ()))
  | .copyInputWorks nextEmpty nextCopied =>
      .copyInputWorks (.kernel nextEmpty) (fun _ => .kernel (nextCopied ()))
  | .popInput nextEmpty nextSome =>
      .popInput (.kernel nextEmpty) (fun _ => .kernel (nextSome ()))
  | .popWork₁ nextEmpty nextSome =>
      .popWork₁ (.kernel nextEmpty) (fun _ => .kernel (nextSome ()))
  | .popWork₂ nextEmpty nextSome =>
      .popWork₂ (.kernel nextEmpty) (fun _ => .kernel (nextSome ()))
  | .inc₁ next => .inc₁ (.kernel next)
  | .inc₂ next => .inc₂ (.kernel next)
  | .inc₃ next => .inc₃ (.kernel next)
  | .dec₁ nextZero nextSucc => .dec₁ (.kernel nextZero) (.kernel nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.kernel nextZero) (.kernel nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.kernel nextZero) (.kernel nextSucc)
  | .jump next => .jump (.kernel next)
  | .halt => .halt

/-- One fixed program for every finite framed family.  The family length and
all gate/source indices are runtime stack data, never control labels. -/
def affineExactlyOneFamilyRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineExactlyOneFamilyLabel
  main := .load .load₁
  op
    | .load .load₁ => .popInput .finish fun
        | .tick => .load .inc₁
        | .separator => .load .load₂
        | .frameEnd => .finish
    | .load .inc₁ => .inc₁ (.load .load₁)
    | .load .load₂ => .popInput .invalid fun
        | .tick => .load .inc₂
        | .separator => .load .load₃
        | .frameEnd => .invalid
    | .load .inc₂ => .inc₂ (.load .load₂)
    | .load .load₃ => .popInput .invalid fun
        | .tick => .load .inc₃
        | .separator => .load .load₄
        | .frameEnd => .invalid
    | .load .inc₃ => .inc₃ (.load .load₃)
    | .load .load₄ => .popInput .invalid fun
        | .tick => .load .inc₄
        | .separator => .load .clearBuffer
        | .frameEnd => .invalid
    | .load .inc₄ => .inc₃ (.load .pushCount)
    | .load .pushCount => .pushWork₂ .tick (.load .load₄)
    | .load .clearBuffer =>
        .popWork₁ (.load .transferCount) (fun _ => .invalid)
    | .load .transferCount =>
        .moveWork₂Work₁ (.load .pushFalse₁)
          (fun _ => .load .transferCount)
    | .load .pushFalse₁ =>
        .pushOutput .constFalseMark (.load .pushFalse₂)
    | .load .pushFalse₂ =>
        .pushOutput .constFalseMark (.kernel .nextFirst)
    | .kernel (.conjunction .done) => .jump .andClear
    | .kernel .halt => .jump (.load .load₁)
    | .kernel label => liftExactlyOneKernelOp (sequentialExactlyOneRevProgram.op label)
    | .andClear => .dec₁ (.load .load₁) .andClear
    | .finish => .halt
    | .invalid => .halt

/-- Embed a kernel configuration while retaining an untouched framed input
tail.  Unit scratch symbols are represented by frame ticks. -/
private def liftExactlyOneKernelCfg (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram) :
    BuilderCfg affineExactlyOneFamilyRevProgram where
  label := c.label.map .kernel
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

private def isAffineExactlyOneCont : SequentialExactlyOneCont → Prop
  | .firstASeen | .firstAWire | .firstBDuplicate | .firstBNext
  | .firstCSeen | .firstCWire
  | .laterASeen | .laterAWire | .laterBDuplicate | .laterBNext
  | .laterCSeen | .laterCWire
  | .finalZeroDuplicate | .finalSomeDuplicate | .finalSeen | .finalNext => True
  | .boolEqNotLeft | .boolEqNotRight
  | .boolEqAndLeft | .boolEqAndRight
  | .boolEqAndStart | .boolEqAndNext
  | .boolEqOrStart | .boolEqOrNext => True
  | .affineNotWire => True
  | .suffixOrCarry | .suffixOrWire => True
  | .conjunctionSource | .conjunctionCarry => True
  | _ => False

private def isAffineExactlyOneKernelLabel : SequentialExactlyOneLabel → Prop
  | .encode _ cont | .save _ cont | .pushArg _ cont | .pushEnd _ cont
  | .restore _ cont | .restoreInc _ cont => isAffineExactlyOneCont cont
  | .resume cont => isAffineExactlyOneCont cont
  | .nextFirst | .nextLater | .decFirstWire | .decLaterWire
  | .pushFirstAnd | .pushLaterAnd | .incFirstDuplicate
  | .decLaterDuplicate | .clearSeen | .copyNext | .saveNext
  | .incSeenFromNext | .restoreNext | .restoreNextInc
  | .incSeen₁ | .incSeen₂ | .incNext₁ | .incNext₂ | .incNext₃
  | .finalZero | .finalSome | .incFinalZeroDuplicate
  | .decFinalSomeDuplicate | .restoreFinalZeroDuplicate
  | .restoreFinalSomeDuplicate | .pushFinalAnd
  | .boolEq _
  | .singleNot _
  | .suffixOr _
  | .conjunction _
  | .clear₁ | .clear₂ | .clear₃ | .halt | .invalid => True
  | _ => False

private def isAffineExactlyOneKernelCfg
    (c : BuilderCfg sequentialExactlyOneRevProgram) : Prop :=
  match c.label with
  | none => False
  | some label => isAffineExactlyOneKernelLabel label

private def preservesFramedInput :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .moveInputWork₁ .. | .moveWork₁Input ..
  | .moveInputWork₂ .. | .moveWork₂Input ..
  | .copyInputWorks .. | .popInput .. => False
  | _ => True

private theorem liftExactlyOneKernel_stepOp (tail : List UnaryFrameSym)
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hsafe : preservesFramedInput op) :
    stepOp (liftExactlyOneKernelOp op) (liftExactlyOneKernelCfg tail c) =
      liftExactlyOneKernelCfg tail (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => rfl
  | pushWork₁ => rfl
  | pushWork₂ => rfl
  | moveInputWork₁ => simp [preservesFramedInput] at hsafe
  | moveWork₁Input => simp [preservesFramedInput] at hsafe
  | moveInputWork₂ => simp [preservesFramedInput] at hsafe
  | moveWork₂Input => simp [preservesFramedInput] at hsafe
  | moveWork₁Work₂ => cases work₁ <;> rfl
  | moveWork₂Work₁ => cases work₂ <;> rfl
  | copyInputWorks => simp [preservesFramedInput] at hsafe
  | popInput => simp [preservesFramedInput] at hsafe
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

private theorem affineExactlyOneKernel_op_preservesFramedInput
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineExactlyOneKernelLabel label) :
    preservesFramedInput (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont =>
      cases register <;> trivial
  | restoreInc register cont =>
      cases register <;> trivial
  | resume cont =>
      cases cont <;> simp_all [isAffineExactlyOneKernelLabel, isAffineExactlyOneCont,
        preservesFramedInput, sequentialExactlyOneRevProgram]
  | boolEq phase => cases phase <;> trivial
  | singleNot phase => cases phase <;> trivial
  | suffixOr phase => cases phase <;> trivial
  | conjunction phase => cases phase <;> trivial
  | cell phase => cases phase <;> trivial
  | _ =>
      simp_all [isAffineExactlyOneKernelLabel, isAffineExactlyOneCont,
        preservesFramedInput, sequentialExactlyOneRevProgram]

private theorem affineExactlyOneFamily_op_cell
    (label : SequentialExactlyOneLabel) (hhalt : label ≠ .halt)
    (handDone : label ≠ .conjunction .done) :
    affineExactlyOneFamilyRevProgram.op (.kernel label) =
      liftExactlyOneKernelOp (sequentialExactlyOneRevProgram.op label) := by
  cases label <;> simp_all [affineExactlyOneFamilyRevProgram]

/-- Every non-input, non-exit kernel instruction is simulated exactly under
the framed-alphabet embedding. -/
private theorem liftExactlyOneKernel_step (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineExactlyOneKernelCfg c)
    (hhalt : c.label ≠ some .halt)
    (handDone : c.label ≠ some (.conjunction .done)) :
    step affineExactlyOneFamilyRevProgram (liftExactlyOneKernelCfg tail c) =
      Option.map (liftExactlyOneKernelCfg tail)
        (step sequentialExactlyOneRevProgram c) := by
  unfold step
  rw [show (liftExactlyOneKernelCfg tail c).label = c.label.map .kernel by rfl]
  cases hlabel : c.label with
  | none => simp [isAffineExactlyOneKernelCfg, hlabel] at hkernel
  | some label =>
      have hlabelKernel : isAffineExactlyOneKernelLabel label := by
        simpa [isAffineExactlyOneKernelCfg, hlabel] using hkernel
      have hlabelHalt : label ≠ .halt := by
        intro h
        apply hhalt
        simpa [hlabel] using congrArg some h
      have hlabelAndDone : label ≠ .conjunction .done := by
        intro h
        apply handDone
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneFamily_op_cell label hlabelHalt hlabelAndDone]
      exact congrArg some (liftExactlyOneKernel_stepOp tail
        (sequentialExactlyOneRevProgram.op label) c
        (affineExactlyOneKernel_op_preservesFramedInput label hlabelKernel))

private def staysInAffineExactlyOneKernel :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .pushOutput _ next | .pushWork₁ _ next | .pushWork₂ _ next
  | .inc₁ next | .inc₂ next | .inc₃ next | .jump next =>
      isAffineExactlyOneKernelLabel next
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
      isAffineExactlyOneKernelLabel nextEmpty ∧
        ∀ symbol, isAffineExactlyOneKernelLabel (nextMoved symbol)
  | .dec₁ nextZero nextSucc | .dec₂ nextZero nextSucc
  | .dec₃ nextZero nextSucc =>
      isAffineExactlyOneKernelLabel nextZero ∧
        isAffineExactlyOneKernelLabel nextSucc
  | .halt => False

private theorem stepOp_staysInAffineExactlyOneKernel
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hop : staysInAffineExactlyOneKernel op) :
    isAffineExactlyOneKernelCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | pushWork₁ => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | pushWork₂ => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | moveInputWork₁ => cases input <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | moveWork₁Input => cases work₁ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | moveInputWork₂ => cases input <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | moveWork₂Input => cases work₂ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | moveWork₁Work₂ => cases work₁ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | moveWork₂Work₁ => cases work₂ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | copyInputWorks => cases input <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | popInput => cases input <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | popWork₁ => cases work₁ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | popWork₂ => cases work₂ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | inc₁ => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | inc₂ => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | inc₃ => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | dec₁ => cases counter₁ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | dec₂ => cases counter₂ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | dec₃ => cases counter₃ <;> simp_all [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp]
  | jump => simpa [staysInAffineExactlyOneKernel,
      isAffineExactlyOneKernelCfg, stepOp] using hop
  | halt => simp [staysInAffineExactlyOneKernel] at hop

private theorem affineExactlyOneKernel_op_stays
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineExactlyOneKernelLabel label) (hexit : label ≠ .halt)
    (handDone : label ≠ .conjunction .done)
    (hinvalid : label ≠ .invalid) :
    staysInAffineExactlyOneKernel (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont =>
      cases register <;> exact ⟨hkernel, hkernel⟩
  | save register cont => exact hkernel
  | pushArg register cont => exact hkernel
  | pushEnd register cont => exact hkernel
  | restore register cont => exact ⟨hkernel, fun _ => hkernel⟩
  | restoreInc register cont => cases register <;> exact hkernel
  | resume cont =>
      cases cont <;> simp_all [isAffineExactlyOneKernelLabel, isAffineExactlyOneCont,
        staysInAffineExactlyOneKernel, sequentialExactlyOneRevProgram]
  | boolEq phase =>
      cases phase <;> simp_all [staysInAffineExactlyOneKernel,
        sequentialExactlyOneRevProgram, isAffineExactlyOneKernelLabel,
        isAffineExactlyOneCont]
  | singleNot phase =>
      cases phase <;> simp_all [staysInAffineExactlyOneKernel,
        sequentialExactlyOneRevProgram, isAffineExactlyOneKernelLabel,
        isAffineExactlyOneCont]
  | suffixOr phase =>
      cases phase <;> simp_all [staysInAffineExactlyOneKernel,
        sequentialExactlyOneRevProgram, isAffineExactlyOneKernelLabel,
        isAffineExactlyOneCont]
  | conjunction phase =>
      cases phase <;> simp_all [staysInAffineExactlyOneKernel,
        sequentialExactlyOneRevProgram, isAffineExactlyOneKernelLabel,
        isAffineExactlyOneCont]
  | cell phase =>
      cases phase <;> simp_all [staysInAffineExactlyOneKernel,
        sequentialExactlyOneRevProgram, isAffineExactlyOneKernelLabel,
        isAffineExactlyOneCont]
  | clear₁ => trivial
  | clear₂ => trivial
  | clear₃ => trivial
  | halt => simp at hexit
  | invalid => simp at hinvalid
  | _ => simp_all [isAffineExactlyOneKernelLabel,
      isAffineExactlyOneCont, staysInAffineExactlyOneKernel,
      sequentialExactlyOneRevProgram]

private theorem affineExactlyOneKernel_step_closed
    (c c' : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineExactlyOneKernelCfg c)
    (hhalt : c.label ≠ some .halt)
    (handDone : c.label ≠ some (.conjunction .done))
    (hinvalid : c.label ≠ some .invalid)
    (hstep : step sequentialExactlyOneRevProgram c = some c') :
    isAffineExactlyOneKernelCfg c' := by
  unfold step at hstep
  cases hlabel : c.label with
  | none => simp [hlabel] at hstep
  | some label =>
      have hlabelKernel : isAffineExactlyOneKernelLabel label := by
        simpa [isAffineExactlyOneKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hhalt
        simpa [hlabel] using congrArg some h
      have hlabelAndDone : label ≠ .conjunction .done := by
        intro h
        apply handDone
        simpa [hlabel] using congrArg some h
      have hlabelInvalid : label ≠ .invalid := by
        intro h
        apply hinvalid
        simpa [hlabel] using congrArg some h
      rw [hlabel] at hstep
      injection hstep with hc'
      subst c'
      exact stepOp_staysInAffineExactlyOneKernel
        (sequentialExactlyOneRevProgram.op label) c
        (affineExactlyOneKernel_op_stays label hlabelKernel hlabelExit
          hlabelAndDone hlabelInvalid)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem sequential_stop_no_return
    (exit targetLabel : SequentialExactlyOneLabel)
    (hop : sequentialExactlyOneRevProgram.op exit = .halt)
    (c target : BuilderCfg sequentialExactlyOneRevProgram)
    (hc : c.label = some exit) (htarget : target.label = some targetLabel) :
    ∀ n : Nat,
      (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
        (step sequentialExactlyOneRevProgram c) ≠ some target := by
  intro n
  let halted : BuilderCfg sequentialExactlyOneRevProgram := {
    c with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step sequentialExactlyOneRevProgram c = some halted := by
    unfold step
    rw [hc]
    simp [hop, stepOp, halted]
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
      have hnone : step sequentialExactlyOneRevProgram halted = none := by
        rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem liftExactlyOneKernel_iterations
    (exit : SequentialExactlyOneLabel)
    (hop : sequentialExactlyOneRevProgram.op exit = .halt)
    (tail : List UnaryFrameSym)
    {a b : BuilderCfg sequentialExactlyOneRevProgram}
    (ha : isAffineExactlyOneKernelCfg a) (hb : b.label = some exit) :
    ∀ n : Nat,
      (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
          (some a) = some b →
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[n]
          (some (liftExactlyOneKernelCfg tail a)) =
            some (liftExactlyOneKernelCfg tail b) := by
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
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[n]
          (step affineExactlyOneFamilyRevProgram (liftExactlyOneKernelCfg tail a)) =
            some (liftExactlyOneKernelCfg tail b)
      have haexit : a.label ≠ some .halt := by
        intro haHalt
        exact sequential_stop_no_return .halt exit rfl a b haHalt hb n h
      have haAndDone : a.label ≠ some (.conjunction .done) := by
        intro haDone
        exact sequential_stop_no_return (.conjunction .done) exit rfl
          a b haDone hb n h
      have hainvalid : a.label ≠ some .invalid := by
        intro haInvalid
        exact sequential_stop_no_return .invalid exit rfl
          a b haInvalid hb n h
      cases hstep : step sequentialExactlyOneRevProgram a with
      | none =>
          rw [hstep, iterate_bind_none] at h
          contradiction
      | some c =>
          have hc := affineExactlyOneKernel_step_closed a c ha haexit
            haAndDone hainvalid hstep
          have hsim := liftExactlyOneKernel_step tail a ha haexit haAndDone
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih hc h

/-- Fieldwise configuration surface for the framed family controller. -/
def affineExactlyOneFamilyCfg (label : AffineExactlyOneFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineExactlyOneFamilyRevProgram where
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

/-- Exactly-one kernel entry after one complete four-field frame has been
consumed and its two leading constant bytes have been emitted. -/
def affineExactlyOneFamilyReadyCfg (start rowBase count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel .nextFirst) none none false tail
    ([.constFalseMark, .constFalseMark] ++ output)
    ((List.replicate count ()).map fun _ => .tick) []
    (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())

/-- Clean redirect point reached after one exactly-one kernel has emitted its
exact affine block and cleared all scratch state. -/
def affineExactlyOneFamilyCoreExitCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel .halt) none none false tail output
    [] [] [] [] []

/-- The established affine exactly-one core transports to the framed
controller without
touching the persistent tail. -/
def affineExactlyOneFamilyCore_run (start rowBase count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyReadyCfg start rowBase count tail output)
      (some (affineExactlyOneFamilyCoreExitCfg tail
        ((affineSequentialExactlyOneGateStream
          start rowBase count).reverse ++ output)))
      (affineSequentialExactlyOneRevCoreSteps start rowBase count) := by
  let source := affineSequentialExactlyOneBodyCfg start rowBase count output
  let target := affineSequentialExactlyOneHaltLabelCfg
    ((affineSequentialExactlyOneGateStream start rowBase count).reverse ++ output)
  have hrun := affineSequentialExactlyOneRev_runToHaltLabel
    start rowBase count output
  have hsource : isAffineExactlyOneKernelCfg source := by
    simp [source, affineSequentialExactlyOneBodyCfg, sequentialExactlyOneCfg,
      isAffineExactlyOneKernelCfg, isAffineExactlyOneKernelLabel]
  have htarget : target.label = some .halt := rfl
  refine ⟨⟨hrun.steps, ?_⟩, hrun.steps_le_m⟩
  have hlift := liftExactlyOneKernel_iterations .halt rfl tail hsource htarget
    hrun.steps hrun.evals_in_steps
  have hsourceLift : liftExactlyOneKernelCfg tail source =
      affineExactlyOneFamilyReadyCfg start rowBase count tail output := by
    unfold source affineSequentialExactlyOneBodyCfg
      affineExactlyOneFamilyReadyCfg liftExactlyOneKernelCfg
      sequentialExactlyOneCfg affineExactlyOneFamilyCfg
    rfl
  have htargetLift : liftExactlyOneKernelCfg tail target =
      affineExactlyOneFamilyCoreExitCfg tail
        ((affineSequentialExactlyOneGateStream
          start rowBase count).reverse ++ output) := by
    rfl
  rw [← hsourceLift, ← htargetLift]
  exact hlift

/-- Exact cost of loading one four-field affine frame and emitting its two
leading Boolean constants. -/
def affineExactlyOneFamilyLoadSteps (start rowBase count : Nat) : Nat :=
  2 * (start + (start + 2) + rowBase) + 4 * count + 8

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem encodeUnaryFrameBlock_succ (value : Nat) :
    encodeUnaryFrameBlock (value + 1) =
      .tick :: encodeUnaryFrameBlock value := by
  simp [encodeUnaryFrameBlock, List.replicate_succ]

private theorem loadFirst_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
      (some (affineExactlyOneFamilyCfg (.load .load₁) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineExactlyOneFamilyCfg (.load .load₂) (some .separator) buffer₂ test
        tail output work₁ work₂ (List.replicate value () ++ first)
        second third) := by
  induction value generalizing buffer₁ test first with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
          (some (affineExactlyOneFamilyCfg (.load .load₁) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            (() :: first) second third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: first)

private theorem loadSecond_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
      (some (affineExactlyOneFamilyCfg (.load .load₂) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineExactlyOneFamilyCfg (.load .load₃) (some .separator) buffer₂ test
        tail output work₁ work₂ first (List.replicate value () ++ second)
        third) := by
  induction value generalizing buffer₁ test second with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
          (some (affineExactlyOneFamilyCfg (.load .load₂) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first (() :: second) third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: second)

private theorem loadThird_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
      (some (affineExactlyOneFamilyCfg (.load .load₃) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineExactlyOneFamilyCfg (.load .load₄) (some .separator)
        buffer₂ test tail output work₁ work₂ first second
        (List.replicate value () ++ third)) := by
  induction value generalizing buffer₁ test third with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[2 * value + 1]
          (some (affineExactlyOneFamilyCfg (.load .load₃) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first second (() :: third))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: third)

private theorem loadFourth_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[3 * value + 1]
      (some (affineExactlyOneFamilyCfg (.load .load₄) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineExactlyOneFamilyCfg (.load .clearBuffer) (some .separator)
        buffer₂ test tail output work₁
        (List.replicate value .tick ++ work₂) first second
        (List.replicate value () ++ third)) := by
  induction value generalizing buffer₁ test work₂ third with
  | zero => rfl
  | succ value ih =>
      have hone : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
          (affineExactlyOneFamilyCfg (.load .load₄) buffer₁ buffer₂ test
            (.tick :: (encodeUnaryFrameBlock value ++ tail)) output
            work₁ work₂ first second third)
          (some (affineExactlyOneFamilyCfg (.load .load₄) (some .tick)
            buffer₂ test (encodeUnaryFrameBlock value ++ tail) output
            work₁ (.tick :: work₂) first second (() :: third))) 3 :=
        ⟨⟨3, rfl⟩, le_rfl⟩
      have hrest := ih (some .tick) test (.tick :: work₂) (() :: third)
      have hfull :
          (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[
              (3 * value + 1) + 3]
            (some (affineExactlyOneFamilyCfg (.load .load₄) buffer₁
              buffer₂ test
              (.tick :: (encodeUnaryFrameBlock value ++ tail)) output
              work₁ work₂ first second third)) =
          some (affineExactlyOneFamilyCfg (.load .clearBuffer)
            (some .separator) buffer₂ test tail output work₁
            (List.replicate value .tick ++ .tick :: work₂) first second
            (List.replicate value () ++ () :: third)) :=
        by
          rw [Function.iterate_add_apply]
          exact hrest
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 3 by omega]
      simpa only [encodeUnaryFrameBlock_succ, List.replicate_succ,
        replicate_append_cons, List.cons_append] using hfull

private theorem transferCount_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[value + 1]
      (some (affineExactlyOneFamilyCfg (.load .transferCount)
        buffer₁ buffer₂ test tail output work₁
        (List.replicate value .tick) first second third)) =
      some (affineExactlyOneFamilyCfg (.load .pushFalse₁)
        buffer₁ none test tail output
        (List.replicate value .tick ++ work₁) [] first second third) := by
  induction value generalizing buffer₂ work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[value + 1]
          (some (affineExactlyOneFamilyCfg (.load .transferCount)
            buffer₁ (some .tick) test tail output (.tick :: work₁)
            (List.replicate value .tick) first second third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

/-- Consume one complete affine frame, preserve the remaining family, and
enter the non-halting exactly-one kernel with exact counters and count stack. -/
def affineExactlyOneFamily_load (start rowBase count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCfg (.load .load₁) none none false
        (encodeUnaryFrame [start, start + 2, rowBase, count] ++ tail)
        output [] [] [] [] [])
      (some (affineExactlyOneFamilyReadyCfg start rowBase count tail output))
      (affineExactlyOneFamilyLoadSteps start rowBase count) := by
  let afterFirst := affineExactlyOneFamilyCfg (.load .load₂) (some .separator)
    none false (encodeUnaryFrameBlock (start + 2) ++
      encodeUnaryFrameBlock rowBase ++ encodeUnaryFrameBlock count ++ tail)
    output [] [] (List.replicate start ()) [] []
  let afterSecond := affineExactlyOneFamilyCfg (.load .load₃) (some .separator)
    none false (encodeUnaryFrameBlock rowBase ++
      encodeUnaryFrameBlock count ++ tail) output [] []
    (List.replicate start ()) (List.replicate (start + 2) ()) []
  let afterThird := affineExactlyOneFamilyCfg (.load .load₄) (some .separator)
    none false (encodeUnaryFrameBlock count ++ tail) output [] []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hfirst : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCfg (.load .load₁) none none false
        (encodeUnaryFrame [start, start + 2, rowBase, count] ++ tail)
        output [] [] [] [] [])
      (some afterFirst) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, encodeUnaryFrame, List.append_assoc] using
      loadFirst_eval start none none false
        (encodeUnaryFrameBlock (start + 2) ++ encodeUnaryFrameBlock rowBase ++
          encodeUnaryFrameBlock count ++ tail) output [] [] [] [] []
  have hsecond : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      afterFirst (some afterSecond) (2 * (start + 2) + 1) := by
    refine ⟨⟨2 * (start + 2) + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, afterSecond, List.append_assoc] using
      loadSecond_eval (start + 2) (some .separator) none false
        (encodeUnaryFrameBlock rowBase ++ encodeUnaryFrameBlock count ++ tail)
        output [] [] (List.replicate start ()) [] []
  have hthird : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      afterSecond (some afterThird) (2 * rowBase + 1) := by
    refine ⟨⟨2 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [afterSecond, afterThird, List.append_assoc] using
      loadThird_eval rowBase (some .separator) none false
        (encodeUnaryFrameBlock count ++ tail) output [] []
        (List.replicate start ()) (List.replicate (start + 2) ()) []
  let beforeReady := affineExactlyOneFamilyCfg (.load .clearBuffer)
    (some .separator) none false tail output []
    (List.replicate count .tick) (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())
  have hfourth : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      afterThird (some beforeReady) (3 * count + 1) := by
    refine ⟨⟨3 * count + 1, ?_⟩, le_rfl⟩
    have h := loadFourth_eval count (some .separator) none false tail output
      [] [] (List.replicate start ()) (List.replicate (start + 2) ())
      (List.replicate rowBase ())
    have hrep : List.replicate count () ++ List.replicate rowBase () =
        List.replicate (rowBase + count) () := by
      rw [← List.replicate_add]
      congr 1
      omega
    simpa [afterThird, beforeReady, hrep] using h
  let afterClear := affineExactlyOneFamilyCfg (.load .transferCount)
    none none false tail output [] (List.replicate count .tick)
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())
  have hclear : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      beforeReady (some afterClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeConstants := affineExactlyOneFamilyCfg (.load .pushFalse₁)
    none none false tail output (List.replicate count .tick) []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())
  have htransfer : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      afterClear (some beforeConstants) (count + 1) := by
    refine ⟨⟨count + 1, ?_⟩, le_rfl⟩
    simpa [afterClear, beforeConstants] using
      transferCount_eval count none none false tail output []
        (List.replicate start ()) (List.replicate (start + 2) ())
        (List.replicate (rowBase + count) ())
  have hconstants : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      beforeConstants
      (some (affineExactlyOneFamilyReadyCfg start rowBase count tail output))
      2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    have hmap : (List.replicate count ()).map (fun _ => .tick) =
        List.replicate count UnaryFrameSym.tick := by simp
    simp [beforeConstants, affineExactlyOneFamilyReadyCfg,
      affineExactlyOneFamilyCfg, Function.iterate_succ_apply, hmap]
    rfl
  let throughTransfer := EvalsToInTime.trans
    (step affineExactlyOneFamilyRevProgram) 1 (count + 1)
    _ afterClear _ hclear htransfer
  have hfinish : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      beforeReady
      (some (affineExactlyOneFamilyReadyCfg start rowBase count tail output))
      (count + 4) := by
    let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
      ((count + 1) + 1) 2 _ beforeConstants _ throughTransfer hconstants
    convert full using 1 <;> omega
  let throughSecond := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    (2 * start + 1) (2 * (start + 2) + 1) _ afterFirst _ hfirst hsecond
  let throughThird := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    ((2 * (start + 2) + 1) + (2 * start + 1)) (2 * rowBase + 1)
    _ afterSecond _ throughSecond hthird
  let throughFourth := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    ((2 * rowBase + 1) +
      ((2 * (start + 2) + 1) + (2 * start + 1)))
    (3 * count + 1) _ afterThird _ throughThird hfourth
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    _ (count + 4)
    _ beforeReady _ throughFourth hfinish
  convert full using 1
  simp [affineExactlyOneFamilyLoadSteps]
  omega

/-- Runtime data for one affine exactly-one invocation. -/
structure AffineExactlyOneFrame where
  start : Nat
  rowBase : Nat
  count : Nat
deriving DecidableEq, Repr

/-- Delimiter-bearing input block for one affine exactly-one group. -/
def encodeAffineExactlyOneFrame (frame : AffineExactlyOneFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.start, frame.start + 2, frame.rowBase, frame.count]

/-- Exact framed size of one runtime four-field block. -/
@[simp] theorem encodeAffineExactlyOneFrame_length (frame : AffineExactlyOneFrame) :
    (encodeAffineExactlyOneFrame frame).length =
      frame.start + (frame.start + 2) + frame.rowBase + frame.count + 4 := by
  simp [encodeAffineExactlyOneFrame, encodeUnaryFrame_length]
  omega

/-- Runtime input for an arbitrary finite exactly-one family. -/
def encodeAffineExactlyOneFamily : List AffineExactlyOneFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineExactlyOneFrame frame ++ encodeAffineExactlyOneFamily rest

/-- Exact forward byte stream of an arbitrary finite exactly-one family. -/
def affineExactlyOneFamilyGateStream : List AffineExactlyOneFrame → List CircuitSym
  | [] => []
  | frame :: rest =>
      affineSequentialExactlyOneGateStream
          frame.start frame.rowBase frame.count ++
        affineExactlyOneFamilyGateStream rest

/-- The recursive family stream is ordinary `flatMap` over runtime frames. -/
theorem affineExactlyOneFamilyGateStream_eq_flatMap
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFamilyGateStream frames =
      frames.flatMap fun frame =>
        affineSequentialExactlyOneGateStream
          frame.start frame.rowBase frame.count := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineExactlyOneFamilyGateStream, ih]

/-- One-group controller cost: frame load, clean core, and loop-back. -/
def affineExactlyOneFrameRevSteps (frame : AffineExactlyOneFrame) : Nat :=
  affineExactlyOneFamilyLoadSteps frame.start frame.rowBase frame.count +
    affineSequentialExactlyOneRevCoreSteps
      frame.start frame.rowBase frame.count + 1

/-- A uniform quadratic envelope for loading and executing one framed group. -/
theorem affineExactlyOneFrameRev_steps_le (frame : AffineExactlyOneFrame) :
    affineExactlyOneFrameRevSteps frame ≤
      400 * (encodeAffineExactlyOneFrame frame).length ^ 2 := by
  have hcore : affineSequentialExactlyOneRevCoreSteps
      frame.start frame.rowBase frame.count ≤
      affineSequentialExactlyOneRevSteps
        frame.start frame.rowBase frame.count := by
    simp [affineSequentialExactlyOneRevSteps]
  have hfull := affineSequentialExactlyOneRev_steps_le
    frame.start frame.rowBase frame.count
  rw [encodeAffineExactlyOneFrame_length]
  simp only [affineExactlyOneFrameRevSteps, affineExactlyOneFamilyLoadSteps]
  nlinarith

/-- Total family cost, including the final empty-input check and halt. -/
def affineExactlyOneFamilyRevSteps : List AffineExactlyOneFrame → Nat
  | [] => 2
  | frame :: rest =>
      affineExactlyOneFrameRevSteps frame + affineExactlyOneFamilyRevSteps rest

/-- The whole arbitrary-length family runs quadratically in the explicit
delimiter-bearing frame length. -/
theorem affineExactlyOneFamilyRev_steps_le (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFamilyRevSteps frames ≤
      400 * (encodeAffineExactlyOneFamily frames).length ^ 2 + 2 := by
  induction frames with
  | nil => simp [affineExactlyOneFamilyRevSteps, encodeAffineExactlyOneFamily]
  | cons frame rest ih =>
      have hframe := affineExactlyOneFrameRev_steps_le frame
      simp only [affineExactlyOneFamilyRevSteps, encodeAffineExactlyOneFamily,
        List.length_append]
      have hsquare :
          (encodeAffineExactlyOneFrame frame).length ^ 2 +
              (encodeAffineExactlyOneFamily rest).length ^ 2 ≤
            ((encodeAffineExactlyOneFrame frame).length +
              (encodeAffineExactlyOneFamily rest).length) ^ 2 := by
        calc
          (encodeAffineExactlyOneFrame frame).length ^ 2 +
                (encodeAffineExactlyOneFamily rest).length ^ 2 ≤
              (encodeAffineExactlyOneFrame frame).length ^ 2 +
                (encodeAffineExactlyOneFamily rest).length ^ 2 +
                2 * (encodeAffineExactlyOneFrame frame).length *
                  (encodeAffineExactlyOneFamily rest).length := by omega
          _ = ((encodeAffineExactlyOneFrame frame).length +
              (encodeAffineExactlyOneFamily rest).length) ^ 2 := by ring
      calc
        affineExactlyOneFrameRevSteps frame + affineExactlyOneFamilyRevSteps rest ≤
            400 * (encodeAffineExactlyOneFrame frame).length ^ 2 +
              (400 * (encodeAffineExactlyOneFamily rest).length ^ 2 + 2) :=
          Nat.add_le_add hframe ih
        _ = 400 * ((encodeAffineExactlyOneFrame frame).length ^ 2 +
              (encodeAffineExactlyOneFamily rest).length ^ 2) + 2 := by ring
        _ ≤ 400 * ((encodeAffineExactlyOneFrame frame).length +
              (encodeAffineExactlyOneFamily rest).length) ^ 2 + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 400 hsquare) 2

/-- Clean loop-header configuration. -/
def affineExactlyOneFamilyLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.load .load₁) none none false input output
    [] [] [] [] []

/-- Execute one framed group and return to the clean loop header with the
unconsumed family intact. -/
def affineExactlyOneFamily_runOne (frame : AffineExactlyOneFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyLoopCfg (encodeAffineExactlyOneFrame frame ++ tail) output)
      (some (affineExactlyOneFamilyLoopCfg tail
        ((affineSequentialExactlyOneGateStream
          frame.start frame.rowBase frame.count).reverse ++ output)))
      (affineExactlyOneFrameRevSteps frame) := by
  have hload := affineExactlyOneFamily_load
    frame.start frame.rowBase frame.count tail output
  have hcore := affineExactlyOneFamilyCore_run
    frame.start frame.rowBase frame.count
    tail output
  let groupOutput :=
    (affineSequentialExactlyOneGateStream
      frame.start frame.rowBase frame.count).reverse ++ output
  have hjump : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCoreExitCfg tail groupOutput)
      (some (affineExactlyOneFamilyLoopCfg tail groupOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughCore := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    (affineExactlyOneFamilyLoadSteps frame.start frame.rowBase frame.count)
    (affineSequentialExactlyOneRevCoreSteps
      frame.start frame.rowBase frame.count)
    _ (affineExactlyOneFamilyReadyCfg
      frame.start frame.rowBase frame.count tail output) _ hload hcore
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    ((affineSequentialExactlyOneRevCoreSteps
        frame.start frame.rowBase frame.count) +
      affineExactlyOneFamilyLoadSteps frame.start frame.rowBase frame.count)
    1 _ (affineExactlyOneFamilyCoreExitCfg tail groupOutput) _ throughCore hjump
  convert full using 1
  · rfl
  · simp [affineExactlyOneFrameRevSteps]
    omega

/-- Runtime cost for a family terminated by an explicit outer
boundary.  Unlike `affineExactlyOneFamilyRevSteps`, the last step stops on the
redirectable `finish` label instead of executing its standalone halt. -/
def affineExactlyOneFamilyUntilEndSteps : List AffineExactlyOneFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineExactlyOneFrameRevSteps frame + affineExactlyOneFamilyUntilEndSteps rest

/-- The explicit stack-frame boundary has been consumed and retained in the
input buffer, ready for an enclosing controller to clear and continue. -/
def affineExactlyOneFamilyFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

/-- An exactly-one family followed by `frameEnd` reaches the redirectable finish
label exactly, preserving the input belonging to later stack frames. -/
def affineExactlyOneFamily_runToFinish (frames : List AffineExactlyOneFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyLoopCfg
        (encodeAffineExactlyOneFamily frames ++ .frameEnd :: tail) output)
      (some (affineExactlyOneFamilyFinishCfg tail
        ((affineExactlyOneFamilyGateStream frames).reverse ++ output)))
      (affineExactlyOneFamilyUntilEndSteps frames) := by
  induction frames generalizing output with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let groupOutput :=
        (affineSequentialExactlyOneGateStream
          frame.start frame.rowBase frame.count).reverse ++ output
      have hfirst := affineExactlyOneFamily_runOne frame
        (encodeAffineExactlyOneFamily rest ++ .frameEnd :: tail) output
      have hrest := ih groupOutput
      let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
        (affineExactlyOneFrameRevSteps frame)
        (affineExactlyOneFamilyUntilEndSteps rest)
        _ (affineExactlyOneFamilyLoopCfg
          (encodeAffineExactlyOneFamily rest ++ .frameEnd :: tail) groupOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneFamily, List.append_assoc]
      · simp [affineExactlyOneFamilyGateStream, groupOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneFamilyUntilEndSteps]
        omega

/-- The redirectable run differs from the standalone run by its final halt
instruction only. -/
@[simp] theorem affineExactlyOneFamilyUntilEndSteps_add_one
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFamilyUntilEndSteps frames + 1 =
      affineExactlyOneFamilyRevSteps frames := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp only [affineExactlyOneFamilyUntilEndSteps, affineExactlyOneFamilyRevSteps]
      omega

/-- The contextual family run inherits the established quadratic bound. -/
theorem affineExactlyOneFamilyUntilEnd_steps_le (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFamilyUntilEndSteps frames ≤
      400 * (encodeAffineExactlyOneFamily frames).length ^ 2 + 1 := by
  have h := affineExactlyOneFamilyRev_steps_le frames
  rw [← affineExactlyOneFamilyUntilEndSteps_add_one] at h
  omega

/-! ## Reusing the embedded kernel for one framed Boolean equality -/

/-- Entry obtained after a three-field loader has restored the Boolean-
equality gate start and source wires.  A dedicated `frameEnd` follows the
kernel so its ordinary loop-back reaches the public family finish boundary. -/
def affineExactlyOneFamilyBoolEqReadyCfg (start left right : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel (.boolEq .notLeft)) none none false
    (.frameEnd :: tail) output [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())

/-- Exact contextual cost of the embedded equality kernel, loop-back, and
explicit outer-boundary check. -/
def affineExactlyOneFamilyBoolEqUntilFinishSteps
    (start left right : Nat) : Nat :=
  affineBoolEqRevCoreSteps start left right + 2

/-- The already embedded sequential kernel can execute one framed Boolean
equality and stop at the same redirectable family boundary used after raw
one-hot groups. -/
def affineExactlyOneFamily_boolEq_runToFinish
    (start left right : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyBoolEqReadyCfg
        start left right tail output)
      (some (affineExactlyOneFamilyFinishCfg tail
        ((affineBoolEqGateStream start left right).reverse ++ output)))
      (affineExactlyOneFamilyBoolEqUntilFinishSteps start left right) := by
  have hsource : isAffineExactlyOneKernelCfg
      (affineBoolEqBodyCfg start left right output) := by
    simp [affineBoolEqBodyCfg, sequentialExactlyOneCfg,
      isAffineExactlyOneKernelCfg, isAffineExactlyOneKernelLabel,
      isAffineExactlyOneCont]
  have hrun := affineBoolEqRev_runToHaltLabel start left right output
  have htarget : (sequentialExactlyOneCfg .halt none none false []
      ((affineBoolEqGateStream start left right).reverse ++ output)
      [] [] [] [] []).label = some .halt := rfl
  have hlift := liftExactlyOneKernel_iterations .halt rfl
    (.frameEnd :: tail) hsource htarget hrun.steps hrun.evals_in_steps
  have hsourceLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (affineBoolEqBodyCfg start left right output) =
        affineExactlyOneFamilyBoolEqReadyCfg
          start left right tail output := by
    rfl
  have htargetLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (sequentialExactlyOneCfg .halt none none false []
        ((affineBoolEqGateStream start left right).reverse ++ output)
        [] [] [] [] []) =
      affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
        ((affineBoolEqGateStream start left right).reverse ++ output) := by
    rfl
  rw [hsourceLift, htargetLift] at hlift
  let equalityOutput :=
    (affineBoolEqGateStream start left right).reverse ++ output
  have hfinish : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) equalityOutput)
      (some (affineExactlyOneFamilyFinishCfg tail equalityOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    (affineBoolEqRevCoreSteps start left right) 2 _
    (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) equalityOutput)
    _ (by simpa [equalityOutput] using
      (show EvalsToInTime (step affineExactlyOneFamilyRevProgram)
        (affineExactlyOneFamilyBoolEqReadyCfg start left right tail output)
        (some (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
          equalityOutput)) (affineBoolEqRevCoreSteps start left right) from
            ⟨⟨hrun.steps, hlift⟩, hrun.steps_le_m⟩)) hfinish
  simpa [affineExactlyOneFamilyBoolEqUntilFinishSteps, equalityOutput,
    Nat.add_comm] using full

/-! ## Reusing the embedded kernel for one framed negation -/

/-- Contextual entry for one arbitrary NOT gate. -/
def affineExactlyOneFamilyNotReadyCfg (source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel (.singleNot .push)) none none false
    (.frameEnd :: tail) output [] [] [] [] (List.replicate source ())

def affineExactlyOneFamilyNotUntilFinishSteps (source : Nat) : Nat :=
  affineNotRevCoreSteps source + 2

/-- Execute one NOT gate in the shared fixed controller and stop at its public
tail-preserving finish boundary. -/
def affineExactlyOneFamily_not_runToFinish
    (source : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyNotReadyCfg source tail output)
      (some (affineExactlyOneFamilyFinishCfg tail
        ((affineNotGateStream source).reverse ++ output)))
      (affineExactlyOneFamilyNotUntilFinishSteps source) := by
  have hsource : isAffineExactlyOneKernelCfg
      (affineNotBodyCfg source output) := by
    simp [affineNotBodyCfg, sequentialExactlyOneCfg,
      isAffineExactlyOneKernelCfg, isAffineExactlyOneKernelLabel,
      isAffineExactlyOneCont]
  have hrun := affineNotRev_runToHaltLabel source output
  have htarget : (sequentialExactlyOneCfg .halt none none false []
      ((affineNotGateStream source).reverse ++ output)
      [] [] [] [] []).label = some .halt := rfl
  have hlift := liftExactlyOneKernel_iterations .halt rfl
    (.frameEnd :: tail) hsource htarget hrun.steps hrun.evals_in_steps
  have hsourceLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (affineNotBodyCfg source output) =
        affineExactlyOneFamilyNotReadyCfg source tail output := by
    rfl
  have htargetLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (sequentialExactlyOneCfg .halt none none false []
        ((affineNotGateStream source).reverse ++ output)
        [] [] [] [] []) =
      affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
        ((affineNotGateStream source).reverse ++ output) := by
    rfl
  rw [hsourceLift, htargetLift] at hlift
  let gateOutput := (affineNotGateStream source).reverse ++ output
  have hfinish : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) gateOutput)
      (some (affineExactlyOneFamilyFinishCfg tail gateOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    (affineNotRevCoreSteps source) 2 _
    (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) gateOutput) _
    (by simpa [gateOutput] using
      (show EvalsToInTime (step affineExactlyOneFamilyRevProgram)
        (affineExactlyOneFamilyNotReadyCfg source tail output)
        (some (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
          gateOutput)) (affineNotRevCoreSteps source) from
            ⟨⟨hrun.steps, hlift⟩, hrun.steps_le_m⟩)) hfinish
  simpa [affineExactlyOneFamilyNotUntilFinishSteps, gateOutput,
    Nat.add_comm] using full

/-! ## Reusing the embedded kernel for one framed disjunction -/

/-- Contextual entry for one arbitrary OR gate, represented as the
one-element case of the established suffix-OR scanner. -/
def affineExactlyOneFamilyOrReadyCfg (left right : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel (.suffixOr .next)) none none false
    (.frameEnd :: tail) output [.tick] []
    (List.replicate left ()) [] (List.replicate (right + 1) ())

def affineExactlyOneFamilyOrUntilFinishSteps (left right : Nat) : Nat :=
  affineOrRevCoreSteps left right + 2

/-- Execute one OR gate in the shared fixed controller and stop at its public
tail-preserving finish boundary. -/
def affineExactlyOneFamily_or_runToFinish
    (left right : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyOrReadyCfg left right tail output)
      (some (affineExactlyOneFamilyFinishCfg tail
        ((affineOrGateStream left right).reverse ++ output)))
      (affineExactlyOneFamilyOrUntilFinishSteps left right) := by
  have hsource : isAffineExactlyOneKernelCfg
      (affineOrBodyCfg left right output) := by
    simp [affineOrBodyCfg, sequentialExactlyOneCfg,
      isAffineExactlyOneKernelCfg, isAffineExactlyOneKernelLabel,
      isAffineExactlyOneCont]
  have hrun := affineOrRev_runToHaltLabel left right output
  have htarget : (sequentialExactlyOneCfg .halt none none false []
      ((affineOrGateStream left right).reverse ++ output)
      [] [] [] [] []).label = some .halt := rfl
  have hlift := liftExactlyOneKernel_iterations .halt rfl
    (.frameEnd :: tail) hsource htarget hrun.steps hrun.evals_in_steps
  have hsourceLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (affineOrBodyCfg left right output) =
        affineExactlyOneFamilyOrReadyCfg left right tail output := by
    rfl
  have htargetLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (sequentialExactlyOneCfg .halt none none false []
        ((affineOrGateStream left right).reverse ++ output)
        [] [] [] [] []) =
      affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
        ((affineOrGateStream left right).reverse ++ output) := by
    rfl
  rw [hsourceLift, htargetLift] at hlift
  let gateOutput := (affineOrGateStream left right).reverse ++ output
  have hfinish : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) gateOutput)
      (some (affineExactlyOneFamilyFinishCfg tail gateOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    (affineOrRevCoreSteps left right) 2 _
    (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail) gateOutput) _
    (by simpa [gateOutput] using
      (show EvalsToInTime (step affineExactlyOneFamilyRevProgram)
        (affineExactlyOneFamilyOrReadyCfg left right tail output)
        (some (affineExactlyOneFamilyCoreExitCfg (.frameEnd :: tail)
          gateOutput)) (affineOrRevCoreSteps left right) from
            ⟨⟨hrun.steps, hlift⟩, hrun.steps_le_m⟩)) hfinish
  simpa [affineExactlyOneFamilyOrUntilFinishSteps, gateOutput,
    Nat.add_comm] using full

/-! ## Reusing the embedded kernel for one framed conjunction -/

/-- Contextual entry for one AND gate.  The first operand is stored in the
kernel's carry register and the second in its source register; the emitted
gate is therefore `.and source carry`. -/
def affineExactlyOneFamilyAndReadyCfg (carry source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel (.conjunction .push)) none none false
    (.frameEnd :: tail) output [] []
    (List.replicate carry ()) [] (List.replicate source ())

/-- Redirect point immediately after the embedded conjunction kernel. -/
def affineExactlyOneFamilyAndCoreExitCfg (carry : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineExactlyOneFamilyRevProgram :=
  affineExactlyOneFamilyCfg (.kernel (.conjunction .done)) none none false
    (.frameEnd :: tail) output [] []
    (List.replicate (carry + 1) ()) [] []

private theorem affineExactlyOneFamilyAndClear_eval (count : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[count + 1]
      (some (affineExactlyOneFamilyCfg .andClear none none false
        (.frameEnd :: tail) output [] [] (List.replicate count ()) [] [])) =
      some (affineExactlyOneFamilyCfg (.load .load₁) none none false
        (.frameEnd :: tail) output [] [] [] [] []) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneFamilyRevProgram))^[count + 1]
          (some (affineExactlyOneFamilyCfg .andClear none none false
            (.frameEnd :: tail) output [] [] (List.replicate count ()) [] [])) = _
      exact ih

/-- Exact contextual cost of the embedded conjunction, register cleanup,
and explicit outer-boundary check. -/
def affineExactlyOneFamilyAndUntilFinishSteps
    (carry source : Nat) : Nat :=
  affineAndRevCoreSteps carry source + carry + 4

/-- Execute one AND gate inside the shared fixed controller, clear the
advanced carry register, and stop at the same public family boundary as the
Boolean-equality component. -/
def affineExactlyOneFamily_and_runToFinish
    (carry source : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyAndReadyCfg carry source tail output)
      (some (affineExactlyOneFamilyFinishCfg tail
        ((affineAndGateStream carry source).reverse ++ output)))
      (affineExactlyOneFamilyAndUntilFinishSteps carry source) := by
  have hsource : isAffineExactlyOneKernelCfg
      (affineAndBodyCfg carry source output) := by
    simp [affineAndBodyCfg, sequentialExactlyOneCfg,
      isAffineExactlyOneKernelCfg, isAffineExactlyOneKernelLabel]
  have hrun := affineAndRev_runToDoneLabel carry source output
  have htarget : (affineAndCoreExitCfg carry
      ((affineAndGateStream carry source).reverse ++ output)).label =
        some (.conjunction .done) := rfl
  have hlift := liftExactlyOneKernel_iterations (.conjunction .done) rfl
    (.frameEnd :: tail) hsource htarget hrun.steps hrun.evals_in_steps
  have hsourceLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (affineAndBodyCfg carry source output) =
        affineExactlyOneFamilyAndReadyCfg carry source tail output := by
    rfl
  have htargetLift : liftExactlyOneKernelCfg (.frameEnd :: tail)
      (affineAndCoreExitCfg carry
        ((affineAndGateStream carry source).reverse ++ output)) =
      affineExactlyOneFamilyAndCoreExitCfg carry tail
        ((affineAndGateStream carry source).reverse ++ output) := by
    rfl
  rw [hsourceLift, htargetLift] at hlift
  let gateOutput := (affineAndGateStream carry source).reverse ++ output
  let beforeClear := affineExactlyOneFamilyCfg .andClear none none false
    (.frameEnd :: tail) gateOutput [] []
    (List.replicate (carry + 1) ()) [] []
  let beforeLoad := affineExactlyOneFamilyCfg (.load .load₁) none none false
    (.frameEnd :: tail) gateOutput [] [] [] [] []
  have hredirect : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyAndCoreExitCfg carry tail gateOutput)
      (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      beforeClear (some beforeLoad) (carry + 2) := by
    refine ⟨⟨carry + 2, ?_⟩, le_rfl⟩
    simpa [beforeClear, beforeLoad, Nat.add_assoc] using
      affineExactlyOneFamilyAndClear_eval (carry + 1) tail gateOutput
  have hfinish : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      beforeLoad (some (affineExactlyOneFamilyFinishCfg tail gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hcore : EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyAndReadyCfg carry source tail output)
      (some (affineExactlyOneFamilyAndCoreExitCfg carry tail gateOutput))
      (affineAndRevCoreSteps carry source) :=
    ⟨⟨hrun.steps, by simpa [gateOutput] using hlift⟩, hrun.steps_le_m⟩
  let throughRedirect := EvalsToInTime.trans
    (step affineExactlyOneFamilyRevProgram)
    (affineAndRevCoreSteps carry source) 1 _
    (affineExactlyOneFamilyAndCoreExitCfg carry tail gateOutput) _
    hcore hredirect
  let throughClear := EvalsToInTime.trans
    (step affineExactlyOneFamilyRevProgram)
    _ (carry + 2) _ beforeClear _
    throughRedirect hclear
  let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
    _ 1 _ beforeLoad _
    throughClear hfinish
  convert full using 1 <;>
    simp [affineExactlyOneFamilyAndUntilFinishSteps, gateOutput] <;> omega

/-- Empty framed family terminates successfully without changing output. -/
def affineExactlyOneFamily_empty_run (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyCfg (.load .load₁) none none false [] output
        [] [] [] [] [])
      (some (haltCfg affineExactlyOneFamilyRevProgram output)) 2 :=
  ⟨⟨2, rfl⟩, le_rfl⟩

/-- Execute any finite delimiter-bearing family with one fixed controller.
The final byte stream agrees exactly with concatenating the semantic group
streams in input order. -/
def affineExactlyOneFamily_run (frames : List AffineExactlyOneFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineExactlyOneFamilyRevProgram)
      (affineExactlyOneFamilyLoopCfg (encodeAffineExactlyOneFamily frames) output)
      (some (haltCfg affineExactlyOneFamilyRevProgram
        ((affineExactlyOneFamilyGateStream frames).reverse ++ output)))
      (affineExactlyOneFamilyRevSteps frames) := by
  induction frames generalizing output with
  | nil =>
      simpa [encodeAffineExactlyOneFamily, affineExactlyOneFamilyGateStream,
        affineExactlyOneFamilyRevSteps, affineExactlyOneFamilyLoopCfg] using
        affineExactlyOneFamily_empty_run output
  | cons frame rest ih =>
      let groupOutput :=
        (affineSequentialExactlyOneGateStream
          frame.start frame.rowBase frame.count).reverse ++ output
      have hfirst := affineExactlyOneFamily_runOne frame
        (encodeAffineExactlyOneFamily rest) output
      have hrest := ih groupOutput
      let full := EvalsToInTime.trans (step affineExactlyOneFamilyRevProgram)
        (affineExactlyOneFrameRevSteps frame) (affineExactlyOneFamilyRevSteps rest)
        _ (affineExactlyOneFamilyLoopCfg (encodeAffineExactlyOneFamily rest) groupOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneFamily, encodeAffineExactlyOneFrame,
          affineExactlyOneFamilyLoopCfg]
      · simp [affineExactlyOneFamilyGateStream, groupOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneFamilyRevSteps]
        omega

end CLRS.Chapter34.Turing.PolyBuilder
