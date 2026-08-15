import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Cell
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Fixed controller for a framed family of cell-validity blocks

The input is a concatenation of triples `(right, left, blank)` in the
delimiter-bearing unary format.  Empty input terminates successfully.  A
complete triple loads the three local counters and enters the established
non-halting cell kernel.  The kernel's clean halt label is redirected to the
next triple instead of executing the standalone halt instruction.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Fixed finite-control phases of the three-field frame prelude. -/
inductive AffineCellFamilyLoadLabel
  | load₁ | inc₁
  | load₂ | inc₂
  | load₃ | inc₃
  | clearBuffer
deriving DecidableEq, Fintype

/-- Grouped finite control keeps the already large cell kernel beneath one
constructor and avoids derived-`Fintype` nested-sum depth failures. -/
inductive AffineCellFamilyLabel
  | load (phase : AffineCellFamilyLoadLabel)
  | cell (label : SequentialExactlyOneLabel)
  | finish | invalid
deriving DecidableEq, Fintype

/-- Relabel one established cell-kernel instruction onto the framed input
alphabet.  Unit scratch symbols become frame `tick`s.  The kernel never reads
the persistent input while executing a cell. -/
private def liftCellKernelOp :
    Op Unit CircuitSym SequentialExactlyOneLabel →
      Op UnaryFrameSym CircuitSym AffineCellFamilyLabel
  | .pushOutput symbol next => .pushOutput symbol (.cell next)
  | .pushWork₁ _ next => .pushWork₁ .tick (.cell next)
  | .pushWork₂ _ next => .pushWork₂ .tick (.cell next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.cell nextEmpty) (fun _ => .cell (nextMoved ()))
  | .copyInputWorks nextEmpty nextCopied =>
      .copyInputWorks (.cell nextEmpty) (fun _ => .cell (nextCopied ()))
  | .popInput nextEmpty nextSome =>
      .popInput (.cell nextEmpty) (fun _ => .cell (nextSome ()))
  | .popWork₁ nextEmpty nextSome =>
      .popWork₁ (.cell nextEmpty) (fun _ => .cell (nextSome ()))
  | .popWork₂ nextEmpty nextSome =>
      .popWork₂ (.cell nextEmpty) (fun _ => .cell (nextSome ()))
  | .inc₁ next => .inc₁ (.cell next)
  | .inc₂ next => .inc₂ (.cell next)
  | .inc₃ next => .inc₃ (.cell next)
  | .dec₁ nextZero nextSucc => .dec₁ (.cell nextZero) (.cell nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.cell nextZero) (.cell nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.cell nextZero) (.cell nextSucc)
  | .jump next => .jump (.cell next)
  | .halt => .halt

/-- One fixed program for every finite framed family.  The family length and
all gate/source indices are runtime stack data, never control labels. -/
def affineCellFamilyRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineCellFamilyLabel
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
        | .separator => .load .clearBuffer
        | .frameEnd => .invalid
    | .load .inc₃ => .inc₃ (.load .load₃)
    | .load .clearBuffer =>
        .popWork₁ (.cell (.cell .notPush)) (fun _ => .invalid)
    | .cell .halt => .jump (.load .load₁)
    | .cell label => liftCellKernelOp (sequentialExactlyOneRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Embed a kernel configuration while retaining an untouched framed input
tail.  Unit scratch symbols are represented by frame ticks. -/
private def liftCellKernelCfg (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram) :
    BuilderCfg affineCellFamilyRevProgram where
  label := c.label.map .cell
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

private def isAffineCellCont : SequentialExactlyOneCont → Prop
  | .boolEqNotLeft | .boolEqNotRight
  | .boolEqAndLeft | .boolEqAndRight
  | .boolEqAndStart | .boolEqAndNext
  | .boolEqOrStart | .boolEqOrNext
  | .affineCellNotWire => True
  | _ => False

private def isAffineCellKernelLabel : SequentialExactlyOneLabel → Prop
  | .encode _ cont | .save _ cont | .pushArg _ cont | .pushEnd _ cont
  | .restore _ cont | .restoreInc _ cont => isAffineCellCont cont
  | .resume cont => isAffineCellCont cont
  | .boolEq _ | .cell _ | .clear₁ | .clear₂ | .clear₃ | .halt => True
  | _ => False

private def isAffineCellKernelCfg
    (c : BuilderCfg sequentialExactlyOneRevProgram) : Prop :=
  match c.label with
  | none => False
  | some label => isAffineCellKernelLabel label

private def preservesFramedInput :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .moveInputWork₁ .. | .moveWork₁Input ..
  | .moveInputWork₂ .. | .moveWork₂Input ..
  | .copyInputWorks .. | .popInput .. => False
  | _ => True

private theorem liftCellKernel_stepOp (tail : List UnaryFrameSym)
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hsafe : preservesFramedInput op) :
    stepOp (liftCellKernelOp op) (liftCellKernelCfg tail c) =
      liftCellKernelCfg tail (stepOp op c) := by
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

private theorem affineCellKernel_op_preservesFramedInput
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineCellKernelLabel label) :
    preservesFramedInput (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont =>
      cases register <;> trivial
  | restoreInc register cont =>
      cases register <;> trivial
  | resume cont =>
      cases cont <;> simp_all [isAffineCellKernelLabel, isAffineCellCont,
        preservesFramedInput, sequentialExactlyOneRevProgram]
  | boolEq phase => cases phase <;> trivial
  | cell phase => cases phase <;> trivial
  | _ =>
      simp_all [isAffineCellKernelLabel, isAffineCellCont,
        preservesFramedInput, sequentialExactlyOneRevProgram]

private theorem affineCellFamily_op_cell
    (label : SequentialExactlyOneLabel) (hlabel : label ≠ .halt) :
    affineCellFamilyRevProgram.op (.cell label) =
      liftCellKernelOp (sequentialExactlyOneRevProgram.op label) := by
  cases label <;> simp_all [affineCellFamilyRevProgram]

/-- Every non-input, non-exit kernel instruction is simulated exactly under
the framed-alphabet embedding. -/
private theorem liftCellKernel_step (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineCellKernelCfg c) (hexit : c.label ≠ some .halt) :
    step affineCellFamilyRevProgram (liftCellKernelCfg tail c) =
      Option.map (liftCellKernelCfg tail)
        (step sequentialExactlyOneRevProgram c) := by
  unfold step
  rw [show (liftCellKernelCfg tail c).label = c.label.map .cell by rfl]
  cases hlabel : c.label with
  | none => simp [isAffineCellKernelCfg, hlabel] at hkernel
  | some label =>
      have hlabelKernel : isAffineCellKernelLabel label := by
        simpa [isAffineCellKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineCellFamily_op_cell label hlabelExit]
      exact congrArg some (liftCellKernel_stepOp tail
        (sequentialExactlyOneRevProgram.op label) c
        (affineCellKernel_op_preservesFramedInput label hlabelKernel))

private def staysInAffineCellKernel :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .pushOutput _ next | .pushWork₁ _ next | .pushWork₂ _ next
  | .inc₁ next | .inc₂ next | .inc₃ next | .jump next =>
      isAffineCellKernelLabel next
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
      isAffineCellKernelLabel nextEmpty ∧
        ∀ symbol, isAffineCellKernelLabel (nextMoved symbol)
  | .dec₁ nextZero nextSucc | .dec₂ nextZero nextSucc
  | .dec₃ nextZero nextSucc =>
      isAffineCellKernelLabel nextZero ∧
        isAffineCellKernelLabel nextSucc
  | .halt => False

private theorem stepOp_staysInAffineCellKernel
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hop : staysInAffineCellKernel op) :
    isAffineCellKernelCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | pushWork₁ => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | pushWork₂ => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | moveInputWork₁ => cases input <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | moveWork₁Input => cases work₁ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | moveInputWork₂ => cases input <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | moveWork₂Input => cases work₂ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | moveWork₁Work₂ => cases work₁ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | moveWork₂Work₁ => cases work₂ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | copyInputWorks => cases input <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | popInput => cases input <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | popWork₁ => cases work₁ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | popWork₂ => cases work₂ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | inc₁ => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | inc₂ => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | inc₃ => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | dec₁ => cases counter₁ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | dec₂ => cases counter₂ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | dec₃ => cases counter₃ <;> simp_all [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp]
  | jump => simpa [staysInAffineCellKernel,
      isAffineCellKernelCfg, stepOp] using hop
  | halt => simp [staysInAffineCellKernel] at hop

private theorem affineCellKernel_op_stays
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineCellKernelLabel label) (hexit : label ≠ .halt) :
    staysInAffineCellKernel (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont =>
      cases register <;> exact ⟨hkernel, hkernel⟩
  | save register cont => exact hkernel
  | pushArg register cont => exact hkernel
  | pushEnd register cont => exact hkernel
  | restore register cont => exact ⟨hkernel, fun _ => hkernel⟩
  | restoreInc register cont => cases register <;> exact hkernel
  | resume cont =>
      cases cont <;> simp_all [isAffineCellKernelLabel, isAffineCellCont,
        staysInAffineCellKernel, sequentialExactlyOneRevProgram]
  | boolEq phase =>
      cases phase <;> simp [staysInAffineCellKernel,
        sequentialExactlyOneRevProgram, isAffineCellKernelLabel,
        isAffineCellCont]
  | cell phase =>
      cases phase <;> simp [staysInAffineCellKernel,
        sequentialExactlyOneRevProgram, isAffineCellKernelLabel,
        isAffineCellCont]
  | clear₁ => trivial
  | clear₂ => trivial
  | clear₃ => trivial
  | halt => simp at hexit
  | _ => simp [isAffineCellKernelLabel] at hkernel

private theorem affineCellKernel_step_closed
    (c c' : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineCellKernelCfg c) (hexit : c.label ≠ some .halt)
    (hstep : step sequentialExactlyOneRevProgram c = some c') :
    isAffineCellKernelCfg c' := by
  unfold step at hstep
  cases hlabel : c.label with
  | none => simp [hlabel] at hstep
  | some label =>
      have hlabelKernel : isAffineCellKernelLabel label := by
        simpa [isAffineCellKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      rw [hlabel] at hstep
      injection hstep with hc'
      subst c'
      exact stepOp_staysInAffineCellKernel
        (sequentialExactlyOneRevProgram.op label) c
        (affineCellKernel_op_stays label hlabelKernel hlabelExit)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem sequential_halt_no_return
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
        counter₃ := counter₃ } = some halted := by
    rfl
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

private theorem liftCellKernel_iterations (tail : List UnaryFrameSym)
    {a b : BuilderCfg sequentialExactlyOneRevProgram}
    (ha : isAffineCellKernelCfg a) (hb : b.label = some .halt) :
    ∀ n : Nat,
      (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
          (some a) = some b →
        (flip Option.bind (step affineCellFamilyRevProgram))^[n]
          (some (liftCellKernelCfg tail a)) =
            some (liftCellKernelCfg tail b) := by
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
        (flip Option.bind (step affineCellFamilyRevProgram))^[n]
          (step affineCellFamilyRevProgram (liftCellKernelCfg tail a)) =
            some (liftCellKernelCfg tail b)
      have haexit : a.label ≠ some .halt := by
        intro haHalt
        exact sequential_halt_no_return a b haHalt hb n h
      cases hstep : step sequentialExactlyOneRevProgram a with
      | none =>
          rw [hstep, iterate_bind_none] at h
          contradiction
      | some c =>
          have hc := affineCellKernel_step_closed a c ha haexit hstep
          have hsim := liftCellKernel_step tail a ha haexit
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih hc h

/-- Fieldwise configuration surface for the framed family controller. -/
def affineCellFamilyCfg (label : AffineCellFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineCellFamilyRevProgram where
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

/-- Cell-kernel entry after one complete triple has been consumed. -/
def affineCellFamilyReadyCfg (right left blank : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg affineCellFamilyRevProgram :=
  affineCellFamilyCfg (.cell (.cell .notPush)) none none false
    tail output work₁ work₂ (List.replicate right ())
    (List.replicate left ()) (List.replicate blank ())

/-- Clean redirect point reached after one cell kernel has emitted its exact
six-gate block and cleared all scratch state. -/
def affineCellFamilyCoreExitCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineCellFamilyRevProgram :=
  affineCellFamilyCfg (.cell .halt) none none false tail output
    [] [] [] [] []

/-- The established cell core transports to the framed controller without
touching the persistent tail. -/
def affineCellFamilyCore_run (right left blank : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyReadyCfg right left blank tail output [] [])
      (some (affineCellFamilyCoreExitCfg tail
        ((affineCellGateStream right left blank).reverse ++ output)))
      (affineCellRevCoreSteps right left blank) := by
  let source := affineCellBodyCfg right left blank output
  let target := sequentialExactlyOneCfg .halt none none false []
    ((affineCellGateStream right left blank).reverse ++ output)
    [] [] [] [] []
  have hrun := affineCellRev_runToHaltLabel right left blank output
  have hsource : isAffineCellKernelCfg source := by
    simp [source, affineCellBodyCfg, sequentialExactlyOneCfg,
      isAffineCellKernelCfg, isAffineCellKernelLabel]
  have htarget : target.label = some .halt := rfl
  refine ⟨⟨hrun.steps, ?_⟩, hrun.steps_le_m⟩
  have hlift := liftCellKernel_iterations tail hsource htarget
    hrun.steps hrun.evals_in_steps
  have hsourceLift : liftCellKernelCfg tail source =
      affineCellFamilyReadyCfg right left blank tail output [] [] := by
    rfl
  have htargetLift : liftCellKernelCfg tail target =
      affineCellFamilyCoreExitCfg tail
        ((affineCellGateStream right left blank).reverse ++ output) := by
    rfl
  rw [← hsourceLift, ← htargetLift]
  exact hlift

/-- Exact cost of loading one framed cell triple. -/
def affineCellFamilyLoadSteps (right left blank : Nat) : Nat :=
  2 * (right + left + blank) + 4

private theorem replicate_append_cons (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem loadFirst_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
      (some (affineCellFamilyCfg (.load .load₁) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineCellFamilyCfg (.load .load₂) (some .separator) buffer₂ test
        tail output work₁ work₂ (List.replicate value () ++ first)
        second third) := by
  induction value generalizing buffer₁ test first with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
          (some (affineCellFamilyCfg (.load .load₁) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            (() :: first) second third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: first)

private theorem loadSecond_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
      (some (affineCellFamilyCfg (.load .load₂) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineCellFamilyCfg (.load .load₃) (some .separator) buffer₂ test
        tail output work₁ work₂ first (List.replicate value () ++ second)
        third) := by
  induction value generalizing buffer₁ test second with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
          (some (affineCellFamilyCfg (.load .load₂) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first (() :: second) third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: second)

private theorem loadThird_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
      (some (affineCellFamilyCfg (.load .load₃) buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (affineCellFamilyCfg (.load .clearBuffer) (some .separator)
        buffer₂ test tail output work₁ work₂ first second
        (List.replicate value () ++ third)) := by
  induction value generalizing buffer₁ test third with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineCellFamilyRevProgram))^[2 * value + 1]
          (some (affineCellFamilyCfg (.load .load₃) (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first second (() :: third))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) test (() :: third)

/-- Consume one complete framed triple, preserve the remaining family and all
symbol stacks, and enter the non-halting cell kernel with exact counters. -/
def affineCellFamily_load (right left blank : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₂ : List UnaryFrameSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyCfg (.load .load₁) none none false
        (encodeUnaryFrame [right, left, blank] ++ tail)
        output [] work₂ [] [] [])
      (some (affineCellFamilyReadyCfg right left blank tail output
        [] work₂))
      (affineCellFamilyLoadSteps right left blank) := by
  let afterFirst := affineCellFamilyCfg (.load .load₂) (some .separator)
    none false
    (encodeUnaryFrameBlock left ++ encodeUnaryFrameBlock blank ++ tail)
    output [] work₂ (List.replicate right ()) [] []
  let afterSecond := affineCellFamilyCfg (.load .load₃) (some .separator)
    none false (encodeUnaryFrameBlock blank ++ tail) output [] work₂
    (List.replicate right ()) (List.replicate left ()) []
  have hfirst : EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyCfg (.load .load₁) none none false
        (encodeUnaryFrame [right, left, blank] ++ tail)
        output [] work₂ [] [] [])
      (some afterFirst) (2 * right + 1) := by
    refine ⟨⟨2 * right + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, encodeUnaryFrame, List.append_assoc] using
      loadFirst_eval right none none false
        (encodeUnaryFrameBlock left ++ encodeUnaryFrameBlock blank ++ tail)
        output [] work₂ [] [] []
  have hsecond : EvalsToInTime (step affineCellFamilyRevProgram)
      afterFirst (some afterSecond) (2 * left + 1) := by
    refine ⟨⟨2 * left + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, afterSecond, List.append_assoc] using
      loadSecond_eval left (some .separator) none false
        (encodeUnaryFrameBlock blank ++ tail) output [] work₂
        (List.replicate right ()) [] []
  let beforeReady := affineCellFamilyCfg (.load .clearBuffer)
    (some .separator) none false tail output [] work₂
    (List.replicate right ()) (List.replicate left ())
    (List.replicate blank ())
  have hthird : EvalsToInTime (step affineCellFamilyRevProgram)
      afterSecond
      (some beforeReady) (2 * blank + 1) := by
    refine ⟨⟨2 * blank + 1, ?_⟩, le_rfl⟩
    simpa [afterSecond, beforeReady] using
      loadThird_eval blank (some .separator) none false tail output
        [] work₂ (List.replicate right ()) (List.replicate left ()) []
  have hclear : EvalsToInTime (step affineCellFamilyRevProgram)
      beforeReady
      (some (affineCellFamilyReadyCfg right left blank tail output
        [] work₂)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let throughSecond := EvalsToInTime.trans (step affineCellFamilyRevProgram)
    (2 * right + 1) (2 * left + 1) _ afterFirst _ hfirst hsecond
  let throughThird := EvalsToInTime.trans (step affineCellFamilyRevProgram)
    ((2 * left + 1) + (2 * right + 1)) (2 * blank + 1)
    _ afterSecond _ throughSecond hthird
  let full := EvalsToInTime.trans (step affineCellFamilyRevProgram)
    ((2 * blank + 1) + ((2 * left + 1) + (2 * right + 1))) 1
    _ beforeReady _ throughThird hclear
  convert full using 1
  simp [affineCellFamilyLoadSteps]
  omega

/-- Runtime data for one six-gate cell invocation. -/
structure AffineCellFrame where
  right : Nat
  left : Nat
  blank : Nat
deriving DecidableEq, Repr

/-- Delimiter-bearing input block for one cell. -/
def encodeAffineCellFrame (frame : AffineCellFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.right, frame.left, frame.blank]

/-- Exact framed size of one runtime triple. -/
@[simp] theorem encodeAffineCellFrame_length (frame : AffineCellFrame) :
    (encodeAffineCellFrame frame).length =
      frame.right + frame.left + frame.blank + 3 := by
  simp [encodeAffineCellFrame, encodeUnaryFrame_length]
  omega

/-- Runtime input for an arbitrary finite cell family. -/
def encodeAffineCellFamily : List AffineCellFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineCellFrame frame ++ encodeAffineCellFamily rest

/-- Exact forward byte stream of an arbitrary finite cell family. -/
def affineCellFamilyGateStream : List AffineCellFrame → List CircuitSym
  | [] => []
  | frame :: rest =>
      affineCellGateStream frame.right frame.left frame.blank ++
        affineCellFamilyGateStream rest

/-- The recursive family stream is ordinary `flatMap` over cell frames. -/
theorem affineCellFamilyGateStream_eq_flatMap
    (frames : List AffineCellFrame) :
    affineCellFamilyGateStream frames =
      frames.flatMap fun frame =>
        affineCellGateStream frame.right frame.left frame.blank := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineCellFamilyGateStream, ih]

/-- One-cell controller cost: frame load, clean cell core, and loop-back. -/
def affineCellFrameRevSteps (frame : AffineCellFrame) : Nat :=
  affineCellFamilyLoadSteps frame.right frame.left frame.blank +
    affineCellRevCoreSteps frame.right frame.left frame.blank + 1

/-- A uniform quadratic envelope for loading and executing one framed cell. -/
theorem affineCellFrameRev_steps_le (frame : AffineCellFrame) :
    affineCellFrameRevSteps frame ≤
      250 * (encodeAffineCellFrame frame).length ^ 2 := by
  have hcore : affineCellRevCoreSteps frame.right frame.left frame.blank ≤
      affineCellRevSteps frame.right frame.left frame.blank := by
    simp [affineCellRevCoreSteps, affineCellRevSteps,
      affineBoolEqRevCoreSteps, affineBoolEqRevSteps]
  have hfull := affineCellRev_steps_le frame.right frame.left frame.blank
  rw [encodeAffineCellFrame_length]
  simp only [affineCellFrameRevSteps, affineCellFamilyLoadSteps]
  nlinarith

/-- Total family cost, including the final empty-input check and halt. -/
def affineCellFamilyRevSteps : List AffineCellFrame → Nat
  | [] => 2
  | frame :: rest =>
      affineCellFrameRevSteps frame + affineCellFamilyRevSteps rest

/-- The whole arbitrary-length family runs quadratically in the explicit
delimiter-bearing frame length. -/
theorem affineCellFamilyRev_steps_le (frames : List AffineCellFrame) :
    affineCellFamilyRevSteps frames ≤
      250 * (encodeAffineCellFamily frames).length ^ 2 + 2 := by
  induction frames with
  | nil => simp [affineCellFamilyRevSteps, encodeAffineCellFamily]
  | cons frame rest ih =>
      have hframe := affineCellFrameRev_steps_le frame
      simp only [affineCellFamilyRevSteps, encodeAffineCellFamily,
        List.length_append]
      have hsquare :
          (encodeAffineCellFrame frame).length ^ 2 +
              (encodeAffineCellFamily rest).length ^ 2 ≤
            ((encodeAffineCellFrame frame).length +
              (encodeAffineCellFamily rest).length) ^ 2 := by
        calc
          (encodeAffineCellFrame frame).length ^ 2 +
                (encodeAffineCellFamily rest).length ^ 2 ≤
              (encodeAffineCellFrame frame).length ^ 2 +
                (encodeAffineCellFamily rest).length ^ 2 +
                2 * (encodeAffineCellFrame frame).length *
                  (encodeAffineCellFamily rest).length := by omega
          _ = ((encodeAffineCellFrame frame).length +
              (encodeAffineCellFamily rest).length) ^ 2 := by ring
      calc
        affineCellFrameRevSteps frame + affineCellFamilyRevSteps rest ≤
            250 * (encodeAffineCellFrame frame).length ^ 2 +
              (250 * (encodeAffineCellFamily rest).length ^ 2 + 2) :=
          Nat.add_le_add hframe ih
        _ = 250 * ((encodeAffineCellFrame frame).length ^ 2 +
              (encodeAffineCellFamily rest).length ^ 2) + 2 := by ring
        _ ≤ 250 * ((encodeAffineCellFrame frame).length +
              (encodeAffineCellFamily rest).length) ^ 2 + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 250 hsquare) 2

/-- Clean loop-header configuration. -/
def affineCellFamilyLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineCellFamilyRevProgram :=
  affineCellFamilyCfg (.load .load₁) none none false input output
    [] [] [] [] []

/-- Execute one framed cell and return to the clean loop header with the
unconsumed family intact. -/
def affineCellFamily_runOne (frame : AffineCellFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyLoopCfg (encodeAffineCellFrame frame ++ tail) output)
      (some (affineCellFamilyLoopCfg tail
        ((affineCellGateStream frame.right frame.left frame.blank).reverse ++
          output)))
      (affineCellFrameRevSteps frame) := by
  have hload := affineCellFamily_load frame.right frame.left frame.blank
    tail output []
  have hcore := affineCellFamilyCore_run frame.right frame.left frame.blank
    tail output
  let cellOutput :=
    (affineCellGateStream frame.right frame.left frame.blank).reverse ++ output
  have hjump : EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyCoreExitCfg tail cellOutput)
      (some (affineCellFamilyLoopCfg tail cellOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughCore := EvalsToInTime.trans (step affineCellFamilyRevProgram)
    (affineCellFamilyLoadSteps frame.right frame.left frame.blank)
    (affineCellRevCoreSteps frame.right frame.left frame.blank)
    _ (affineCellFamilyReadyCfg frame.right frame.left frame.blank
      tail output [] []) _ hload hcore
  let full := EvalsToInTime.trans (step affineCellFamilyRevProgram)
    ((affineCellRevCoreSteps frame.right frame.left frame.blank) +
      affineCellFamilyLoadSteps frame.right frame.left frame.blank)
    1 _ (affineCellFamilyCoreExitCfg tail cellOutput) _ throughCore hjump
  convert full using 1
  · rfl
  · simp [affineCellFrameRevSteps]
    omega

/-- Runtime cost for a cell family terminated by an explicit stack-frame
boundary.  Unlike `affineCellFamilyRevSteps`, the last step stops on the
redirectable `finish` label instead of executing its standalone halt. -/
def affineCellFamilyUntilEndSteps : List AffineCellFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineCellFrameRevSteps frame + affineCellFamilyUntilEndSteps rest

/-- The explicit stack-frame boundary has been consumed and retained in the
input buffer, ready for an enclosing controller to clear and continue. -/
def affineCellFamilyFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineCellFamilyRevProgram :=
  affineCellFamilyCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

/-- A cell family followed by `frameEnd` reaches the redirectable finish
label exactly, preserving the input belonging to later stack frames. -/
def affineCellFamily_runToFinish (frames : List AffineCellFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyLoopCfg
        (encodeAffineCellFamily frames ++ .frameEnd :: tail) output)
      (some (affineCellFamilyFinishCfg tail
        ((affineCellFamilyGateStream frames).reverse ++ output)))
      (affineCellFamilyUntilEndSteps frames) := by
  induction frames generalizing output with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let cellOutput :=
        (affineCellGateStream frame.right frame.left frame.blank).reverse ++
          output
      have hfirst := affineCellFamily_runOne frame
        (encodeAffineCellFamily rest ++ .frameEnd :: tail) output
      have hrest := ih cellOutput
      let full := EvalsToInTime.trans (step affineCellFamilyRevProgram)
        (affineCellFrameRevSteps frame)
        (affineCellFamilyUntilEndSteps rest)
        _ (affineCellFamilyLoopCfg
          (encodeAffineCellFamily rest ++ .frameEnd :: tail) cellOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineCellFamily, List.append_assoc]
      · simp [affineCellFamilyGateStream, cellOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineCellFamilyUntilEndSteps]
        omega

/-- The redirectable run differs from the standalone run by its final halt
instruction only. -/
@[simp] theorem affineCellFamilyUntilEndSteps_add_one
    (frames : List AffineCellFrame) :
    affineCellFamilyUntilEndSteps frames + 1 =
      affineCellFamilyRevSteps frames := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp only [affineCellFamilyUntilEndSteps, affineCellFamilyRevSteps]
      omega

/-- The contextual cell-family run inherits the established quadratic bound. -/
theorem affineCellFamilyUntilEnd_steps_le (frames : List AffineCellFrame) :
    affineCellFamilyUntilEndSteps frames ≤
      250 * (encodeAffineCellFamily frames).length ^ 2 + 1 := by
  have h := affineCellFamilyRev_steps_le frames
  rw [← affineCellFamilyUntilEndSteps_add_one] at h
  omega

/-- Empty framed family terminates successfully without changing output. -/
def affineCellFamily_empty_run (output : List CircuitSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyCfg (.load .load₁) none none false [] output
        [] [] [] [] [])
      (some (haltCfg affineCellFamilyRevProgram output)) 2 :=
  ⟨⟨2, rfl⟩, le_rfl⟩

/-- Execute any finite delimiter-bearing family with one fixed controller.
The final byte stream agrees exactly with concatenating the semantic cell
streams in input order. -/
def affineCellFamily_run (frames : List AffineCellFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineCellFamilyRevProgram)
      (affineCellFamilyLoopCfg (encodeAffineCellFamily frames) output)
      (some (haltCfg affineCellFamilyRevProgram
        ((affineCellFamilyGateStream frames).reverse ++ output)))
      (affineCellFamilyRevSteps frames) := by
  induction frames generalizing output with
  | nil =>
      simpa [encodeAffineCellFamily, affineCellFamilyGateStream,
        affineCellFamilyRevSteps, affineCellFamilyLoopCfg] using
        affineCellFamily_empty_run output
  | cons frame rest ih =>
      let cellOutput :=
        (affineCellGateStream frame.right frame.left frame.blank).reverse ++
          output
      have hfirst := affineCellFamily_runOne frame
        (encodeAffineCellFamily rest) output
      have hrest := ih cellOutput
      let full := EvalsToInTime.trans (step affineCellFamilyRevProgram)
        (affineCellFrameRevSteps frame) (affineCellFamilyRevSteps rest)
        _ (affineCellFamilyLoopCfg (encodeAffineCellFamily rest) cellOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineCellFamily, encodeAffineCellFrame,
          affineCellFamilyLoopCfg]
      · simp [affineCellFamilyGateStream, cellOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineCellFamilyRevSteps]
        omega

end CLRS.Chapter34.Turing.PolyBuilder
