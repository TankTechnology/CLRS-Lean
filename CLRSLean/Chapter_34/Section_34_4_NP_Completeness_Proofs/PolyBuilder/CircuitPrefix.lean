import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate
import Mathlib.Tactic

/-!
# Streaming the initial circuit prefix

The general-circuit encoding begins with its input arity and then the gate
stream.  For the canonical tableau allocator, the first gates are precisely
the input gates `0, ..., n - 1`.  This module gives one concrete bounded
builder which parks its unit-clock input, emits the arity header, restores the
clock, and then reuses the verified input-gate streamer.  A final verified
reversal exposes the forward wire format
`encNat n ++ inputGateStream n`.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Exact serialized prefix consisting of the arity header and all canonical
input gates. -/
def circuitInputPrefix (count : Nat) : List CircuitSym :=
  encNat count ++ inputGateStream count

/-! ## Relabeling the verified input-gate program -/

/-- Finite control for the header prelude followed by the existing gate
streamer. -/
inductive CircuitInputPrefixLabel
  | scanHeader
  | pushHeaderArg
  | pushHeaderEnd
  | restoreInput
  | gate (label : InputGateLabel)
deriving DecidableEq, Fintype

/-- Embed an input-gate instruction into the extended finite control. -/
private def liftInputGateOp :
    Op Unit CircuitSym InputGateLabel →
      Op Unit CircuitSym CircuitInputPrefixLabel
  | .pushOutput symbol cont => .pushOutput symbol (.gate cont)
  | .pushWork₁ symbol cont => .pushWork₁ symbol (.gate cont)
  | .pushWork₂ symbol cont => .pushWork₂ symbol (.gate cont)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.gate nextEmpty) (fun symbol => .gate (nextMoved symbol))
  | .copyInputWorks nextEmpty nextCopied =>
      .copyInputWorks (.gate nextEmpty)
        (fun symbol => .gate (nextCopied symbol))
  | .popInput nextEmpty nextSome =>
      .popInput (.gate nextEmpty) (fun symbol => .gate (nextSome symbol))
  | .popWork₁ nextEmpty nextSome =>
      .popWork₁ (.gate nextEmpty) (fun symbol => .gate (nextSome symbol))
  | .popWork₂ nextEmpty nextSome =>
      .popWork₂ (.gate nextEmpty) (fun symbol => .gate (nextSome symbol))
  | .inc₁ cont => .inc₁ (.gate cont)
  | .inc₂ cont => .inc₂ (.gate cont)
  | .inc₃ cont => .inc₃ (.gate cont)
  | .dec₁ nextZero nextSucc => .dec₁ (.gate nextZero) (.gate nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.gate nextZero) (.gate nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.gate nextZero) (.gate nextSucc)
  | .jump cont => .jump (.gate cont)
  | .halt => .halt

/-- Reversed-prefix program.  The header scan both parks the input and
prepends one unary mark per token.  After the terminator is prepended, the
input is restored and control enters the verified gate streamer. -/
def circuitInputPrefixRevProgram : Program Unit CircuitSym where
  Label := CircuitInputPrefixLabel
  main := .scanHeader
  op
    | .scanHeader =>
        .moveInputWork₁ .pushHeaderEnd (fun _ => .pushHeaderArg)
    | .pushHeaderArg => .pushOutput .argMark .scanHeader
    | .pushHeaderEnd => .pushOutput .endMark .restoreInput
    | .restoreInput =>
        .moveWork₁Input (.gate .next) (fun _ => .restoreInput)
    | .gate label => liftInputGateOp (inputGateRevProgram.op label)

/-- Embed a gate-streamer configuration into the extended program. -/
private def liftInputGateCfg (c : BuilderCfg inputGateRevProgram) :
    BuilderCfg circuitInputPrefixRevProgram where
  label := c.label.map .gate
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

private theorem liftInputGate_stepOp
    (op : Op Unit CircuitSym InputGateLabel)
    (c : BuilderCfg inputGateRevProgram) :
    stepOp (liftInputGateOp op) (liftInputGateCfg c) =
      liftInputGateCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [liftInputGateOp, liftInputGateCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

/-- Every gate-streamer step is simulated exactly after relabeling. -/
private theorem liftInputGate_step (c : BuilderCfg inputGateRevProgram) :
    step circuitInputPrefixRevProgram (liftInputGateCfg c) =
      Option.map liftInputGateCfg (step inputGateRevProgram c) := by
  unfold step
  rw [show (liftInputGateCfg c).label =
      c.label.map CircuitInputPrefixLabel.gate by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      change some
        (stepOp (liftInputGateOp (inputGateRevProgram.op label))
          (liftInputGateCfg c)) =
          some (liftInputGateCfg (stepOp (inputGateRevProgram.op label) c))
      exact congrArg some (liftInputGate_stepOp (inputGateRevProgram.op label) c)

/-! ## Exact header prelude -/

private def circuitInputPrefixCfg (label : CircuitInputPrefixLabel)
    (buffer : Option Unit) (input : List Unit) (output : List CircuitSym)
    (work₁ : List Unit) : BuilderCfg circuitInputPrefixRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- Scan the full clock, parking it while accumulating the reversed unary
header without losing any input token. -/
private theorem circuitInputPrefix_scan_eval (buffer : Option Unit)
    (input : List Unit) (output : List CircuitSym) (parked : List Unit) :
    (flip Option.bind (step circuitInputPrefixRevProgram))^[
        2 * input.length + 1]
      (some (circuitInputPrefixCfg .scanHeader buffer input output parked)) =
      some (circuitInputPrefixCfg .pushHeaderEnd none []
        (List.replicate input.length .argMark ++ output)
        (input.reverse ++ parked)) := by
  induction input generalizing buffer output parked with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol
      rw [show 2 * (Unit.unit :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step circuitInputPrefixRevProgram))^[
            2 * rest.length + 1]
          (some (circuitInputPrefixCfg .scanHeader (some ()) rest
            (.argMark :: output) (() :: parked))) = _
      simpa only [List.length_cons, List.replicate_succ,
        replicate_append_cons, List.reverse_cons, List.cons_append,
        List.append_assoc, List.nil_append] using
        ih (some ()) (.argMark :: output) (() :: parked)

/-- Restore a parked clock in its original order and enter the gate
streamer. -/
private theorem circuitInputPrefix_restore_eval (buffer : Option Unit)
    (work₁ input : List Unit) (output : List CircuitSym) :
    (flip Option.bind (step circuitInputPrefixRevProgram))^[work₁.length + 1]
      (some (circuitInputPrefixCfg .restoreInput buffer input output work₁)) =
      some (circuitInputPrefixCfg (.gate .next) none
        (work₁.reverse ++ input) output []) := by
  induction work₁ generalizing buffer input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol
      rw [show (Unit.unit :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step circuitInputPrefixRevProgram))^[
            rest.length + 1]
          (some (circuitInputPrefixCfg .restoreInput (some ())
            (() :: input) output rest)) = _
      simpa only [List.reverse_cons, List.singleton_append,
        List.append_assoc] using ih (some ()) (() :: input)

/-- Exact prelude run from the ordinary initial configuration to the lifted
input-gate start configuration. -/
private def circuitInputPrefix_prelude (input : List Unit) :
    EvalsToInTime (step circuitInputPrefixRevProgram)
      (initialCfg circuitInputPrefixRevProgram input)
      (some (liftInputGateCfg
        { initialCfg inputGateRevProgram input with
            output := (encNat input.length).reverse }))
      (3 * input.length + 3) := by
  let afterScan := circuitInputPrefixCfg .pushHeaderEnd none []
    (List.replicate input.length .argMark) input.reverse
  let afterEnd := circuitInputPrefixCfg .restoreInput none []
    (.endMark :: List.replicate input.length .argMark) input.reverse
  let gateStart := circuitInputPrefixCfg (.gate .next) none input
    (.endMark :: List.replicate input.length .argMark) []
  have hscan : EvalsToInTime (step circuitInputPrefixRevProgram)
      (initialCfg circuitInputPrefixRevProgram input)
      (some afterScan) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [initialCfg, circuitInputPrefixCfg,
      circuitInputPrefixRevProgram, afterScan] using
      circuitInputPrefix_scan_eval none input [] []
  have hend : EvalsToInTime (step circuitInputPrefixRevProgram)
      afterScan (some afterEnd) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step circuitInputPrefixRevProgram)
      afterEnd (some gateStart) (input.length + 1) := by
    refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
    simpa [afterEnd, gateStart] using
      circuitInputPrefix_restore_eval none input.reverse []
        (.endMark :: List.replicate input.length .argMark)
  let throughEnd := EvalsToInTime.trans (step circuitInputPrefixRevProgram)
    (2 * input.length + 1) 1 _ afterScan _ hscan hend
  let full := EvalsToInTime.trans (step circuitInputPrefixRevProgram)
    (1 + (2 * input.length + 1)) (input.length + 1)
    _ afterEnd _ throughEnd hrestore
  have hbound : input.length + 1 + (1 + (2 * input.length + 1)) =
      3 * input.length + 3 := by omega
  rw [← hbound]
  simpa [gateStart, circuitInputPrefixCfg, liftInputGateCfg, initialCfg,
    inputGateRevProgram, encNat] using full

/-! ## Complete reversed and forward machines -/

/-- Exact step count of the combined reversed-prefix builder. -/
def circuitInputPrefixRevSteps (input : List Unit) : Nat :=
  inputGateRevSteps input + (3 * input.length + 3)

/-- Exact concrete run producing the reversed complete prefix. -/
def circuitInputPrefixRev_run (input : List Unit) :
    EvalsToInTime (step circuitInputPrefixRevProgram)
      (initialCfg circuitInputPrefixRevProgram input)
      (some (haltCfg circuitInputPrefixRevProgram
        (circuitInputPrefix input.length).reverse))
      (circuitInputPrefixRevSteps input) := by
  let suffix := (encNat input.length).reverse
  let gateRun := inputGateRev_runWithSuffix input suffix
  have hstop : step inputGateRevProgram
      (haltCfg inputGateRevProgram
        ((inputGateStream input.length).reverse ++ suffix)) = none := by
    rfl
  have lifted : EvalsToInTime (step circuitInputPrefixRevProgram)
      (liftInputGateCfg
        { initialCfg inputGateRevProgram input with output := suffix })
      (some (liftInputGateCfg
        (haltCfg inputGateRevProgram
          ((inputGateStream input.length).reverse ++ suffix))))
      (inputGateRevSteps input) :=
    _root_.Turing.TM2Comp.evalsToInTime_lift liftInputGateCfg gateRun hstop
      (fun c _ => liftInputGate_step c)
  let full := EvalsToInTime.trans (step circuitInputPrefixRevProgram)
    (3 * input.length + 3) (inputGateRevSteps input)
    _
    (liftInputGateCfg
      { initialCfg inputGateRevProgram input with output := suffix })
    _ (circuitInputPrefix_prelude input) lifted
  have hhaltLift : liftInputGateCfg
      (haltCfg inputGateRevProgram
        ((inputGateStream input.length).reverse ++ suffix)) =
      haltCfg circuitInputPrefixRevProgram
        ((inputGateStream input.length).reverse ++ suffix) := by
    rfl
  rw [hhaltLift] at full
  simpa [circuitInputPrefixRevSteps, circuitInputPrefix, suffix,
    List.reverse_append] using full

/-- Exact reversed-prefix builder output contract. -/
theorem circuitInputPrefixRev_builderOutputs :
    BuilderOutputs circuitInputPrefixRevProgram
      (fun input => (circuitInputPrefix input.length).reverse)
      circuitInputPrefixRevSteps := by
  intro input
  exact ⟨circuitInputPrefixRev_run input⟩

/-- Exact reversed-prefix compiled TM2 output contract. -/
theorem circuitInputPrefixRev_outputs :
    Outputs circuitInputPrefixRevProgram
      (fun input => (circuitInputPrefix input.length).reverse)
      circuitInputPrefixRevSteps :=
  Outputs.of_builder_run circuitInputPrefixRev_builderOutputs

/-- Quadratic runtime envelope for header parking and input-gate
serialization. -/
noncomputable def circuitInputPrefixRev_polyBound :
    PolyBound circuitInputPrefixRevSteps where
  polynomial := 6 * Polynomial.X ^ 2 + 4 * Polynomial.X + 6
  bound input := by
    have hgate := inputGateRev_polyBound.bound input
    change inputGateRevSteps input ≤
      (6 * Polynomial.X ^ 2 + Polynomial.X + 3).eval input.length at hgate
    have hgate' : inputGateRevSteps input ≤
        6 * input.length ^ 2 + input.length + 3 := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
        using hgate
    simp only [circuitInputPrefixRevSteps, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- Concrete polynomial-time machine producing the reversed complete
prefix. -/
noncomputable def circuitInputPrefixRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => (circuitInputPrefix input.length).reverse) :=
  ComputableInPolyTime circuitInputPrefixRevProgram _
    circuitInputPrefixRevSteps circuitInputPrefixRev_outputs
    circuitInputPrefixRev_polyBound

/-- Concrete polynomial-time machine producing the forward arity-and-input-
gate prefix. -/
noncomputable def circuitInputPrefix_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => circuitInputPrefix input.length) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      circuitInputPrefixRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
