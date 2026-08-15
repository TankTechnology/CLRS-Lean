import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Runtime-framed tail-first conjunction serialization

This module first isolates one counter-preserving AND gate.  The surrounding
fixed controller will load an arbitrary reversed wire family from a unary
runtime frame and redirect the clean AND exit back to its loader.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Exact encoding of one conjunction step whose fresh output becomes the
next carry wire. -/
def affineAndGateStream (carry source : Nat) : List CircuitSym :=
  encodeCircuitGate (.and source carry)

/-- Contextual entry with the carry in `seen` and the source in `wire`. -/
def affineAndBodyCfg (carry source : Nat) (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.conjunction .push) none none false [] output [] []
    (List.replicate carry ()) [] (List.replicate source ())

/-- Redirectable exit after the source register has been cleared and the
carry register advanced to the fresh output wire. -/
def affineAndCoreExitCfg (carry : Nat) (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.conjunction .done) none none false [] output [] []
    (List.replicate (carry + 1) ()) [] []

/-- Exact cost of one counter-preserving AND invocation. -/
def affineAndRevCoreSteps (carry source : Nat) : Nat :=
  6 * source + 5 * carry + 11

private theorem affineAndClearWire_eval (source carry : Nat)
    (test : Bool) (output : List CircuitSym) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[source + 1]
      (some (sequentialExactlyOneCfg (.conjunction .clearWire)
        none none test [] output [] [] (List.replicate carry ()) []
        (List.replicate source ()))) =
      some (sequentialExactlyOneCfg (.conjunction .incCarry)
        none none false [] output [] [] (List.replicate carry ()) [] []) := by
  induction source generalizing test with
  | zero => rfl
  | succ source ih =>
      rw [show source + 1 + 1 = (source + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[source + 1]
          (some (sequentialExactlyOneCfg (.conjunction .clearWire)
            none none true [] output [] [] (List.replicate carry ()) []
            (List.replicate source ()))) = _
      simpa [List.replicate_succ] using ih true

/-- The shared counter serializer emits exactly `.and source carry`, retains
the incremented carry, clears the temporary source, and stops at a public
redirect point. -/
def affineAndRev_runToDoneLabel (carry source : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineAndBodyCfg carry source output)
      (some (affineAndCoreExitCfg carry
        ((affineAndGateStream carry source).reverse ++ output)))
      (affineAndRevCoreSteps carry source) := by
  let c₀ := sequentialExactlyOneCfg
    (.encode .wire .conjunctionSource) none none false []
    (.andMark :: output) [] [] (List.replicate carry ()) []
    (List.replicate source ())
  have hpush : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineAndBodyCfg carry source output) (some c₀) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let sourceOutput := (encNat source).reverse ++ .andMark :: output
  let c₁ := sequentialExactlyOneCfg (.resume .conjunctionSource)
    none none false [] sourceOutput [] [] (List.replicate carry ()) []
    (List.replicate source ())
  have hsource : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * source + 3) := by
    simpa [c₀, c₁, sourceOutput] using
      encodeWire_run source .conjunctionSource none false []
        (.andMark :: output) [] (List.replicate carry ()) []
  let c₂ := sequentialExactlyOneCfg (.encode .seen .conjunctionCarry)
    none none false [] sourceOutput [] [] (List.replicate carry ()) []
    (List.replicate source ())
  have hjumpCarry : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let gateOutput := (encodeCircuitGate (.and source carry)).reverse ++ output
  let c₃ := sequentialExactlyOneCfg (.resume .conjunctionCarry)
    none none false [] gateOutput [] [] (List.replicate carry ()) []
    (List.replicate source ())
  have hcarry : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) (5 * carry + 3) := by
    simpa [c₂, c₃, sourceOutput, gateOutput, encodeCircuitGate,
      List.reverse_append, List.append_assoc] using
      encodeSeen_run carry .conjunctionCarry none false [] sourceOutput [] []
        (List.replicate source ())
  let beforeClear := sequentialExactlyOneCfg (.conjunction .clearWire)
    none none false [] gateOutput [] [] (List.replicate carry ()) []
    (List.replicate source ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeInc := sequentialExactlyOneCfg (.conjunction .incCarry)
    none none false [] gateOutput [] [] (List.replicate carry ()) [] []
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some beforeInc) (source + 1) := by
    refine ⟨⟨source + 1, ?_⟩, le_rfl⟩
    simpa [beforeClear, beforeInc] using
      affineAndClearWire_eval source carry false gateOutput
  have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeInc (some (affineAndCoreExitCfg carry gateOutput)) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram beforeInc =
      some (affineAndCoreExitCfg carry gateOutput)
    unfold beforeInc affineAndCoreExitCfg
    rw [show carry + 1 = Nat.succ carry by omega, List.replicate_succ]
    rfl
  let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * source + 3) _ c₀ _ hpush hsource
  let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁ _ t₁ hjumpCarry
  let t₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * carry + 3) _ c₂ _ t₂ hcarry
  let t₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₃ _ t₃ hjumpClear
  let t₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (source + 1) _ beforeClear _ t₄ hclear
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ beforeInc _ t₅ hinc
  convert full using 1
  · simp [affineAndGateStream, gateOutput]
  · simp [affineAndRevCoreSteps]
    omega

/-- Runtime data for one tail-first conjunction fold. -/
structure AffineConjunctionFrame where
  start : Nat
  wires : List Nat
deriving DecidableEq, Repr

/-- Unary blocks in the order consumed by the controller. -/
def encodeAffineConjunctionSources (sources : List Nat) :
    List UnaryFrameSym :=
  sources.flatMap encodeUnaryFrameBlock

/-- The semantic conjunction is tail-first, so the runtime source order is
the reverse of the public source-wire order. -/
def encodeAffineConjunctionFrame (frame : AffineConjunctionFrame) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock frame.start ++
    encodeAffineConjunctionSources frame.wires.reverse ++ [.frameEnd]

@[simp] theorem encodeAffineConjunctionSources_length (sources : List Nat) :
    (encodeAffineConjunctionSources sources).length =
      (sources.map fun source => source + 1).sum := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp [encodeAffineConjunctionSources, encodeUnaryFrameBlock]
      omega

/-- Exact runtime-frame size, including the start separator and final
`frameEnd`. -/
@[simp] theorem encodeAffineConjunctionFrame_length
    (frame : AffineConjunctionFrame) :
    (encodeAffineConjunctionFrame frame).length =
      frame.start + 2 + (frame.wires.map fun wire => wire + 1).sum := by
  simp [encodeAffineConjunctionFrame, encodeUnaryFrameBlock]
  omega

namespace AffineConjunction

/-- AND gates in the exact order produced after the true seed. -/
def chunksFrom : Nat → List Nat → List CircuitGate
  | _, [] => []
  | carry, source :: rest =>
      .and source carry :: chunksFrom (carry + 1) rest

theorem chunksFrom_append (carry : Nat) (left right : List Nat) :
    chunksFrom carry (left ++ right) =
      chunksFrom carry left ++ chunksFrom (carry + left.length) right := by
  induction left generalizing carry with
  | nil => simp [chunksFrom]
  | cons source rest ih =>
      simp only [List.cons_append, chunksFrom, List.length_cons]
      rw [ih]
      have hcarry : carry + 1 + rest.length =
          carry + (rest.length + 1) := by omega
      rw [hcarry]

end AffineConjunction

/-- Exact forward byte stream of one tail-first conjunction. -/
def affineConjunctionGateStream (frame : AffineConjunctionFrame) :
    List CircuitSym :=
  ([CircuitGate.const true] ++
    AffineConjunction.chunksFrom frame.start frame.wires.reverse).flatMap
      encodeCircuitGate

private theorem conjunctionGateTrace_wire (start : Nat) (wires : List Nat) :
    (CircuitBuilder.conjunctionGateTrace start wires).wire =
      start + wires.length := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp only [CircuitBuilder.conjunctionGateTrace]
      rw [CircuitBuilder.conjunctionGateTrace_length]
      simp only [List.length_cons]

private theorem conjunctionGateTrace_gates (start : Nat) (wires : List Nat) :
    (CircuitBuilder.conjunctionGateTrace start wires).gates =
      [CircuitGate.const true] ++
        AffineConjunction.chunksFrom start wires.reverse := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp only [CircuitBuilder.conjunctionGateTrace, List.reverse_cons]
      rw [ih, AffineConjunction.chunksFrom_append,
        conjunctionGateTrace_wire]
      simp [AffineConjunction.chunksFrom]

/-- The runtime stream is byte-for-byte the established semantic conjunction
trace. -/
theorem affineConjunctionGateStream_eq_trace
    (frame : AffineConjunctionFrame) :
    affineConjunctionGateStream frame =
      (CircuitBuilder.conjunctionGateTrace
        frame.start frame.wires).gates.flatMap encodeCircuitGate := by
  rw [conjunctionGateTrace_gates]
  rfl

/-- Fixed finite phases of the runtime-frame loader. -/
inductive AffineConjunctionLoadLabel
  | loadStart | incStart | clearStartBuffer | seed
  | loadWire | incWire | clearWireBuffer | clearCarry
deriving DecidableEq, Fintype

/-- Grouped control keeps the shared numeral encoder below one constructor. -/
inductive AffineConjunctionLabel
  | load (phase : AffineConjunctionLoadLabel)
  | core (label : SequentialExactlyOneLabel)
  | finish | invalid
deriving DecidableEq, Fintype

private def liftAndKernelOp :
    Op Unit CircuitSym SequentialExactlyOneLabel →
      Op UnaryFrameSym CircuitSym AffineConjunctionLabel
  | .pushOutput symbol next => .pushOutput symbol (.core next)
  | .pushWork₁ _ next => .pushWork₁ .tick (.core next)
  | .pushWork₂ _ next => .pushWork₂ .tick (.core next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.core nextEmpty) (fun _ => .core (nextMoved ()))
  | .copyInputWorks nextEmpty nextCopied =>
      .copyInputWorks (.core nextEmpty) (fun _ => .core (nextCopied ()))
  | .popInput nextEmpty nextSome =>
      .popInput (.core nextEmpty) (fun _ => .core (nextSome ()))
  | .popWork₁ nextEmpty nextSome =>
      .popWork₁ (.core nextEmpty) (fun _ => .core (nextSome ()))
  | .popWork₂ nextEmpty nextSome =>
      .popWork₂ (.core nextEmpty) (fun _ => .core (nextSome ()))
  | .inc₁ next => .inc₁ (.core next)
  | .inc₂ next => .inc₂ (.core next)
  | .inc₃ next => .inc₃ (.core next)
  | .dec₁ nextZero nextSucc => .dec₁ (.core nextZero) (.core nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.core nextZero) (.core nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.core nextZero) (.core nextSucc)
  | .jump next => .jump (.core next)
  | .halt => .halt

/-- One fixed controller for every start wire and finite source-wire list. -/
def affineConjunctionRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineConjunctionLabel
  main := .load .loadStart
  op
    | .load .loadStart => .popInput .invalid fun
        | .tick => .load .incStart
        | .separator => .load .clearStartBuffer
        | .frameEnd => .invalid
    | .load .incStart => .inc₁ (.load .loadStart)
    | .load .clearStartBuffer =>
        .popWork₁ (.load .seed) (fun _ => .invalid)
    | .load .seed => .pushOutput .constTrueMark (.load .loadWire)
    | .load .loadWire => .popInput .invalid fun
        | .tick => .load .incWire
        | .separator => .load .clearWireBuffer
        | .frameEnd => .load .clearCarry
    | .load .incWire => .inc₃ (.load .loadWire)
    | .load .clearWireBuffer =>
        .popWork₁ (.core (.conjunction .push)) (fun _ => .invalid)
    | .load .clearCarry =>
        .dec₁ .finish (.load .clearCarry)
    | .core (.conjunction .done) => .jump (.load .loadWire)
    | .core label => liftAndKernelOp (sequentialExactlyOneRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the conjunction controller. -/
def affineConjunctionCfg (label : AffineConjunctionLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (carry next source : List Unit) : BuilderCfg affineConjunctionRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := carry
  counter₂ := next
  counter₃ := source

/-- Clean entry configuration for one complete conjunction frame. -/
def affineConjunctionLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineConjunctionRevProgram :=
  affineConjunctionCfg (.load .loadStart) none none false input output
    [] [] [] [] []

private def affineConjunctionWireLoopCfg (carry : Nat)
    (input : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineConjunctionRevProgram :=
  affineConjunctionCfg (.load .loadWire) none none false input output
    [] [] (List.replicate carry ()) [] []

/-- Redirectable clean exit after `frameEnd` and accumulator cleanup. -/
def affineConjunctionFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineConjunctionRevProgram :=
  affineConjunctionCfg .finish (some .frameEnd) none false tail output
    [] [] [] [] []

private def liftAndKernelCfg (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram) :
    BuilderCfg affineConjunctionRevProgram where
  label := c.label.map .core
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

private def isAffineAndCont : SequentialExactlyOneCont → Prop
  | .conjunctionSource | .conjunctionCarry => True
  | _ => False

private def isAffineAndKernelLabel : SequentialExactlyOneLabel → Prop
  | .encode _ cont | .save _ cont | .pushArg _ cont | .pushEnd _ cont
  | .restore _ cont | .restoreInc _ cont | .resume cont => isAffineAndCont cont
  | .conjunction _ => True
  | _ => False

private def isAffineAndKernelCfg
    (c : BuilderCfg sequentialExactlyOneRevProgram) : Prop :=
  match c.label with
  | none => False
  | some label => isAffineAndKernelLabel label

private def preservesAndTail :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .moveInputWork₁ .. | .moveWork₁Input ..
  | .moveInputWork₂ .. | .moveWork₂Input ..
  | .copyInputWorks .. | .popInput .. => False
  | _ => True

private theorem liftAndKernel_stepOp (tail : List UnaryFrameSym)
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hsafe : preservesAndTail op) :
    stepOp (liftAndKernelOp op) (liftAndKernelCfg tail c) =
      liftAndKernelCfg tail (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => rfl
  | pushWork₁ => rfl
  | pushWork₂ => rfl
  | moveInputWork₁ => simp [preservesAndTail] at hsafe
  | moveWork₁Input => simp [preservesAndTail] at hsafe
  | moveInputWork₂ => simp [preservesAndTail] at hsafe
  | moveWork₂Input => simp [preservesAndTail] at hsafe
  | moveWork₁Work₂ => cases work₁ <;> rfl
  | moveWork₂Work₁ => cases work₂ <;> rfl
  | copyInputWorks => simp [preservesAndTail] at hsafe
  | popInput => simp [preservesAndTail] at hsafe
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

private theorem affineAndKernel_op_preservesTail
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineAndKernelLabel label) :
    preservesAndTail (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont => cases register <;> trivial
  | restoreInc register cont => cases register <;> trivial
  | resume cont =>
      cases cont <;> simp_all [isAffineAndKernelLabel, isAffineAndCont,
        preservesAndTail, sequentialExactlyOneRevProgram]
  | conjunction phase => cases phase <;> trivial
  | _ =>
      simp_all [isAffineAndKernelLabel, isAffineAndCont, preservesAndTail,
        sequentialExactlyOneRevProgram]

private theorem affineConjunction_op_core
    (label : SequentialExactlyOneLabel)
    (hlabel : label ≠ .conjunction .done) :
    affineConjunctionRevProgram.op (.core label) =
      liftAndKernelOp (sequentialExactlyOneRevProgram.op label) := by
  cases label <;> simp_all [affineConjunctionRevProgram]

private theorem liftAndKernel_step (tail : List UnaryFrameSym)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineAndKernelCfg c)
    (hexit : c.label ≠ some (.conjunction .done)) :
    step affineConjunctionRevProgram (liftAndKernelCfg tail c) =
      Option.map (liftAndKernelCfg tail)
        (step sequentialExactlyOneRevProgram c) := by
  unfold step
  rw [show (liftAndKernelCfg tail c).label = c.label.map .core by rfl]
  cases hlabel : c.label with
  | none => simp [isAffineAndKernelCfg, hlabel] at hkernel
  | some label =>
      have hlabelKernel : isAffineAndKernelLabel label := by
        simpa [isAffineAndKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .conjunction .done := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineConjunction_op_core label hlabelExit]
      exact congrArg some (liftAndKernel_stepOp tail
        (sequentialExactlyOneRevProgram.op label) c
        (affineAndKernel_op_preservesTail label hlabelKernel))

private def staysInAffineAndKernel :
    Op Unit CircuitSym SequentialExactlyOneLabel → Prop
  | .pushOutput _ next | .pushWork₁ _ next | .pushWork₂ _ next
  | .inc₁ next | .inc₂ next | .inc₃ next | .jump next =>
      isAffineAndKernelLabel next
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
      isAffineAndKernelLabel nextEmpty ∧
        ∀ symbol, isAffineAndKernelLabel (nextMoved symbol)
  | .dec₁ nextZero nextSucc | .dec₂ nextZero nextSucc
  | .dec₃ nextZero nextSucc =>
      isAffineAndKernelLabel nextZero ∧
        isAffineAndKernelLabel nextSucc
  | .halt => False

private theorem stepOp_staysInAffineAndKernel
    (op : Op Unit CircuitSym SequentialExactlyOneLabel)
    (c : BuilderCfg sequentialExactlyOneRevProgram)
    (hop : staysInAffineAndKernel op) :
    isAffineAndKernelCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op with
  | pushOutput => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | pushWork₁ => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | pushWork₂ => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | moveInputWork₁ => cases input <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | moveWork₁Input => cases work₁ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | moveInputWork₂ => cases input <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | moveWork₂Input => cases work₂ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | moveWork₁Work₂ => cases work₁ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | moveWork₂Work₁ => cases work₂ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | copyInputWorks => cases input <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | popInput => cases input <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | popWork₁ => cases work₁ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | popWork₂ => cases work₂ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | inc₁ => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | inc₂ => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | inc₃ => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | dec₁ => cases counter₁ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | dec₂ => cases counter₂ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | dec₃ => cases counter₃ <;> simp_all [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp]
  | jump => simpa [staysInAffineAndKernel,
      isAffineAndKernelCfg, stepOp] using hop
  | halt => simp [staysInAffineAndKernel] at hop

private theorem affineAndKernel_op_stays
    (label : SequentialExactlyOneLabel)
    (hkernel : isAffineAndKernelLabel label)
    (hexit : label ≠ .conjunction .done) :
    staysInAffineAndKernel (sequentialExactlyOneRevProgram.op label) := by
  cases label with
  | encode register cont =>
      cases register <;> exact ⟨hkernel, hkernel⟩
  | save register cont => exact hkernel
  | pushArg register cont => exact hkernel
  | pushEnd register cont => exact hkernel
  | restore register cont => exact ⟨hkernel, fun _ => hkernel⟩
  | restoreInc register cont => cases register <;> exact hkernel
  | resume cont =>
      cases cont <;> simp_all [isAffineAndKernelLabel, isAffineAndCont,
        staysInAffineAndKernel, sequentialExactlyOneRevProgram]
  | conjunction phase =>
      cases phase <;> simp_all [staysInAffineAndKernel,
        sequentialExactlyOneRevProgram, isAffineAndKernelLabel,
        isAffineAndCont]
  | _ => simp [isAffineAndKernelLabel] at hkernel

private theorem affineAndKernel_step_closed
    (c c' : BuilderCfg sequentialExactlyOneRevProgram)
    (hkernel : isAffineAndKernelCfg c)
    (hexit : c.label ≠ some (.conjunction .done))
    (hstep : step sequentialExactlyOneRevProgram c = some c') :
    isAffineAndKernelCfg c' := by
  unfold step at hstep
  cases hlabel : c.label with
  | none => simp [hlabel] at hstep
  | some label =>
      have hlabelKernel : isAffineAndKernelLabel label := by
        simpa [isAffineAndKernelCfg, hlabel] using hkernel
      have hlabelExit : label ≠ .conjunction .done := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      rw [hlabel] at hstep
      injection hstep with hc'
      subst c'
      exact stepOp_staysInAffineAndKernel
        (sequentialExactlyOneRevProgram.op label) c
        (affineAndKernel_op_stays label hlabelKernel hlabelExit)

private theorem conjunction_iterate_bind_none { σ : Type }
    (f : σ → Option σ) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem affineAnd_done_no_return
    (c target : BuilderCfg sequentialExactlyOneRevProgram)
    (hc : c.label = some (.conjunction .done))
    (htarget : target.label = some (.conjunction .done)) : ∀ n : Nat,
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
      { label := some (SequentialExactlyOneLabel.conjunction
          SequentialConjunctionLabel.done)
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
      rw [hnone, conjunction_iterate_bind_none]
      simp

private theorem liftAndKernel_iterations_to_done (tail : List UnaryFrameSym)
    {a b : BuilderCfg sequentialExactlyOneRevProgram}
    (ha : isAffineAndKernelCfg a)
    (hb : b.label = some (.conjunction .done)) : ∀ n : Nat,
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineConjunctionRevProgram))^[n]
        (some (liftAndKernelCfg tail a)) =
          some (liftAndKernelCfg tail b) := by
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
        (flip Option.bind (step affineConjunctionRevProgram))^[n]
          (step affineConjunctionRevProgram (liftAndKernelCfg tail a)) =
            some (liftAndKernelCfg tail b)
      have haexit : a.label ≠ some (.conjunction .done) := by
        intro haDone
        exact affineAnd_done_no_return a b haDone hb n h
      cases hstep : step sequentialExactlyOneRevProgram a with
      | none =>
          rw [hstep, conjunction_iterate_bind_none] at h
          contradiction
      | some c =>
          have hc := affineAndKernel_step_closed a c ha haexit hstep
          have hsim := liftAndKernel_step tail a ha haexit
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih hc h

private def affineConjunctionCoreExitCfg (carry : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    BuilderCfg affineConjunctionRevProgram :=
  affineConjunctionCfg (.core (.conjunction .done)) none none false tail output
    [] [] (List.replicate (carry + 1) ()) [] []

private def affineConjunctionAndCore_run (carry source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionCfg (.core (.conjunction .push)) none none false
        tail output [] [] (List.replicate carry ()) []
        (List.replicate source ()))
      (some (affineConjunctionCoreExitCfg carry tail
        ((affineAndGateStream carry source).reverse ++ output)))
      (affineAndRevCoreSteps carry source) := by
  have sourceRun := affineAndRev_runToDoneLabel carry source output
  have hsource : isAffineAndKernelCfg (affineAndBodyCfg carry source output) :=
    by simp [affineAndBodyCfg, sequentialExactlyOneCfg,
      isAffineAndKernelCfg, isAffineAndKernelLabel]
  have htarget : (affineAndCoreExitCfg carry
      ((affineAndGateStream carry source).reverse ++ output)).label =
        some (.conjunction .done) := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have lifted := liftAndKernel_iterations_to_done tail hsource htarget
    sourceRun.steps sourceRun.evals_in_steps
  exact lifted

private theorem conjunction_replicate_append_cons (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem conjunctionLoadStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (tail : List UnaryFrameSym)
    (output : List CircuitSym) (carry : List Unit) :
    (flip Option.bind (step affineConjunctionRevProgram))^[2 * value + 1]
      (some (affineConjunctionCfg (.load .loadStart) buffer₁ none false
        (encodeUnaryFrameBlock value ++ tail) output [] [] carry [] [])) =
      some (affineConjunctionCfg (.load .clearStartBuffer)
        (some .separator) none false tail output [] []
        (List.replicate value () ++ carry) [] []) := by
  induction value generalizing buffer₁ carry with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineConjunctionRevProgram))^[2 * value + 1]
          (some (affineConjunctionCfg (.load .loadStart) (some .tick)
            none false (encodeUnaryFrameBlock value ++ tail) output [] []
            (() :: carry) [] [])) = _
      simpa only [List.replicate_succ, conjunction_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: carry)

/-- Exact cost of loading the start index and seeding the conjunction. -/
def affineConjunctionStartSteps (start : Nat) : Nat :=
  2 * start + 3

private def affineConjunctionStart_load (start : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg (encodeUnaryFrameBlock start ++ tail) output)
      (some (affineConjunctionWireLoopCfg start tail
        (.constTrueMark :: output)))
      (affineConjunctionStartSteps start) := by
  let afterLoad := affineConjunctionCfg (.load .clearStartBuffer)
    (some .separator) none false tail output [] []
    (List.replicate start ()) [] []
  let beforeSeed := affineConjunctionCfg (.load .seed) none none false
    tail output [] [] (List.replicate start ()) [] []
  have hload : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg (encodeUnaryFrameBlock start ++ tail) output)
      (some afterLoad) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [afterLoad, affineConjunctionLoopCfg] using
      conjunctionLoadStart_eval start none tail output []
  have hclear : EvalsToInTime (step affineConjunctionRevProgram)
      afterLoad (some beforeSeed) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hseed : EvalsToInTime (step affineConjunctionRevProgram)
      beforeSeed
      (some (affineConjunctionWireLoopCfg start tail
        (.constTrueMark :: output))) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let throughClear := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (2 * start + 1) 1 _ afterLoad _ hload hclear
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (1 + (2 * start + 1)) 1 _ beforeSeed _ throughClear hseed
  convert full using 1
  simp [affineConjunctionStartSteps]
  omega

private theorem conjunctionLoadWire_eval (value carry : Nat)
    (buffer₁ : Option UnaryFrameSym) (tail : List UnaryFrameSym)
    (output : List CircuitSym) (source : List Unit) :
    (flip Option.bind (step affineConjunctionRevProgram))^[2 * value + 1]
      (some (affineConjunctionCfg (.load .loadWire) buffer₁ none false
        (encodeUnaryFrameBlock value ++ tail) output [] []
        (List.replicate carry ()) [] source)) =
      some (affineConjunctionCfg (.load .clearWireBuffer)
        (some .separator) none false tail output [] []
        (List.replicate carry ()) []
        (List.replicate value () ++ source)) := by
  induction value generalizing buffer₁ source with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineConjunctionRevProgram))^[2 * value + 1]
          (some (affineConjunctionCfg (.load .loadWire) (some .tick)
            none false (encodeUnaryFrameBlock value ++ tail) output [] []
            (List.replicate carry ()) [] (() :: source))) = _
      simpa only [List.replicate_succ, conjunction_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: source)

/-- Exact cost of loading one source wire and clearing the separator buffer. -/
def affineConjunctionWireLoadSteps (source : Nat) : Nat :=
  2 * source + 2

private def affineConjunctionWire_load (carry source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry
        (encodeUnaryFrameBlock source ++ tail) output)
      (some (affineConjunctionCfg (.core (.conjunction .push))
        none none false tail output [] [] (List.replicate carry ()) []
        (List.replicate source ())))
      (affineConjunctionWireLoadSteps source) := by
  let afterLoad := affineConjunctionCfg (.load .clearWireBuffer)
    (some .separator) none false tail output [] []
    (List.replicate carry ()) [] (List.replicate source ())
  have hload : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry
        (encodeUnaryFrameBlock source ++ tail) output)
      (some afterLoad) (2 * source + 1) := by
    refine ⟨⟨2 * source + 1, ?_⟩, le_rfl⟩
    simpa [afterLoad, affineConjunctionWireLoopCfg] using
      conjunctionLoadWire_eval source carry none tail output []
  have hclear : EvalsToInTime (step affineConjunctionRevProgram)
      afterLoad
      (some (affineConjunctionCfg (.core (.conjunction .push))
        none none false tail output [] [] (List.replicate carry ()) []
        (List.replicate source ()))) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (2 * source + 1) 1 _ afterLoad _ hload hclear
  convert full using 1
  simp [affineConjunctionWireLoadSteps]
  omega

/-- Exact cost of loading and serializing one source wire, including the
redirect back to the runtime loader. -/
def affineConjunctionWireSteps (carry source : Nat) : Nat :=
  affineConjunctionWireLoadSteps source +
    affineAndRevCoreSteps carry source + 1

private def affineConjunctionWire_run (carry source : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry
        (encodeUnaryFrameBlock source ++ tail) output)
      (some (affineConjunctionWireLoopCfg (carry + 1) tail
        ((affineAndGateStream carry source).reverse ++ output)))
      (affineConjunctionWireSteps carry source) := by
  let gateOutput := (affineAndGateStream carry source).reverse ++ output
  let coreEntry := affineConjunctionCfg (.core (.conjunction .push))
    none none false tail output [] [] (List.replicate carry ()) []
    (List.replicate source ())
  let coreExit := affineConjunctionCoreExitCfg carry tail gateOutput
  have hload : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry
        (encodeUnaryFrameBlock source ++ tail) output)
      (some coreEntry) (affineConjunctionWireLoadSteps source) := by
    simpa [coreEntry] using
      affineConjunctionWire_load carry source tail output
  have hcore : EvalsToInTime (step affineConjunctionRevProgram)
      coreEntry (some coreExit) (affineAndRevCoreSteps carry source) := by
    simpa [coreEntry, coreExit, gateOutput] using
      affineConjunctionAndCore_run carry source tail output
  have hredirect : EvalsToInTime (step affineConjunctionRevProgram)
      coreExit
      (some (affineConjunctionWireLoopCfg (carry + 1) tail gateOutput))
      1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let throughCore := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (affineConjunctionWireLoadSteps source)
    (affineAndRevCoreSteps carry source) _ coreEntry _ hload hcore
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (affineAndRevCoreSteps carry source +
      affineConjunctionWireLoadSteps source) 1
    _ coreExit _ throughCore hredirect
  convert full using 1
  simp [affineConjunctionWireSteps, gateOutput]
  omega

private theorem conjunctionClearCarry_eval (carry : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    (flip Option.bind (step affineConjunctionRevProgram))^[carry + 1]
      (some (affineConjunctionCfg (.load .clearCarry)
        (some .frameEnd) none false tail output [] []
        (List.replicate carry ()) [] [])) =
      some (affineConjunctionFinishCfg tail output) := by
  induction carry with
  | zero => rfl
  | succ carry ih =>
      rw [show carry + 1 + 1 = (carry + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineConjunctionRevProgram))^[carry + 1]
          (some (affineConjunctionCfg (.load .clearCarry)
            (some .frameEnd) none false tail output [] []
            (List.replicate carry ()) [] [])) = _
      exact ih

/-- Exact empty-source tail cost: consume `frameEnd`, clear the carry, and
enter the redirectable finish label. -/
def affineConjunctionFinishSteps (carry : Nat) : Nat :=
  carry + 2

private def affineConjunctionFinish_run (carry : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry (.frameEnd :: tail) output)
      (some (affineConjunctionFinishCfg tail output))
      (affineConjunctionFinishSteps carry) := by
  let beforeClear := affineConjunctionCfg (.load .clearCarry)
    (some .frameEnd) none false tail output [] []
    (List.replicate carry ()) [] []
  have hframeEnd : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry (.frameEnd :: tail) output)
      (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step affineConjunctionRevProgram)
      beforeClear (some (affineConjunctionFinishCfg tail output))
      (carry + 1) := by
    refine ⟨⟨carry + 1, ?_⟩, le_rfl⟩
    simpa [beforeClear] using conjunctionClearCarry_eval carry tail output
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    1 (carry + 1) _ beforeClear _ hframeEnd hclear
  convert full using 1
  simp [affineConjunctionFinishSteps]

/-- Exact recursive cost from the source loader through the clean finish
label. -/
def affineConjunctionFoldSteps : Nat → List Nat → Nat
  | carry, [] => affineConjunctionFinishSteps carry
  | carry, source :: rest =>
      affineConjunctionWireSteps carry source +
        affineConjunctionFoldSteps (carry + 1) rest

private def affineConjunctionSources_runToFinish
    (sources : List Nat) (carry : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg carry
        (encodeAffineConjunctionSources sources ++ .frameEnd :: tail) output)
      (some (affineConjunctionFinishCfg tail
        (((AffineConjunction.chunksFrom carry sources).flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineConjunctionFoldSteps carry sources) := by
  induction sources generalizing carry output with
  | nil =>
      simpa [encodeAffineConjunctionSources, AffineConjunction.chunksFrom,
        affineConjunctionFoldSteps] using
        affineConjunctionFinish_run carry tail output
  | cons source rest ih =>
      let restInput := encodeAffineConjunctionSources rest ++ .frameEnd :: tail
      let gateOutput := (affineAndGateStream carry source).reverse ++ output
      have hwire : EvalsToInTime (step affineConjunctionRevProgram)
          (affineConjunctionWireLoopCfg carry
            (encodeUnaryFrameBlock source ++ restInput) output)
          (some (affineConjunctionWireLoopCfg (carry + 1)
            restInput gateOutput))
          (affineConjunctionWireSteps carry source) := by
        simpa [restInput, gateOutput] using
          affineConjunctionWire_run carry source restInput output
      have hrest : EvalsToInTime (step affineConjunctionRevProgram)
          (affineConjunctionWireLoopCfg (carry + 1) restInput gateOutput)
          (some (affineConjunctionFinishCfg tail
            (((AffineConjunction.chunksFrom (carry + 1) rest).flatMap
              encodeCircuitGate).reverse ++ gateOutput)))
          (affineConjunctionFoldSteps (carry + 1) rest) := by
        simpa [restInput, gateOutput] using ih (carry + 1) gateOutput
      let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
        (affineConjunctionWireSteps carry source)
        (affineConjunctionFoldSteps (carry + 1) rest)
        _ (affineConjunctionWireLoopCfg (carry + 1) restInput gateOutput) _
        hwire hrest
      convert full using 1
      · simp [encodeAffineConjunctionSources, restInput]
      · simp [AffineConjunction.chunksFrom, affineAndGateStream, gateOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineConjunctionFoldSteps]
        omega

/-- Exact contextual runtime through the redirectable finish label. -/
def affineConjunctionUntilFinishSteps
    (frame : AffineConjunctionFrame) : Nat :=
  affineConjunctionStartSteps frame.start +
    affineConjunctionFoldSteps frame.start frame.wires.reverse

/-- Standalone runtime, including the final halt instruction. -/
def affineConjunctionRevSteps (frame : AffineConjunctionFrame) : Nat :=
  affineConjunctionUntilFinishSteps frame + 1

/-- Execute one complete runtime frame, preserve an arbitrary unconsumed
input tail, and stop at the clean redirectable finish label. -/
def affineConjunction_runToFinish (frame : AffineConjunctionFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame ++ tail) output)
      (some (affineConjunctionFinishCfg tail
        ((affineConjunctionGateStream frame).reverse ++ output)))
      (affineConjunctionUntilFinishSteps frame) := by
  let sourceInput := encodeAffineConjunctionSources frame.wires.reverse ++
    .frameEnd :: tail
  have hstart : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg
        (encodeUnaryFrameBlock frame.start ++ sourceInput) output)
      (some (affineConjunctionWireLoopCfg frame.start sourceInput
        (.constTrueMark :: output)))
      (affineConjunctionStartSteps frame.start) := by
    simpa [sourceInput] using
      affineConjunctionStart_load frame.start sourceInput output
  have hsources : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionWireLoopCfg frame.start sourceInput
        (.constTrueMark :: output))
      (some (affineConjunctionFinishCfg tail
        (((AffineConjunction.chunksFrom frame.start frame.wires.reverse).flatMap
          encodeCircuitGate).reverse ++ .constTrueMark :: output)))
      (affineConjunctionFoldSteps frame.start frame.wires.reverse) := by
    simpa [sourceInput] using
      affineConjunctionSources_runToFinish frame.wires.reverse frame.start
        tail (.constTrueMark :: output)
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (affineConjunctionStartSteps frame.start)
    (affineConjunctionFoldSteps frame.start frame.wires.reverse)
    _ (affineConjunctionWireLoopCfg frame.start sourceInput
      (.constTrueMark :: output)) _ hstart hsources
  convert full using 1
  · simp [encodeAffineConjunctionFrame, sourceInput, List.append_assoc]
  · simp [affineConjunctionGateStream, encodeCircuitGate,
      List.reverse_append, List.append_assoc]
  · simp [affineConjunctionUntilFinishSteps]
    omega

/-- Standalone exact execution theorem for one affine conjunction frame. -/
def affineConjunction_run (frame : AffineConjunctionFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg (encodeAffineConjunctionFrame frame) output)
      (some (haltCfg affineConjunctionRevProgram
        ((affineConjunctionGateStream frame).reverse ++ output)))
      (affineConjunctionRevSteps frame) := by
  let gateOutput := (affineConjunctionGateStream frame).reverse ++ output
  have hfinish := affineConjunction_runToFinish frame [] output
  have hhalt : EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionFinishCfg [] gateOutput)
      (some (haltCfg affineConjunctionRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineConjunctionRevProgram)
    (affineConjunctionUntilFinishSteps frame) 1
    _ (affineConjunctionFinishCfg [] gateOutput) _ hfinish hhalt
  convert full using 1
  · simp
  · simp [affineConjunctionRevSteps, Nat.add_comm]

/-- Weighted unconsumed source size.  The factor two pays for the fact that
the running carry grows while each unary block is consumed. -/
private def affineConjunctionSourceWeight : List Nat → Nat
  | [] => 0
  | source :: rest => 2 * (source + 1) +
      affineConjunctionSourceWeight rest

private theorem affineConjunctionSourceWeight_eq (sources : List Nat) :
    affineConjunctionSourceWeight sources =
      2 * (encodeAffineConjunctionSources sources).length := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp [affineConjunctionSourceWeight, encodeAffineConjunctionSources,
        encodeUnaryFrameBlock, ih]
      omega

private theorem affineConjunctionFold_steps_le
    (sources : List Nat) (carry : Nat) :
    affineConjunctionFoldSteps carry sources ≤
      20 * (carry + affineConjunctionSourceWeight sources + 1) ^ 2 + 1 := by
  induction sources generalizing carry with
  | nil =>
      simp [affineConjunctionFoldSteps, affineConjunctionFinishSteps,
        affineConjunctionSourceWeight]
      nlinarith
  | cons source rest ih =>
      have hrest := ih (carry + 1)
      calc
        affineConjunctionFoldSteps carry (source :: rest) =
            affineConjunctionWireSteps carry source +
              affineConjunctionFoldSteps (carry + 1) rest := rfl
        _ ≤ affineConjunctionWireSteps carry source +
              (20 * (carry + 1 + affineConjunctionSourceWeight rest + 1) ^ 2 +
                1) := Nat.add_le_add_left hrest _
        _ ≤ 20 *
              (carry + affineConjunctionSourceWeight (source :: rest) + 1) ^ 2 +
                1 := by
          let restMeasure := carry + 1 +
            affineConjunctionSourceWeight rest + 1
          let delta := 2 * source + 1
          have hmeasure :
              carry + affineConjunctionSourceWeight (source :: rest) + 1 =
                restMeasure + delta := by
            simp [affineConjunctionSourceWeight, restMeasure, delta]
            omega
          have hcarry : carry + 2 ≤ restMeasure := by
            simp [restMeasure]
          have hdelta : 1 ≤ delta := by simp [delta]
          have hproduct : (carry + 2) * 1 ≤ restMeasure * delta :=
            Nat.mul_le_mul hcarry hdelta
          have hdeltaSquare : 4 * source + 1 ≤ delta ^ 2 := by
            simp [delta]
            nlinarith
          have hcost :
              8 * source + 5 * carry + 14 ≤
                20 * (2 * restMeasure * delta + delta ^ 2) := by
            have hproductScaled : 40 * (carry + 2) ≤
                40 * (restMeasure * delta) :=
              Nat.mul_le_mul_left 40 (by simpa using hproduct)
            have hdeltaScaled : 20 * (4 * source + 1) ≤
                20 * delta ^ 2 := Nat.mul_le_mul_left 20 hdeltaSquare
            rw [show 20 * (2 * restMeasure * delta + delta ^ 2) =
              40 * (restMeasure * delta) + 20 * delta ^ 2 by ring]
            omega
          rw [hmeasure]
          change affineConjunctionWireSteps carry source +
              (20 * restMeasure ^ 2 + 1) ≤
            20 * (restMeasure + delta) ^ 2 + 1
          have hsquare : (restMeasure + delta) ^ 2 =
              restMeasure ^ 2 + 2 * restMeasure * delta + delta ^ 2 := by
            ring
          rw [hsquare]
          have hwireCost : affineConjunctionWireSteps carry source ≤
              20 * (2 * restMeasure * delta + delta ^ 2) := by
            simp [affineConjunctionWireSteps, affineConjunctionWireLoadSteps,
              affineAndRevCoreSteps]
            omega
          rw [show 20 *
              (restMeasure ^ 2 + 2 * restMeasure * delta + delta ^ 2) + 1 =
            (20 * restMeasure ^ 2 + 1) +
              20 * (2 * restMeasure * delta + delta ^ 2) by ring]
          omega

/-- The fixed conjunction controller runs in a quadratic bound in the exact
delimiter-bearing input length. -/
theorem affineConjunctionRev_steps_le (frame : AffineConjunctionFrame) :
    affineConjunctionRevSteps frame ≤
      1000 * (encodeAffineConjunctionFrame frame).length ^ 2 + 2 := by
  let sourceLength :=
    (encodeAffineConjunctionSources frame.wires.reverse).length
  let frameLength := (encodeAffineConjunctionFrame frame).length
  let measure := frame.start +
    affineConjunctionSourceWeight frame.wires.reverse + 1
  have hframeLength : frameLength = frame.start + sourceLength + 2 := by
    simp [frameLength, sourceLength, encodeAffineConjunctionFrame,
      encodeUnaryFrameBlock]
    omega
  have hweight :
      affineConjunctionSourceWeight frame.wires.reverse = 2 * sourceLength := by
    simpa [sourceLength] using
      affineConjunctionSourceWeight_eq frame.wires.reverse
  have hmeasure : measure ≤ 2 * frameLength := by
    simp only [measure]
    omega
  have hsquare : measure ^ 2 ≤ (2 * frameLength) ^ 2 :=
    Nat.pow_le_pow_left hmeasure 2
  have hfold := affineConjunctionFold_steps_le
    frame.wires.reverse frame.start
  have hscaled : 20 * measure ^ 2 ≤ 20 * (2 * frameLength) ^ 2 :=
    Nat.mul_le_mul_left 20 hsquare
  change affineConjunctionRevSteps frame ≤ 1000 * frameLength ^ 2 + 2
  simp only [affineConjunctionRevSteps, affineConjunctionUntilFinishSteps,
    affineConjunctionStartSteps]
  simp only [measure] at hscaled
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
