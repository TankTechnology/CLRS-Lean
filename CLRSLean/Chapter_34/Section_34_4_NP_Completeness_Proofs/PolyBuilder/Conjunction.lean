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

end CLRS.Chapter34.Turing.PolyBuilder
