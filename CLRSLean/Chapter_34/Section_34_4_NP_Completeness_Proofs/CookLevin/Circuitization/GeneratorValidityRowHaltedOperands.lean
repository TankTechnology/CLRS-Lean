import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFirstValidityHaltedFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowAffineOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleRowMark

/-!
# Source compilation of every validity row's halted operands

The first validity-row source compiler supplies one closed operand triple.
This module closes the row-iteration gap for that phase.  Three simultaneous
affine progressions generate {lit}`haltedStart`, {lit}`haltedLeft`, and
{lit}`haltedRight`
for every arithmetic validity-row frame, directly from the raw verifier word.
The resulting fixed TM2 emits the actual delimiter-bearing row-major operand
stream consumed by the halted/none-label equality controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Exact row-major operand family -/

/-- The three halted/none-label operands advance affinely with the validity
row gate cost and the tableau configuration width. -/
def verifierValidityRowHaltedProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTripleProgression :=
  exactPolynomialAffineUnaryTripleProgression
    (verifierFirstValidityRowStartPolynomial W +
      (rawOneHotGatePolynomial W.machine.tm).comp (verifierHeight W))
    0
    (Polynomial.C (labelCount W.machine.tm + 1))
    (verifierValidityRowCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W)
    input

/-- Natural operand triples generated from the raw verifier word. -/
def verifierValidityRowHaltedTriples
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (Nat × Nat × Nat) :=
  affineUnaryTripleProgressionRows
    (verifierValidityRowHaltedProgression W input)

/-- The generated triples agree field-for-field and row-for-row with the
actual runtime frames supplied to the complete validity-row controller. -/
theorem verifierValidityRowHaltedTriples_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowHaltedTriples W input =
      (verifierValidityRowFramesByLength W input.length).map fun frame =>
        (frame.haltedStart, frame.haltedLeft, frame.haltedRight) := by
  unfold verifierValidityRowHaltedTriples verifierValidityRowHaltedProgression
    exactPolynomialAffineUnaryTripleProgression
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [verifierFirstValidityRowStartPolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat, Polynomial.eval_comp, Polynomial.eval_zero,
    Polynomial.eval_C, verifierTableauInputPolynomial_eval,
    rawOneHotGatePolynomial_eval, verifierValidityRowCostPolynomial_eval,
    verifierCfgBitCountPolynomial_eval,
    verifierValidityRowCountPolynomial_eval]
  unfold verifierValidityRowFramesByLength arithmeticValidityRowFrames
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext row
  simp only [arithmeticValidityRowFrame, arithmeticHaltedMatchStart,
    arithmeticNoneLabelWire, Function.comp_apply]
  apply Prod.ext
  · simp
    omega
  · apply Prod.ext
    · simp
    · simp
      omega

/-! ## Concrete raw-input TM2 -/

/-- Delimiter-bearing row-major halted operand frames. -/
def verifierValidityRowHaltedOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    (verifierFirstValidityRowStartPolynomial W +
      (rawOneHotGatePolynomial W.machine.tm).comp (verifierHeight W))
    0
    (Polynomial.C (labelCount W.machine.tm + 1))
    (verifierValidityRowCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W)
    input

/-- The concrete byte stream is exactly the three halted operands of every
actual validity-row frame, in controller consumption order. -/
theorem verifierValidityRowHaltedOperandFrames_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowHaltedOperandFrames W input =
      (verifierValidityRowFramesByLength W input.length).flatMap fun frame =>
        encodeUnaryFrame
          [frame.haltedStart, frame.haltedLeft, frame.haltedRight] := by
  change (verifierValidityRowHaltedTriples W input).flatMap
      (fun row => encodeUnaryFrame [row.1, row.2.1, row.2.2]) = _
  rw [verifierValidityRowHaltedTriples_eq_frames]
  simp [List.flatMap_map]

/-- A fixed polynomial-time TM2 compiles all three actual halted operands of
all validity rows directly from the raw verifier word. -/
noncomputable def
    verifierValidityRowHaltedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowHaltedOperandFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (verifierFirstValidityRowStartPolynomial W +
        (rawOneHotGatePolynomial W.machine.tm).comp (verifierHeight W))
      0
      (Polynomial.C (labelCount W.machine.tm + 1))
      (verifierValidityRowCostPolynomial W)
      (verifierCfgBitCountPolynomial W)
      (verifierCfgBitCountPolynomial W)
      (verifierValidityRowCountPolynomial W)

/-! ## Row-marked source interface -/

/-- Insert one outer `frameEnd` after each complete halted operand triple.
The ordinary separator after `haltedRight` is retained, because it belongs to
the halted-equality controller invocation itself. -/
def verifierValidityRowHaltedMarkedOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  markUnaryTripleRows (verifierValidityRowHaltedOperandFrames W input)

/-- The marked source has exactly one packet per canonical validity row. -/
theorem verifierValidityRowHaltedMarkedOperandFrames_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowHaltedMarkedOperandFrames W input =
      (verifierValidityRowFramesByLength W input.length).flatMap fun frame =>
        encodeUnaryFrame
          [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
            [.frameEnd] := by
  unfold verifierValidityRowHaltedMarkedOperandFrames
  change markUnaryTripleRows
      (encodeUnaryTripleRows (verifierValidityRowHaltedTriples W input)) = _
  rw [markUnaryTripleRows_encode,
    verifierValidityRowHaltedTriples_eq_frames]
  simp [encodeUnaryTripleMarkedRows, List.flatMap_map]

/-- A fixed polynomial-time TM2 compiles the row-marked halted operand
packets directly from the raw verifier word. -/
noncomputable def
    verifierValidityRowHaltedMarkedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowHaltedMarkedOperandFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierValidityRowHaltedOperandFrames_computableInPolyTime W)
      markUnaryTripleRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      markUnaryTripleRows (verifierValidityRowHaltedOperandFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
