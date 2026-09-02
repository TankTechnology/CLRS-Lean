import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmStartsSource

/-!
# Affine wire channels of verifier-input arms

Two of the four wire blocks in every candidate-length arm are singleton
affine progressions: its selected height bit advances by one, and its blank
separator cell advances by one input-stack symbol width.  This module derives
their exact input-length polynomials and compiles both channels from the raw
word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First public-input height wire, corresponding to candidate length zero. -/
noncomputable def verifierInputArmHeightBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  let tm := W.machine.tm
  Polynomial.C
      (1 + (labelCount tm + 1) + stateCount tm +
        arithmeticStackOrdinal tm tm.k₀ + 1) +
    Polynomial.C (cfgStackBitOffsetHeightCoeff tm tm.k₀) *
      verifierHeight W + Polynomial.X

@[simp] theorem verifierInputArmHeightBasePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInputArmHeightBasePolynomial W).eval n =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm ((verifierHeight W).eval n)
          W.machine.tm.k₀ + (1 + n) := by
  rw [cfgStackBitOffset_eq_affine]
  simp [verifierInputArmHeightBasePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- Height-wire singleton value for one candidate arm. -/
def verifierInputArmHeightWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) : Nat :=
  1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
    cfgStackBitOffset W.machine.tm ((verifierHeight W).eval input.length)
      W.machine.tm.k₀ + (arm.val + 1 + input.length)

/-- Blank separator-cell singleton value for one candidate arm. -/
def verifierInputArmSeparatorWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) : Nat :=
  1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
    cfgStackBitOffset W.machine.tm ((verifierHeight W).eval input.length)
      W.machine.tm.k₀ +
      (((verifierHeight W).eval input.length + 1) +
        ((verifierInputCode W none).val +
          ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) *
            arm.val))

/-- Raw-input affine stream of all height-wire operands. -/
def verifierInputArmHeightWireFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierInputArmHeightBasePolynomial W) 1
    (verifierInputArmCountPolynomial W) input

/-- Raw-input affine stream of all blank separator-cell operands. -/
def verifierInputArmSeparatorWireFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierInputSeparatorBasePolynomial W)
    (Polynomial.C
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1))
    (verifierInputArmCountPolynomial W) input

/-- The height channel has exactly the pointwise arithmetic coordinates. -/
theorem verifierInputArmHeightWireFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmHeightWireFrames W input =
      encodeUnaryFrame (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmHeightWire W input arm) := by
  unfold verifierInputArmHeightWireFrames
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierInputArmCountPolynomial_eval]
  apply congrArg encodeUnaryFrame
  apply List.ofFn_inj.mpr
  funext arm
  simp only [Fin.val_cast]
  simp [verifierInputArmHeightWire]
  omega

/-- The separator-cell channel has exactly the pointwise arithmetic
coordinates. -/
theorem verifierInputArmSeparatorWireFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmSeparatorWireFrames W input =
      encodeUnaryFrame (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmSeparatorWire W input arm) := by
  unfold verifierInputArmSeparatorWireFrames
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierInputArmCountPolynomial_eval]
  apply congrArg encodeUnaryFrame
  apply List.ofFn_inj.mpr
  funext arm
  simp only [Fin.val_cast]
  simp [verifierInputArmSeparatorWire,
    verifierInputSeparatorBasePolynomial_eval]
  ring

/-- The arithmetic arm wire list exposes the two compiled singleton
channels at its head and after its growing separator-NOT prefix. -/
theorem verifierInputArmArithmeticWires_eq_channels
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    verifierInputArmArithmeticWires W input arm =
      [verifierInputArmHeightWire W input arm] ++
      List.ofFn (fun prefixIndex : Fin arm.val =>
        (verifierInitialBoundaryEndPolynomial W).eval input.length +
          prefixIndex.val) ++
      [verifierInputArmSeparatorWire W input arm] ++
      List.ofFn (fun index : Fin input.length =>
        1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) W.machine.tm.k₀ +
            (((verifierHeight W).eval input.length + 1) +
              ((verifierInputCode W (some (input.get index))).val +
                ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) *
                  (arm.val + 1 + index.val)))) := by
  rfl

/-- Fixed polynomial-time TM2 for the height-wire channel. -/
noncomputable def verifierInputArmHeightWireFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputArmHeightWireFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (verifierInputArmHeightBasePolynomial W) 1
    (verifierInputArmCountPolynomial W)

/-- Fixed polynomial-time TM2 for the blank separator-cell channel. -/
noncomputable def verifierInputArmSeparatorWireFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputArmSeparatorWireFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (verifierInputSeparatorBasePolynomial W)
    (Polynomial.C
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1))
    (verifierInputArmCountPolynomial W)

end CLRS.Chapter34.Turing.CookLevin
