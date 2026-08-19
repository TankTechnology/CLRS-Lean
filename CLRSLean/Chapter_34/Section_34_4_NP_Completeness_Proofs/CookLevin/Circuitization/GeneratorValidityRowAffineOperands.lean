import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowIndices
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression

/-!
# Source compilation of affine validity-row operands

Every validity row advances two essential runtime operands affinely.  Its
tableau-bit base advances by one configuration width, while its gate start
advances by one complete row-validity cost.  This module instantiates the
fixed affine progression TM2 for both families and identifies their values
with the actual arithmetic row family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact input-length polynomial for one configuration row's bit width. -/
def verifierCfgBitCountPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  (cfgBitPolynomial W.machine.tm).comp (verifierHeight W)

@[simp] theorem verifierCfgBitCountPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (inputLength : Nat) :
    (verifierCfgBitCountPolynomial W).eval inputLength =
      cfgBitCount W.machine.tm ((verifierHeight W).eval inputLength) := by
  simp [verifierCfgBitCountPolynomial, Polynomial.eval_comp]

/-- Runtime progression for the tableau-bit base of every validity row. -/
def verifierValidityRowBaseProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryProgression :=
  exactPolynomialAffineUnaryProgression 0
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W) input

/-- Runtime progression for the first gate allocated to every validity row. -/
def verifierValidityRowGateStartProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryProgression :=
  exactPolynomialAffineUnaryProgression
    (verifierTableauInputPolynomial W + 2)
    (verifierValidityRowCostPolynomial W)
    (verifierValidityRowCountPolynomial W) input

/-- Natural tableau bases generated from the raw verifier word. -/
def verifierValidityRowBaseValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  affineUnaryProgressionValues (verifierValidityRowBaseProgression W input)

/-- Natural validity-gate starts generated from the raw verifier word. -/
def verifierValidityRowGateStartValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  affineUnaryProgressionValues
    (verifierValidityRowGateStartProgression W input)

/-- Closed row-index formula for every generated tableau base. -/
theorem verifierValidityRowBaseValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowBaseValues W input =
      List.ofFn fun row : Fin
          (tableauRowCount ((verifierHorizon W).eval input.length)) =>
        row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) := by
  unfold verifierValidityRowBaseValues verifierValidityRowBaseProgression
    affineUnaryProgressionValues exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp

/-- Closed row-index formula for every generated validity-gate start. -/
theorem verifierValidityRowGateStartValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowGateStartValues W input =
      List.ofFn fun row : Fin
          (tableauRowCount ((verifierHorizon W).eval input.length)) =>
        tableauInputCount W.machine.tm
            ((verifierHeight W).eval input.length)
            ((verifierHorizon W).eval input.length) + 2 +
          row.val * validCfgGateCost W.machine.tm
            ((verifierHeight W).eval input.length) := by
  unfold verifierValidityRowGateStartValues
    verifierValidityRowGateStartProgression affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp [Polynomial.eval_add]

/-- The generated tableau bases are exactly the {lit}`haltedLeft` operands stored
in the real affine validity-row family. -/
theorem verifierValidityRowBaseValues_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowBaseValues W input =
      (verifierValidityRowFramesByLength W input.length).map
        AffineValidityRowFrame.haltedLeft := by
  rw [verifierValidityRowBaseValues_eq_ofFn]
  unfold verifierValidityRowFramesByLength arithmeticValidityRowFrames
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext row
  rfl

/-- Delimiter-bearing tableau-base frames. -/
def verifierValidityRowBaseFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream 0
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W) input

/-- Delimiter-bearing validity-gate-start frames. -/
def verifierValidityRowGateStartFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierTableauInputPolynomial W + 2)
    (verifierValidityRowCostPolynomial W)
    (verifierValidityRowCountPolynomial W) input

theorem verifierValidityRowBaseFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowBaseFrames W input =
      encodeUnaryFrame (verifierValidityRowBaseValues W input) := by
  rfl

theorem verifierValidityRowGateStartFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowGateStartFrames W input =
      encodeUnaryFrame (verifierValidityRowGateStartValues W input) := by
  rfl

/-- A fixed TM2 compiles all actual tableau-row bases from the raw word. -/
noncomputable def verifierValidityRowBaseFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowBaseFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    0 (verifierCfgBitCountPolynomial W)
      (verifierValidityRowCountPolynomial W)

/-- A fixed TM2 compiles all actual validity-gate starts from the raw word. -/
noncomputable def verifierValidityRowGateStartFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowGateStartFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (verifierTableauInputPolynomial W + 2)
    (verifierValidityRowCostPolynomial W)
    (verifierValidityRowCountPolynomial W)

end CLRS.Chapter34.Turing.CookLevin
