import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowAffineOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryTripleProgression

/-!
# Runtime seeds for every Cook--Levin validity row

The complete row frame is variable-width, but its arithmetic expansion is
determined by three row-major values: the common tableau height, the current
validity-gate start, and the current tableau-bit base.  This module compiles
those seeds directly from the raw verifier word with one fixed triple-
progression TM2 and proves that expanding them gives exactly the canonical
validity-row family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Semantic row seeds -/

/-- Minimal arithmetic data from which the complete runtime frame of one
validity row is reconstructed. -/
structure ValidityRowSeed where
  height : Nat
  start : Nat
  rowBase : Nat
deriving DecidableEq, Repr

/-- Expand one row seed through the already verified arithmetic frame
constructor. -/
noncomputable def expandValidityRowSeed
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    AffineValidityRowFrame :=
  arithmeticValidityRowFrame tm seed.height seed.start seed.rowBase

/-- One simultaneous affine progression for height, validity-gate start, and
tableau-bit base across every verifier row. -/
def verifierValidityRowSeedProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTripleProgression :=
  exactPolynomialAffineUnaryTripleProgression
    (verifierHeight W)
    (verifierTableauInputPolynomial W + 2)
    0
    0
    (verifierValidityRowCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W)
    input

/-- Natural row-major seeds decoded from the simultaneous progression. -/
def verifierValidityRowSeeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List ValidityRowSeed :=
  (affineUnaryTripleProgressionRows
    (verifierValidityRowSeedProgression W input)).map fun row =>
      { height := row.1
        start := row.2.1
        rowBase := row.2.2 }

/-- Closed row-index formula for the simultaneous seed progression. -/
theorem verifierValidityRowSeedTriples_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineUnaryTripleProgressionRows
        (verifierValidityRowSeedProgression W input) =
      List.ofFn fun row : Fin
          (tableauRowCount ((verifierHorizon W).eval input.length)) =>
        ((verifierHeight W).eval input.length,
          tableauInputCount W.machine.tm
              ((verifierHeight W).eval input.length)
              ((verifierHorizon W).eval input.length) + 2 +
            row.val * validCfgGateCost W.machine.tm
              ((verifierHeight W).eval input.length),
          row.val * cfgBitCount W.machine.tm
            ((verifierHeight W).eval input.length)) := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [verifierValidityRowSeedProgression,
    exactPolynomialAffineUnaryTripleProgression,
    verifierValidityRowCountPolynomial_eval,
    verifierTableauInputPolynomial_eval,
    verifierValidityRowCostPolynomial_eval,
    verifierCfgBitCountPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_ofNat, Polynomial.eval_zero]
  apply List.ofFn_inj.mpr
  funext row
  simp

/-- Expanding the compiled seeds reconstructs the actual canonical row family
with exactly the same length, order, gate starts, and tableau bases. -/
theorem verifierValidityRowSeeds_expand_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowSeeds W input).map
        (expandValidityRowSeed W.machine.tm) =
      verifierValidityRowFramesByLength W input.length := by
  unfold verifierValidityRowSeeds
  rw [verifierValidityRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  unfold verifierValidityRowFramesByLength arithmeticValidityRowFrames
  apply List.ofFn_inj.mpr
  funext row
  rfl

/-! ## Concrete raw-input seed compiler -/

/-- Delimiter-bearing `(height, start, rowBase)` blocks in row-major order. -/
def verifierValidityRowSeedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    (verifierHeight W)
    (verifierTableauInputPolynomial W + 2)
    0
    0
    (verifierValidityRowCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierValidityRowCountPolynomial W)
    input

/-- The compiled byte stream is exactly the three fields of every semantic
seed, in expansion-controller consumption order. -/
theorem verifierValidityRowSeedFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowSeedFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] := by
  simp [verifierValidityRowSeedFrames,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    verifierValidityRowSeeds, verifierValidityRowSeedProgression,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleRowValues, List.flatMap_map]

/-- A fixed polynomial-time TM2 compiles every row-major validity seed
directly from the raw verifier word. -/
noncomputable def verifierValidityRowSeedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowSeedFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (verifierHeight W)
      (verifierTableauInputPolynomial W + 2)
      0
      0
      (verifierValidityRowCostPolynomial W)
      (verifierCfgBitCountPolynomial W)
      (verifierValidityRowCountPolynomial W)

end CLRS.Chapter34.Turing.CookLevin
