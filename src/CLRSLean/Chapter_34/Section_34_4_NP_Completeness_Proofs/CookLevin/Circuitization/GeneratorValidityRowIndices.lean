import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryIndexFrames

/-!
# Runtime ordinals for every Cook--Levin validity row

The all-row controller consumes one affine operand frame per tableau row.  To
compile those frames from the raw verifier word, a fixed source machine first
needs the exact runtime family of row ordinals.  This module instantiates the
generic polynomial unary-index compiler at the verifier horizon and proves
that the resulting delimiter-bearing frames have exactly the same length and
order as the semantic validity-row family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The number of validity rows is the verifier horizon plus its initial row. -/
def verifierValidityRowCountPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierHorizon W + 1

/-- Evaluating the row-count polynomial gives the exact tableau row count. -/
@[simp] theorem verifierValidityRowCountPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (inputLength : Nat) :
    (verifierValidityRowCountPolynomial W).eval inputLength =
      tableauRowCount ((verifierHorizon W).eval inputLength) := by
  simp [verifierValidityRowCountPolynomial, tableauRowCount,
    Polynomial.eval_add]

/-- Delimiter-bearing unary ordinals for all validity rows of a raw input. -/
def verifierValidityRowIndexFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryIndexFrames
    (verifierValidityRowCountPolynomial W) input

/-- The compiled ordinal frames enumerate exactly the positions of the
runtime affine validity-row family, with no missing or extra row. -/
theorem verifierValidityRowIndexFrames_eq_frameOrdinals
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowIndexFrames W input =
      encodeUnaryFrame
        (List.range
          (verifierValidityRowFramesByLength W input.length).length) := by
  have hlength :
      (verifierValidityRowFramesByLength W input.length).length =
        tableauRowCount ((verifierHorizon W).eval input.length) := by
    simp [verifierValidityRowFramesByLength, arithmeticValidityRowFrames]
  rw [hlength]
  simp [verifierValidityRowIndexFrames, exactPolynomialUnaryIndexFrames]

/-- A fixed polynomial-time TM2 compiles the raw verifier word directly into
the complete family of validity-row ordinals. -/
noncomputable def verifierValidityRowIndexFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowIndexFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialUnaryIndexFrames_computableInPolyTime
    (verifierValidityRowCountPolynomial W)

end CLRS.Chapter34.Turing.CookLevin
