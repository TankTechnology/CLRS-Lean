import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorNotProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource

/-!
# Concrete source for verifier-input separator NOTs

The separator cell of the public input stack occupies one fixed affine wire
progression.  This module derives its exact input-length polynomial and feeds
it through the generic NOT-family source compiler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact polynomial for the first separator-symbol cell wire of the public
input stack. -/
noncomputable def verifierInputSeparatorBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  let tm := W.machine.tm
  Polynomial.C
      (1 + (labelCount tm + 1) + stateCount tm +
        arithmeticStackOrdinal tm tm.k₀ + 1 +
        (verifierInputCode W none).val) +
    Polynomial.C (cfgStackBitOffsetHeightCoeff tm tm.k₀ + 1) *
      verifierHeight W

@[simp] theorem verifierInputSeparatorBasePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInputSeparatorBasePolynomial W).eval n =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm ((verifierHeight W).eval n)
          W.machine.tm.k₀ +
        (((verifierHeight W).eval n + 1) +
          (verifierInputCode W none).val) := by
  rw [cfgStackBitOffset_eq_affine]
  simp [verifierInputSeparatorBasePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- Arithmetic separator-source list emitted directly from the raw verifier
word. -/
def verifierInputSeparatorCompiledSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  exactPolynomialAffineNotSources
    (verifierInputSeparatorBasePolynomial W)
    (Polynomial.C
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1))
    (verifierHeight W) input

/-- The arithmetic source is pointwise identical to the semantic first-row
input-stack separator source. -/
theorem verifierInputSeparatorCompiledSources_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputSeparatorCompiledSources W input =
      verifierInputSeparatorSources W input := by
  have hcompiled : verifierInputSeparatorCompiledSources W input =
      List.ofFn fun cell : Fin ((verifierHeight W).eval input.length) =>
        (verifierInputSeparatorBasePolynomial W).eval input.length +
          cell.val *
            ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) := by
    unfold verifierInputSeparatorCompiledSources
      exactPolynomialAffineNotSources eqFinProgressionSeeds
    rw [affineUnaryTripleProgressionRows_eq_ofFn]
    simp [exactPolynomialAffineUnaryTripleProgression]
    rfl
  rw [hcompiled]
  unfold verifierInputSeparatorSources VerifierInput.separatorNotSources
  apply List.ofFn_inj.mpr
  funext cell
  change (verifierInputSeparatorBasePolynomial W).eval input.length +
      cell.val *
        ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) =
    (verifierRows W input).rows (verifierFirstRow _)
      (CfgSlot.stackCell W.machine.tm.k₀ cell
        (verifierInputCode W none))
  rw [verifierRowStackCellWire_eq]
  rw [verifierInputSeparatorBasePolynomial_eval]
  simp [verifierFirstRow]
  ring

/-- Exact marker-bearing input consumed by the separator NOT-family phase. -/
def verifierInputSeparatorInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineNotFamilyInput
    (verifierInputSeparatorBasePolynomial W)
    (Polynomial.C
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1))
    (verifierHeight W) input

/-- The compiled input is byte-for-byte the canonical separator operand
encoding already consumed by the input-boundary controller. -/
theorem verifierInputSeparatorInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputSeparatorInputTarget W input =
      encodeAffineNotFamilySources (verifierInputSeparatorSources W input) := by
  unfold verifierInputSeparatorInputTarget
    exactPolynomialAffineNotFamilyInput
  exact congrArg encodeAffineNotFamilySources
    (verifierInputSeparatorCompiledSources_eq W input)

/-- One fixed polynomial-time TM2 compiles the exact separator NOT operands
from the raw verifier input. -/
noncomputable def
    verifierInputSeparatorInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputSeparatorInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineNotFamilyInput_computableInPolyTime
    (verifierInputSeparatorBasePolynomial W)
    (Polynomial.C
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1))
    (verifierHeight W)

end CLRS.Chapter34.Turing.CookLevin
