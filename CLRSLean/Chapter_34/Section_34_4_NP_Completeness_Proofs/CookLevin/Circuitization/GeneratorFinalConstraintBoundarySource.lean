import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintBoundaryOutputs
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat

/-!
# Raw-input source for the three final boundary wires

The symbolic-initial output is a polynomial singleton.  The input-shape and
positive accepting outputs are obtained by adding fixed polynomials to
already compiled dynamic endpoints.  The negative accepting branch emits the
shared false-pool coordinate.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Unary singleton for the symbolic-initial output. -/
def verifierInitialBoundaryOutputFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryFrame
    (verifierInitialBoundaryOutputPolynomial W) input

@[simp] theorem verifierInitialBoundaryOutputFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialBoundaryOutputFrame W input =
      encodeUnaryFrameBlock (verifierInitialBoundary W input).wire := by
  rw [verifierInitialBoundary_wire_eq]
  rfl

/-- Unary singleton for the input-shape output. -/
def verifierInputBoundaryOutputFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameSameInputAddPolynomial
    (verifierInputFinalOrStart W)
    (verifierInputArmCountPolynomial W) input

@[simp] theorem verifierInputBoundaryOutputFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputBoundaryOutputFrame W input =
      encodeUnaryFrameBlock (verifierInputBoundary W input).wire := by
  rw [verifierInputBoundary_wire_eq]
  simp [verifierInputBoundaryOutputFrame, verifierInputBoundaryOutput]

/-- Unary singleton for the total accepting-boundary output. -/
def verifierAcceptingBoundaryOutputFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  if verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁ then
    unaryFrameSameInputAddPolynomial
      (verifierInputBoundaryEnd W)
      (Polynomial.C 6 * verifierCfgBitCountPolynomial W) input
  else
    exactPolynomialUnaryFrame
      (verifierInitialFalseWirePolynomial W) input

@[simp] theorem verifierAcceptingBoundaryOutputFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierAcceptingBoundaryOutputFrame W input =
      encodeUnaryFrameBlock (verifierAcceptingBoundary W input).wire := by
  rw [verifierAcceptingBoundary_wire_eq]
  classical
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · simp [verifierAcceptingBoundaryOutputFrame,
      verifierAcceptingBoundaryOutput, hmember]
  · simp [verifierAcceptingBoundaryOutputFrame,
      verifierAcceptingBoundaryOutput, hmember,
      exactPolynomialUnaryFrame]

/-- Forward delimiter-bearing source for `[initial, input, accepting]`. -/
def verifierBoundaryOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierInitialBoundaryOutputFrame W input ++
    verifierInputBoundaryOutputFrame W input ++
    verifierAcceptingBoundaryOutputFrame W input

/-- The compiled source is exactly the semantic boundary-output suffix. -/
theorem verifierBoundaryOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierBoundaryOutputSource W input =
      encodeAffineConjunctionSources
        [(verifierInitialBoundary W input).wire,
          (verifierInputBoundary W input).wire,
          (verifierAcceptingBoundary W input).wire] := by
  simp [verifierBoundaryOutputSource, encodeAffineConjunctionSources]

/-- Fixed polynomial-time source for the symbolic-initial output. -/
noncomputable def verifierInitialBoundaryOutputFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialBoundaryOutputFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialUnaryFrame_computableInPolyTime
    (verifierInitialBoundaryOutputPolynomial W)

/-- Fixed polynomial-time source for the input-shape output. -/
noncomputable def verifierInputBoundaryOutputFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputBoundaryOutputFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputFinalOrStartFrame_computableInPolyTime W
  let base : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame
        [verifierInputFinalOrStart W input]) := by
    simpa only [verifierInputFinalOrStartFrame_eq] using raw
  exact unaryFrameSameInputAddPolynomial_computableInPolyTime
    (verifierInputFinalOrStart W)
    (verifierInputArmCountPolynomial W) base

/-- Fixed polynomial-time source for the static accepting branch. -/
noncomputable def verifierAcceptingBoundaryOutputFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingBoundaryOutputFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · let raw := verifierInputBoundaryEndFrame_computableInPolyTime W
    let base : _root_.Turing.TM2ComputableInPolyTime id id
        (fun input => encodeUnaryFrame
          [verifierInputBoundaryEnd W input]) := by
      simpa only [verifierInputBoundaryEndFrame_eq] using raw
    have result := unaryFrameSameInputAddPolynomial_computableInPolyTime
      (verifierInputBoundaryEnd W)
      (Polynomial.C 6 * verifierCfgBitCountPolynomial W) base
    simpa [verifierAcceptingBoundaryOutputFrame, hmember] using result
  · have result := exactPolynomialUnaryFrame_computableInPolyTime
      (Γ := Γ) (verifierInitialFalseWirePolynomial W)
    simpa [verifierAcceptingBoundaryOutputFrame, hmember] using result

/-- One fixed polynomial-time TM2 emits all three boundary outputs in their
public conjunction order. -/
noncomputable def verifierBoundaryOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBoundaryOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  let initial := verifierInitialBoundaryOutputFrame_computableInPolyTime W
  let inputShape := verifierInputBoundaryOutputFrame_computableInPolyTime W
  let first := unaryFrameSameInputConcat_computableInPolyTime
    initial inputShape
  let accepting := verifierAcceptingBoundaryOutputFrame_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    first accepting
  simpa [verifierBoundaryOutputSource, List.append_assoc] using complete

end CLRS.Chapter34.Turing.CookLevin
