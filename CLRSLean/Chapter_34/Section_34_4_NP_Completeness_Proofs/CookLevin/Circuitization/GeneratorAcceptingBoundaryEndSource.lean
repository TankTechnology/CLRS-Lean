import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryClosure
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputAddPolynomial

/-!
# Concrete source for the accepting-boundary endpoint

The accepting-output test has a machine-static branch.  When the Boolean
acceptance symbol belongs to the reachable output alphabet, the exact-row
equality appends six gates per configuration bit.  Otherwise the semantic
false boundary reuses the shared false wire and appends no gates.  This file
turns that split into one exact polynomial endpoint generated from the raw
verifier word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact, machine-static polynomial gate cost of the accepting boundary. -/
def verifierAcceptingBoundaryCostPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  if verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁ then
    Polynomial.C 6 * verifierCfgBitCountPolynomial W + 1
  else
    0

@[simp] theorem verifierAcceptingBoundaryCostPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierAcceptingBoundaryCostPolynomial W).eval n =
      acceptingOutputCircuitGateCost W.machine.tm
        ((verifierHeight W).eval n) (verifierAcceptingOutput W) := by
  classical
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · have hfit : AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval n) (verifierAcceptingOutput W) :=
      by
        rw [verifierAcceptingOutput_eq_singleton]
        refine ⟨?_, by simpa using verifierHeight_one_le W n⟩
        intro symbol hsymbol
        have hsymbolEq : symbol = verifierAcceptingSymbol W := by
          simpa using hsymbol
        simpa [hsymbolEq] using hmember
    rw [verifierAcceptingOutput_eq_singleton] at hfit ⊢
    rw [show verifierAcceptingBoundaryCostPolynomial W =
        Polynomial.C 6 * verifierCfgBitCountPolynomial W + 1 by
      simp [verifierAcceptingBoundaryCostPolynomial, hmember]]
    rw [show acceptingOutputCircuitGateCost W.machine.tm
        ((verifierHeight W).eval n) [verifierAcceptingSymbol W] =
        6 * cfgBitCount W.machine.tm ((verifierHeight W).eval n) + 1 by
      unfold acceptingOutputCircuitGateCost
      rw [if_pos hfit]]
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  · have hfit : ¬ AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval n) (verifierAcceptingOutput W) := by
      intro h
      apply hmember
      apply h.1 (verifierAcceptingSymbol W)
      simp
    rw [verifierAcceptingOutput_eq_singleton] at hfit ⊢
    rw [show verifierAcceptingBoundaryCostPolynomial W = 0 by
      simp [verifierAcceptingBoundaryCostPolynomial, hmember]]
    unfold acceptingOutputCircuitGateCost
    rw [if_neg hfit]
    simp

/-- Builder-free arithmetic endpoint of the complete accepting boundary. -/
def verifierAcceptingBoundaryEnd
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  verifierInputBoundaryEnd W input +
    (verifierAcceptingBoundaryCostPolynomial W).eval input.length

/-- The semantic accepting builder ends at the generated arithmetic point. -/
theorem verifierAcceptingBoundary_gates_length_eq_end
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierAcceptingBoundary W input).builder.gates.length =
      verifierAcceptingBoundaryEnd W input := by
  unfold verifierAcceptingBoundary
  rw [acceptingOutputCircuit_gate_delta]
  rw [verifierInputBoundary_gates_length_eq_end]
  simp only [verifierAcceptingBoundaryEnd]
  rw [verifierAcceptingBoundaryCostPolynomial_eval]
  rfl

/-- Unary singleton containing the accepting-boundary endpoint. -/
def verifierAcceptingBoundaryEndFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameSameInputAddPolynomial
    (verifierInputBoundaryEnd W)
    (verifierAcceptingBoundaryCostPolynomial W) input

@[simp] theorem verifierAcceptingBoundaryEndFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierAcceptingBoundaryEndFrame W input =
      encodeUnaryFrame [verifierAcceptingBoundaryEnd W input] := by
  simp [verifierAcceptingBoundaryEndFrame, verifierAcceptingBoundaryEnd]

/-- A fixed polynomial-time TM2 computes the exact endpoint from raw input. -/
noncomputable def verifierAcceptingBoundaryEndFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingBoundaryEndFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputBoundaryEndFrame_computableInPolyTime W
  let base : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame [verifierInputBoundaryEnd W input]) :=
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierInputBoundaryEndFrame_eq] at run
        simpa only [id_eq] using run }
  change _root_.Turing.TM2ComputableInPolyTime id id
    (unaryFrameSameInputAddPolynomial
      (verifierInputBoundaryEnd W)
      (verifierAcceptingBoundaryCostPolynomial W))
  exact unaryFrameSameInputAddPolynomial_computableInPolyTime
    (verifierInputBoundaryEnd W)
    (verifierAcceptingBoundaryCostPolynomial W) base

end CLRS.Chapter34.Turing.CookLevin
