import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrStartSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputAddPolynomial

/-!
# Concrete source for the verifier input-boundary endpoint

The input-boundary endpoint is the dynamic start of its final disjunction
plus the exact cost of that false-seeded disjunction.  This module computes
that endpoint directly from the raw verifier word and identifies it with the
proof-carrying builder length used by the accepting boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact polynomial cost of the final false-seeded input-arm disjunction. -/
def verifierInputFinalOrCostPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierInputArmCountPolynomial W + 1

@[simp] theorem verifierInputFinalOrCostPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInputFinalOrCostPolynomial W).eval n =
      W.certificateBound.eval n + 2 := by
  simp [verifierInputFinalOrCostPolynomial]

/-- Builder-free arithmetic endpoint of the complete input boundary. -/
def verifierInputBoundaryEnd
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  verifierInputFinalOrStart W input +
    (verifierInputFinalOrCostPolynomial W).eval input.length

/-- The proof-carrying input-boundary builder ends at the arithmetic endpoint. -/
theorem verifierInputBoundary_gates_length_eq_end
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundary W input).builder.gates.length =
      verifierInputBoundaryEnd W input := by
  have hfinal :
      (verifierInputBoundary W input).builder.gates.length =
        (verifierInputBoundaryScript W input).finalOrStart +
          (verifierInputBoundaryScript W input).finalOrWires.length + 1 := by
    unfold verifierInputBoundary verifierInputBoundaryScript
      compileVerifierInputShapeScript verifierInputShapeCircuit
    dsimp only
    rw [CircuitBuilder.disjunction_gate_delta]
  rw [hfinal, verifierInputBoundaryScript_finalOrStart_eq_arithmetic]
  simp only [verifierInputBoundaryScript_finalOrWires_length,
    verifierInputFinalOrCostPolynomial_eval, verifierInputBoundaryEnd]
  omega

/-- Exact unary singleton containing the complete input-boundary endpoint. -/
def verifierInputBoundaryEndFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameSameInputAddPolynomial
    (verifierInputFinalOrStart W)
    (verifierInputFinalOrCostPolynomial W) input

@[simp] theorem verifierInputBoundaryEndFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputBoundaryEndFrame W input =
      encodeUnaryFrame [verifierInputBoundaryEnd W input] := by
  simp [verifierInputBoundaryEndFrame, verifierInputBoundaryEnd]

/-- End-to-end fixed polynomial-time TM2 from the raw verifier word to the
exact builder endpoint at which accepting-boundary gates begin. -/
noncomputable def verifierInputBoundaryEndFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputBoundaryEndFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputFinalOrStartFrame_computableInPolyTime W
  let source : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame
        [verifierInputFinalOrStart W input]) :=
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierInputFinalOrStartFrame_eq] at run
        simpa only [id_eq] using run }
  change _root_.Turing.TM2ComputableInPolyTime id id
    (unaryFrameSameInputAddPolynomial
      (verifierInputFinalOrStart W)
      (verifierInputFinalOrCostPolynomial W))
  exact unaryFrameSameInputAddPolynomial_computableInPolyTime
    (verifierInputFinalOrStart W)
    (verifierInputFinalOrCostPolynomial W) source

end CLRS.Chapter34.Turing.CookLevin
