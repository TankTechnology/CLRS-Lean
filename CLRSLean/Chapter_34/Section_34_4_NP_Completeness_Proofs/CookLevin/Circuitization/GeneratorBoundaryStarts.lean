import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmsLayout

/-!
# Exact polynomial starts of the post-transition boundaries

These polynomials expose the fresh-wire indices at which the symbolic initial
boundary, separator NOT family, and input arms begin.  They replace opaque
proof-carrying builder lengths by arithmetic values computable from the raw
input length.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact polynomial for the builder length after all adjacent-row
transitions. -/
def verifierTransitionEndPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierTransitionStartPolynomial W +
    verifierHorizon W * verifierTransitionCostPolynomial W

@[simp] theorem verifierTransitionEndPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTransitionEndPolynomial W).eval n =
      (arithmeticTransitionsAt W.machine.tm
        ((verifierHeight W).eval n)
        ((verifierHorizon W).eval n)).builder.gates.length := by
  unfold verifierTransitionEndPolynomial arithmeticTransitionsAt
  rw [transitionCircuitFamily_gate_delta]
  rw [← verifierTransitionStartPolynomial_eval_eq_validity_length]
  simp [Polynomial.eval_add, Polynomial.eval_mul,
    verifierTransitionCostPolynomial_eval]

/-- At an actual verifier word, the transition-end polynomial is the literal
semantic transition-builder length. -/
theorem verifierTransitionEndPolynomial_eval_eq_builder
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionEndPolynomial W).eval input.length =
      (verifierTransitions W input).builder.gates.length := by
  simpa [verifierTransitions, verifierRows, verifierPool,
    verifierValidity, arithmeticTransitionsAt, arithmeticValidityAt,
    arithmeticPoolAt, arithmeticRowsAt] using
      verifierTransitionEndPolynomial_eval W input.length

/-- Exact polynomial for the builder length after complete symbolic
initial-row equality. -/
def verifierInitialBoundaryEndPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierTransitionEndPolynomial W +
    Polynomial.C 6 * verifierCfgBitCountPolynomial W + 1

@[simp] theorem verifierInitialBoundaryEndPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInitialBoundaryEndPolynomial W).eval n =
      (verifierTransitionEndPolynomial W).eval n +
        (6 * cfgBitCount W.machine.tm ((verifierHeight W).eval n) + 1) := by
  simp [verifierInitialBoundaryEndPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- The initial-boundary end polynomial is the literal semantic builder
length. -/
theorem verifierInitialBoundaryEndPolynomial_eval_eq_builder
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInitialBoundaryEndPolynomial W).eval input.length =
      (verifierInitialBoundary W input).builder.gates.length := by
  rw [verifierInitialBoundaryEndPolynomial_eval,
    verifierTransitionEndPolynomial_eval_eq_builder]
  unfold verifierInitialBoundary
  rw [symbolicInitialCfgCircuit_gate_delta]

/-- Exact polynomial for the builder length after separator negations and,
equivalently, the start of the first candidate-length arm. -/
def verifierInputArmsStartPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierInitialBoundaryEndPolynomial W + verifierHeight W

@[simp] theorem verifierInputArmsStartPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInputArmsStartPolynomial W).eval n =
      (verifierInitialBoundaryEndPolynomial W).eval n +
        (verifierHeight W).eval n := by
  simp [verifierInputArmsStartPolynomial, Polynomial.eval_add]

/-- The arithmetic arms start is the actual builder length returned by the
separator-NOT phase. -/
theorem verifierInputArmsStartPolynomial_eval_eq_separatorBuilder
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmsStartPolynomial W).eval input.length =
      let rows := verifierRows W input
      let pool := verifierPool W input
      let validity := verifierValidity W input
      let transitions := verifierTransitions W input
      let initial := verifierInitialBoundary W input
      let extension := pool.extension.trans (validity.extension.trans
        (transitions.extension.trans initial.extension))
      let row := rows.rows (verifierFirstRow _)
      let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
      (VerifierInput.buildSeparatorNots initial.builder
        (row.stack W.machine.tm.k₀) (hrow.stack _)
        (verifierInputCode W none)).builder.gates.length := by
  rw [verifierInputArmsStartPolynomial_eval,
    verifierInitialBoundaryEndPolynomial_eval_eq_builder]
  rw [VerifierInput.SeparatorNotsResult.gate_delta]

end CLRS.Chapter34.Turing.CookLevin
