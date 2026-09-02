import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryEndSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds

/-!
# Closed coordinates of the final validity outputs

Every canonical row-validity circuit ends at its last fresh wire.  Since all
rows have the same exact affine cost, their public outputs form one arithmetic
progression.  This module proves the coordinate formula independently of the
later conjunction serializer.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Last-wire offset of one canonical validity row, as a polynomial in the
public stack height. -/
def validCfgOutputOffsetPolynomial
    (tm : _root_.Turing.FinTM2) : Polynomial Nat := by
  letI : Fintype tm.K := tm.kFin
  exact Polynomial.C
      (3 * labelCount tm + 3 * stateCount tm + 19 +
        9 * Fintype.card tm.K) +
    Polynomial.C
      (∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 19)) *
        Polynomial.X

/-- The output offset is exactly one less than the nonempty row cost. -/
theorem validCfgOutputOffsetPolynomial_eval_add_one
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (validCfgOutputOffsetPolynomial tm).eval H + 1 =
      validCfgGateCost tm H := by
  letI : Fintype tm.K := tm.kFin
  rw [← validCfgGatePolynomial_eval tm H]
  simp only [validCfgOutputOffsetPolynomial, validCfgGatePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

/-- The pure single-row trace output is its start plus the exact output
offset. -/
theorem canonicalValidityGateTrace_wire_eq_start_add_offset
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) :
    (canonicalValidityGateTrace start wires).wire =
      start + (validCfgOutputOffsetPolynomial tm).eval H := by
  letI : Fintype tm.K := tm.kFin
  have hlast :
      (canonicalValidityGateTrace start wires).wire + 1 =
        start + (canonicalValidityGateTrace start wires).gates.length := by
    simp only [canonicalValidityGateTrace, List.length_append,
      CircuitBuilder.conjunctionGateTrace_wire_eq,
      CircuitBuilder.conjunctionGateTrace_length]
    simp only [Nat.add_assoc]
  rw [canonicalValidityGateTrace_length] at hlast
  have hoff := validCfgOutputOffsetPolynomial_eval_add_one tm H
  rw [← hoff] at hlast
  have hcancel :
      (canonicalValidityGateTrace start wires).wire + 1 =
        (start + (validCfgOutputOffsetPolynomial tm).eval H) + 1 := by
    simpa only [Nat.add_assoc] using hlast
  exact Nat.add_right_cancel hcancel

/-- Every family output occupies the last wire of its row-local validity
block. -/
theorem validCfgCircuitFamilyGateTrace_output_eq
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (start : Nat) (rows : Fin n → CfgWires tm H) (row : Fin n) :
    (validCfgCircuitFamilyGateTrace start n rows).outputs row =
      start + row.val * validCfgGateCost tm H +
        (validCfgOutputOffsetPolynomial tm).eval H := by
  induction n with
  | zero => exact Fin.elim0 row
  | succ n ih =>
      let prefixRows : Fin n → CfgWires tm H :=
        fun index => rows index.castSucc
      simp only [validCfgCircuitFamilyGateTrace]
      split
      next hrow =>
        simpa [prefixRows, Nat.add_assoc] using
          ih prefixRows ⟨row.val, hrow⟩
      next hrow =>
        have hlastRow : row = Fin.last n := by
          apply Fin.ext
          simp
          omega
        subst row
        rw [canonicalValidityGateTrace_wire_eq_start_add_offset]
        simp only [validCfgCircuitFamilyGateTrace_length, Fin.val_last]

/-- Closed coordinate of every semantic verifier-validity output. -/
theorem verifierValidity_output_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) :
    (verifierValidity W input).outputs row =
      tableauInputCount W.machine.tm
          ((verifierHeight W).eval input.length)
          ((verifierHorizon W).eval input.length) + 2 +
        row.val * validCfgGateCost W.machine.tm
          ((verifierHeight W).eval input.length) +
        (validCfgOutputOffsetPolynomial W.machine.tm).eval
          ((verifierHeight W).eval input.length) := by
  unfold verifierValidity verifierPool verifierRows
  dsimp only
  rw [validCfgCircuitFamily_output_eq_trace]
  rw [CircuitBuilder.allocateBoolWirePool_gate_delta,
    allocateTableauRows_gate_delta]
  simpa [tableauRowCount] using
    validCfgCircuitFamilyGateTrace_output_eq
      (tm := W.machine.tm)
      (H := (verifierHeight W).eval input.length)
      (tableauInputCount W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) + 2)
      (allocateTableauRows W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)).rows row

/-- Input-length polynomial for the last-wire offset of one verifier
validity row. -/
def verifierValidityOutputOffsetPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  (validCfgOutputOffsetPolynomial W.machine.tm).comp (verifierHeight W)

@[simp] theorem verifierValidityOutputOffsetPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierValidityOutputOffsetPolynomial W).eval n =
      (validCfgOutputOffsetPolynomial W.machine.tm).eval
        ((verifierHeight W).eval n) := by
  simp [verifierValidityOutputOffsetPolynomial, Polynomial.eval_comp]

end CLRS.Chapter34.Turing.CookLevin
