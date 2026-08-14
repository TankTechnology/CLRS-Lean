import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate

/-!
# Exact Cook--Levin circuit header

The serialized verifier circuit starts with the unary encoding of its exact
external-input arity.  This module derives an exact fixed-machine polynomial
for one tableau-row width, composes it with the verifier height and horizon,
and instantiates the verified exact-polynomial clock.  The resulting concrete
TM2 emits precisely the `encNat` prefix of `encodeCircuit (verifierCircuit W x)`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing
open PolyBuilder

/-! ## Exact row-width and tableau-arity polynomials -/

/-- Exact affine polynomial for the Boolean width of one configuration row. -/
def cfgBitPolynomial (tm : _root_.Turing.FinTM2) : Polynomial Nat := by
  letI : Fintype tm.K := tm.kFin
  exact Polynomial.C
      (1 + (labelCount tm + 1) + stateCount tm + Fintype.card tm.K) +
    Polynomial.C
      (∑ k : tm.K, ((reachableAlphabet tm k).card + 2)) * Polynomial.X

/-- Evaluating the affine row-width polynomial gives the semantic codec width
exactly, not merely an upper bound. -/
@[simp] theorem cfgBitPolynomial_eval (tm : _root_.Turing.FinTM2) (H : Nat) :
    (cfgBitPolynomial tm).eval H = cfgBitCount tm H := by
  letI : Fintype tm.K := tm.kFin
  simp only [cfgBitPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold cfgBitCount
  rw [show (∑ k : tm.K,
      ((H + 1) + H * ((reachableAlphabet tm k).card + 1))) =
      Fintype.card tm.K +
        H * (∑ k : tm.K, ((reachableAlphabet tm k).card + 2)) by
    calc
      (∑ k : tm.K,
          ((H + 1) + H * ((reachableAlphabet tm k).card + 1))) =
          ∑ k : tm.K,
            (1 + H * ((reachableAlphabet tm k).card + 2)) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = Fintype.card tm.K +
          H * (∑ k : tm.K, ((reachableAlphabet tm k).card + 2)) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · simp
            · symm
              exact Finset.mul_sum Finset.univ
                (fun k : tm.K => (reachableAlphabet tm k).card + 2) H]
  ring

/-- Exact polynomial for the complete public tableau input arity. -/
def verifierTableauInputPolynomial {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  (verifierHorizon W + 1) *
    (cfgBitPolynomial W.machine.tm).comp (verifierHeight W)

/-- The tableau-arity polynomial agrees exactly with the semantic layout. -/
@[simp] theorem verifierTableauInputPolynomial_eval {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTableauInputPolynomial W).eval n =
      tableauInputCount W.machine.tm
        ((verifierHeight W).eval n) ((verifierHorizon W).eval n) := by
  simp [verifierTableauInputPolynomial, tableauInputCount, tableauRowCount,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]

/-! ## Exact unary arity clock and serialized header -/

/-- Unit clock whose length is the exact tableau input arity. -/
def verifierTableauInputClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierTableauInputPolynomial W) input

@[simp] theorem verifierTableauInputClock_length {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierTableauInputClock W input).length =
      tableauInputCount W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) := by
  simp [verifierTableauInputClock]

/-- Concrete polynomial-time implementation of the exact tableau-input clock. -/
noncomputable def verifierTableauInputClock_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierTableauInputClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime
    (verifierTableauInputPolynomial W)

/-- Exact serialized input-arity prefix of the verifier circuit. -/
def verifierCircuitHeader {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  encNat (verifierTableauInputClock W input).length

/-- The generated header is definitionally tied to the closed semantic
circuit's declared input count. -/
theorem verifierCircuitHeader_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitHeader W input =
      encNat (verifierCircuit W input).inputCount := by
  simp [verifierCircuitHeader, verifierCircuit_inputCount]

/-- Concrete polynomial-time machine for the exact verifier-circuit header. -/
noncomputable def verifierCircuitHeader_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierCircuitHeader W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (verifierTableauInputClock_computableInPolyTime W)
    (lengthEncoding_computableInPolyTime Unit)
  change TM2ComputableInPolyTime id id
    ((fun input : List Unit => encNat input.length) ∘
      verifierTableauInputClock W)
  exact Classical.choice composed

/-! ## Exact initial input-gate family -/

/-- Serialized gates allocated for every public tableau bit, in semantic
builder order. -/
def verifierInputGateStream {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  inputGateStream (verifierTableauInputClock W input).length

/-- The streamed family is exactly the encoding of the gates produced by the
existing proof-carrying tableau allocator. -/
theorem verifierInputGateStream_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierInputGateStream W input =
      (verifierRows W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierRows, allocateTableauRows_gates_eq]
  rw [List.flatMap_map]
  simp [verifierInputGateStream, inputGateStream_eq]

/-- Concrete polynomial-time machine for the exact initial input-gate family. -/
noncomputable def verifierInputGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierInputGateStream W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (verifierTableauInputClock_computableInPolyTime W)
    inputGateStream_computableInPolyTime
  change TM2ComputableInPolyTime id id
    ((fun clock : List Unit => inputGateStream clock.length) ∘
      verifierTableauInputClock W)
  exact Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
