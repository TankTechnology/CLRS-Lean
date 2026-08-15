import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool

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

/-! ## Combined exact serialization prefix -/

/-- Exact serialized input-arity header followed by every canonical tableau
input gate. -/
def verifierCircuitInputPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  circuitInputPrefix (verifierTableauInputClock W input).length

/-- The combined stream agrees exactly with the corresponding semantic
prefix of the assembled verifier circuit. -/
theorem verifierCircuitInputPrefix_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitInputPrefix W input =
      encNat (verifierCircuit W input).inputCount ++
        (verifierRows W input).builder.gates.flatMap encodeCircuitGate := by
  change verifierCircuitHeader W input ++ verifierInputGateStream W input = _
  rw [verifierCircuitHeader_eq, verifierInputGateStream_eq]

/-- The initial row allocator is an actual append-only prefix of the final
conjunction builder. -/
private theorem verifierRows_extends_conjunction {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierRows W input).builder.Extends (verifierConjunction W input).1 := by
  let poolExtension := (verifierPool W input).extension
  let validityExtension := (verifierValidity W input).extension
  let transitionExtension := (verifierTransitions W input).extension
  let initialExtension := (verifierInitialBoundary W input).extension
  let inputExtension := (verifierInputBoundary W input).extension
  let acceptingExtension := (verifierAcceptingBoundary W input).extension
  let conjunctionExtension := CircuitBuilder.conjunction_extends
    (verifierAcceptingBoundary W input).builder
    (verifierConstraintWires W input) (verifierConstraintWires_valid W input)
  exact poolExtension.trans (validityExtension.trans
    (transitionExtension.trans (initialExtension.trans
      (inputExtension.trans (acceptingExtension.trans conjunctionExtension)))))

/-- The generated arity-and-input-gate stream is a literal list prefix of the
complete verifier-circuit encoding. -/
theorem verifierCircuitInputPrefix_isPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitInputPrefix W input <+:
      encodeCircuit (verifierCircuit W input) := by
  rcases (verifierRows_extends_conjunction W input) with
    ⟨_, suffix, hgates⟩
  refine ⟨suffix.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output, ?_⟩
  rw [verifierCircuitInputPrefix_eq]
  change _ = encNat (verifierCircuit W input).inputCount ++
    (verifierCircuit W input).gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output
  change (verifierCircuit W input).gates =
      (verifierRows W input).builder.gates ++ suffix at hgates
  rw [hgates, List.flatMap_append]
  simp only [List.append_assoc]

/-- Concrete polynomial-time machine for the exact combined serialization
prefix. -/
noncomputable def verifierCircuitInputPrefix_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierCircuitInputPrefix W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (verifierTableauInputClock_computableInPolyTime W)
    circuitInputPrefix_computableInPolyTime
  change TM2ComputableInPolyTime id id
    ((fun clock : List Unit => circuitInputPrefix clock.length) ∘
      verifierTableauInputClock W)
  exact Classical.choice composed

/-! ## Shared Boolean-pool extension -/

/-- Extend the exact input prefix by the unique shared false/true gates. -/
def verifierCircuitPoolPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  appendBoolPool (verifierCircuitInputPrefix W input)

/-- The extended stream agrees exactly with the semantic builder immediately
after allocating its shared Boolean pool. -/
theorem verifierCircuitPoolPrefix_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitPoolPrefix W input =
      encNat (verifierCircuit W input).inputCount ++
        (verifierPool W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierCircuitPoolPrefix, appendBoolPool,
    verifierCircuitInputPrefix_eq]
  rw [verifierPool, CircuitBuilder.allocateBoolWirePool_gates_eq,
    List.flatMap_append]
  simp [boolPoolGateStream, encodeCircuitGate, List.append_assoc]

/-- The pool builder remains an append-only prefix of the final conjunction
builder. -/
private theorem verifierPool_extends_conjunction {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierPool W input).builder.Extends (verifierConjunction W input).1 := by
  let validityExtension := (verifierValidity W input).extension
  let transitionExtension := (verifierTransitions W input).extension
  let initialExtension := (verifierInitialBoundary W input).extension
  let inputExtension := (verifierInputBoundary W input).extension
  let acceptingExtension := (verifierAcceptingBoundary W input).extension
  let conjunctionExtension := CircuitBuilder.conjunction_extends
    (verifierAcceptingBoundary W input).builder
    (verifierConstraintWires W input) (verifierConstraintWires_valid W input)
  exact validityExtension.trans (transitionExtension.trans
    (initialExtension.trans (inputExtension.trans
      (acceptingExtension.trans conjunctionExtension))))

/-- The header, tableau inputs, and Boolean pool form a literal prefix of the
complete verifier-circuit encoding. -/
theorem verifierCircuitPoolPrefix_isPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitPoolPrefix W input <+:
      encodeCircuit (verifierCircuit W input) := by
  rcases (verifierPool_extends_conjunction W input) with
    ⟨_, suffix, hgates⟩
  refine ⟨suffix.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output, ?_⟩
  rw [verifierCircuitPoolPrefix_eq]
  change _ = encNat (verifierCircuit W input).inputCount ++
    (verifierCircuit W input).gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output
  change (verifierCircuit W input).gates =
      (verifierPool W input).builder.gates ++ suffix at hgates
  rw [hgates, List.flatMap_append]
  simp only [List.append_assoc]

/-- Concrete polynomial-time machine for the exact prefix through shared
constant allocation. -/
noncomputable def verifierCircuitPoolPrefix_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierCircuitPoolPrefix W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (verifierCircuitInputPrefix_computableInPolyTime W)
    appendBoolPool_computableInPolyTime
  change TM2ComputableInPolyTime id id
    (appendBoolPool ∘ verifierCircuitInputPrefix W)
  exact Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
