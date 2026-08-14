import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Arms

/-!
# Polynomial-size verifier-input shape circuit

This structural layer constrains the designated input stack by enumerating
only admissible certificate lengths.  It never enumerates certificate
contents.  Semantic characterization is deliberately left to the sibling
semantics layer.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Exact cost: one prebuilt separator NOT per cell, one conjunction per
fitting length arm, and a final disjunction over all length arms. -/
def verifierInputShapeGateCost {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ) : Nat :=
  H + (∑ length : Fin (W.certificateBound.eval x.length + 1),
    verifierInputArmGateCost H x.length length.val) +
      (W.certificateBound.eval x.length + 2)

/-- Proof-carrying output of the verifier-input shape circuit. -/
structure VerifierInputShapeResult (base : CircuitBuilder) (gateCost : Nat) where
  builder : CircuitBuilder
  wire : CircuitBuilder.Wire
  extension : base.Extends builder
  valid : builder.WireValid wire
  gate_delta : builder.gates.length = base.gates.length + gateCost

/-- Build the certificate-shaped input-stack constraint using one more length
arm than the certificate bound; certificate symbols are never enumerated. -/
def verifierInputShapeCircuit {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ) :
    VerifierInputShapeResult base (verifierInputShapeGateCost W H x) := by
  let separatorNots := VerifierInput.buildSeparatorNots base inputStack
    hinputStack (verifierInputCode W none)
  let pool' := pool.mono separatorNots.extension
  let hstack' := hinputStack.mono separatorNots.extension
  let bound := W.certificateBound.eval x.length
  let arms := VerifierInput.buildInputArms W H x separatorNots.builder pool'
    inputStack hstack' separatorNots.wires separatorNots.valid
      (fun inputs cell => by
        rw [separatorNots.eval, separatorNots.extension.evalWire_eq inputs
          (hinputStack.cell cell (verifierInputCode W none))]) (bound + 1)
  let armList := List.ofFn arms.wires
  have harmList : ∀ wire ∈ armList, arms.builder.WireValid wire := by
    intro wire hwire
    simp only [armList, List.mem_ofFn] at hwire
    rcases hwire with ⟨arm, rfl⟩
    exact arms.valid arm
  let output := arms.builder.disjunction armList harmList
  exact
    { builder := output.1
      wire := output.2
      extension := separatorNots.extension.trans (arms.extension.trans
        (CircuitBuilder.disjunction_extends arms.builder armList harmList))
      valid := CircuitBuilder.disjunction_wireValid arms.builder armList harmList
      gate_delta := by
        rw [CircuitBuilder.disjunction_gate_delta, arms.gate_delta,
          separatorNots.gate_delta]
        simp only [armList, List.length_ofFn, bound,
          verifierInputShapeGateCost]
        omega }

theorem verifierInputShapeCircuit_extends {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ) :
    base.Extends (verifierInputShapeCircuit W H base pool inputStack
      hinputStack x).builder :=
  (verifierInputShapeCircuit W H base pool inputStack hinputStack x).extension

theorem verifierInputShapeCircuit_wireValid {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ) :
    (verifierInputShapeCircuit W H base pool inputStack hinputStack x).builder.WireValid
      (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire :=
  (verifierInputShapeCircuit W H base pool inputStack hinputStack x).valid

theorem verifierInputShapeCircuit_gate_delta {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ) :
    (verifierInputShapeCircuit W H base pool inputStack hinputStack x).builder.gates.length =
      base.gates.length + verifierInputShapeGateCost W H x :=
  (verifierInputShapeCircuit W H base pool inputStack hinputStack x).gate_delta

/-- Structural evaluation hook: the final OR accepts exactly when one
certificate length up to the published bound satisfies its shape arm. -/
theorem verifierInputShapeCircuit_eval_iff_exists_length
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) :
    let result := verifierInputShapeCircuit W H base pool inputStack
      hinputStack x
    result.builder.evalWire inputs result.wire = true ↔
      ∃ length, length ≤ W.certificateBound.eval x.length ∧
        VerifierInputArmMatches W H x
          (evalStackBits base inputs inputStack) length := by
  unfold verifierInputShapeCircuit
  dsimp only
  rw [CircuitBuilder.disjunction_eval, List.any_eq_true]
  constructor
  · rintro ⟨wire, hwire, htrue⟩
    simp only [List.mem_ofFn] at hwire
    rcases hwire with ⟨arm, rfl⟩
    refine ⟨arm.val, by omega, ?_⟩
    let separatorNots := VerifierInput.buildSeparatorNots base inputStack
      hinputStack (verifierInputCode W none)
    let arms := VerifierInput.buildInputArms W H x separatorNots.builder
      (pool.mono separatorNots.extension) inputStack
      (hinputStack.mono separatorNots.extension) separatorNots.wires
      separatorNots.valid (fun inputs cell => by
        rw [separatorNots.eval, separatorNots.extension.evalWire_eq inputs
          (hinputStack.cell cell (verifierInputCode W none))])
      (W.certificateBound.eval x.length + 1)
    change arms.builder.evalWire inputs (arms.wires arm) = true at htrue
    have hmatches := (arms.eval_true_iff inputs arm).mp htrue
    rwa [evalStackBits_extends separatorNots.extension inputs inputStack
      hinputStack] at hmatches
  · rintro ⟨length, hlength, hmatches⟩
    let arm : Fin (W.certificateBound.eval x.length + 1) :=
      ⟨length, by omega⟩
    refine ⟨_, by exact List.mem_ofFn.mpr ⟨arm, rfl⟩, ?_⟩
    let separatorNots := VerifierInput.buildSeparatorNots base inputStack
      hinputStack (verifierInputCode W none)
    let arms := VerifierInput.buildInputArms W H x separatorNots.builder
      (pool.mono separatorNots.extension) inputStack
      (hinputStack.mono separatorNots.extension) separatorNots.wires
      separatorNots.valid (fun inputs cell => by
        rw [separatorNots.eval, separatorNots.extension.evalWire_eq inputs
          (hinputStack.cell cell (verifierInputCode W none))])
      (W.certificateBound.eval x.length + 1)
    change arms.builder.evalWire inputs (arms.wires arm) = true
    apply (arms.eval_true_iff inputs arm).mpr
    rwa [evalStackBits_extends separatorNots.extension inputs inputStack
      hinputStack]

theorem verifierInputShapeCircuit_proof_irrel {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack₁ hinputStack₂ : inputStack.ValidIn base) (x : List Γ) :
    verifierInputShapeCircuit W H base pool inputStack hinputStack₁ x =
      verifierInputShapeCircuit W H base pool inputStack hinputStack₂ x := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
