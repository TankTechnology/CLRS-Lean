import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Initial

/-!
# CLRS Section 34.4 - Exact accepting-output constraints

Acceptance is equality with the complete canonical {lit}`Turing.haltList` row:
reserved halted label, explicit halted bit, initial state, exact output stack,
and every other stack empty.  Unsupported or oversized outputs produce a real
constant-false constraint.

Main results:

- Definition {lit}`acceptingOutputCircuit`: total exact accepting constraint.
- Theorem {lit}`acceptingOutputCircuit_eval_iff`: exact complete-row semantics.
- Theorem {lit}`acceptingOutputCircuit_gate_delta`: exact conditional cost.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Target admissibility -/

/-- The requested output is encodable in the fixed finite row alphabet and
fits the public height. -/
def AcceptingOutputFits (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) : Prop :=
  (∀ a, a ∈ output → a ∈ reachableAlphabet tm tm.k₁) ∧ output.length ≤ H

noncomputable instance acceptingOutputFitsDecidable
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) : Decidable (AcceptingOutputFits tm H output) :=
  Classical.dec _

/-- An admissible requested output makes the complete halt target
alphabet-bounded. -/
theorem haltList_alphabetBounded_of_fits
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) (hfit : AcceptingOutputFits tm H output) :
    CfgAlphabetBounded tm (_root_.Turing.haltList tm output) := by
  intro k a ha
  by_cases hk : k = tm.k₁
  · subst k
    exact hfit.1 a (by simpa [_root_.Turing.haltList] using ha)
  · simp [_root_.Turing.haltList, hk] at ha

/-- Every stack of an admissible complete halt target fits the public height. -/
theorem haltList_height_of_fits
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) (hfit : AcceptingOutputFits tm H output) :
    ∀ k, ((_root_.Turing.haltList tm output).stk k).length ≤ H := by
  intro k
  by_cases hk : k = tm.k₁
  · subst k
    simpa [_root_.Turing.haltList] using hfit.2
  · simp [_root_.Turing.haltList, hk]

/-! ## Total construction -/

/-- Exact gate cost of the total accepting-output constraint. -/
def acceptingOutputCircuitGateCost (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) : Nat :=
  if AcceptingOutputFits tm H output then 6 * cfgBitCount tm H + 1 else 0

/-- Compare a public row with the complete canonical halt target, or emit a
constant-false output when that target cannot be represented at this height. -/
def acceptingOutputCircuit (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (output : List (tm.Γ tm.k₁)) : BoundaryCircuitResult base := by
  classical
  by_cases hfit : AcceptingOutputFits tm H output
  · let target := _root_.Turing.haltList tm output
    let halphabet := haltList_alphabetBounded_of_fits tm H output hfit
    let hheight := haltList_height_of_fits tm H output hfit
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    exact cfgEqBoundaryCircuit base row targetWires hrow
      (staticBoundedCfgWires_valid pool code)
  · exact falseBoundaryCircuit base pool

/-! ## Structural contracts -/

theorem acceptingOutputCircuit_extends
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (output : List (tm.Γ tm.k₁)) :
    base.Extends (acceptingOutputCircuit tm H base pool row hrow output).builder :=
  (acceptingOutputCircuit tm H base pool row hrow output).extension

theorem acceptingOutputCircuit_wireValid
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (output : List (tm.Γ tm.k₁)) :
    (acceptingOutputCircuit tm H base pool row hrow output).builder.WireValid
      (acceptingOutputCircuit tm H base pool row hrow output).wire :=
  (acceptingOutputCircuit tm H base pool row hrow output).valid

theorem acceptingOutputCircuit_gate_delta
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (output : List (tm.Γ tm.k₁)) :
    (acceptingOutputCircuit tm H base pool row hrow output).builder.gates.length =
      base.gates.length + acceptingOutputCircuitGateCost tm H output := by
  classical
  by_cases hfit : AcceptingOutputFits tm H output
  · let target := _root_.Turing.haltList tm output
    let halphabet := haltList_alphabetBounded_of_fits tm H output hfit
    let hheight := haltList_height_of_fits tm H output hfit
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    have htargetValid : targetWires.ValidIn base :=
      staticBoundedCfgWires_valid pool code
    rw [show acceptingOutputCircuit tm H base pool row hrow output =
        cfgEqBoundaryCircuit base row targetWires hrow htargetValid by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    change (cfgEq base row targetWires hrow htargetValid).builder.gates.length =
      base.gates.length + acceptingOutputCircuitGateCost tm H output
    simpa [acceptingOutputCircuitGateCost, hfit] using
      cfgEq_gate_delta base row targetWires hrow htargetValid
  · rw [show acceptingOutputCircuit tm H base pool row hrow output =
        falseBoundaryCircuit base pool by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    change base.gates.length =
      base.gates.length + acceptingOutputCircuitGateCost tm H output
    simp [acceptingOutputCircuitGateCost, hfit]

theorem acceptingOutputCircuit_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow₁ hrow₂ : row.ValidIn base)
    (output : List (tm.Γ tm.k₁)) :
    acceptingOutputCircuit tm H base pool row hrow₁ output =
      acceptingOutputCircuit tm H base pool row hrow₂ output := by
  rfl

/-! ## Exact complete-row semantics -/

/-- The accepting output is true exactly when the public row successfully
decodes to the complete {lit}`Turing.haltList` target.  Unsupported, oversized,
and malformed rows are all rejected by the generated circuit. -/
theorem acceptingOutputCircuit_eval_iff
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (row : CfgWires tm H)
    (hrow : row.ValidIn base) (output : List (tm.Γ tm.k₁)) :
    (acceptingOutputCircuit tm H base pool row hrow output).builder.evalWire
        inputs (acceptingOutputCircuit tm H base pool row hrow output).wire =
      true ↔
      evalBundle base inputs row hrow =
        some (_root_.Turing.haltList tm output) := by
  classical
  by_cases hfit : AcceptingOutputFits tm H output
  · let target := _root_.Turing.haltList tm output
    let halphabet := haltList_alphabetBounded_of_fits tm H output hfit
    let hheight := haltList_height_of_fits tm H output hfit
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    have htargetValid : targetWires.ValidIn base :=
      staticBoundedCfgWires_valid pool code
    rw [show acceptingOutputCircuit tm H base pool row hrow output =
        cfgEqBoundaryCircuit base row targetWires hrow htargetValid by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    rw [cfgEqBoundaryCircuit_eval_iff]
    constructor
    · intro hbits
      apply evalBundle_encodeCfg base inputs row hrow halphabet hheight
      rw [hbits]
      exact staticBoundedCfgWires_eval pool inputs code
    · intro hdecoded
      rcases evalBundle_eq_some_canonical base inputs row hrow target
          hdecoded with ⟨hactualAlphabet, hactualHeight, hbits⟩
      have halphabetProof : hactualAlphabet = halphabet := Subsingleton.elim _ _
      subst hactualAlphabet
      have hheightProof : hactualHeight = hheight := Subsingleton.elim _ _
      subst hactualHeight
      rw [hbits]
      exact (staticBoundedCfgWires_eval pool inputs code).symm
  · rw [show acceptingOutputCircuit tm H base pool row hrow output =
        falseBoundaryCircuit base pool by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    constructor
    · intro htrue
      rw [falseBoundaryCircuit_eval] at htrue
      contradiction
    · intro hdecoded
      rcases evalBundle_eq_some_canonical base inputs row hrow
          (_root_.Turing.haltList tm output) hdecoded with
        ⟨halphabet, hheight, _⟩
      exfalso
      apply hfit
      constructor
      · intro a ha
        exact halphabet tm.k₁ a (by
          simpa [_root_.Turing.haltList] using ha)
      · have hk1 := hheight tm.k₁
        simpa [_root_.Turing.haltList] using hk1

end

end CLRS.Chapter34.Turing.CookLevin
