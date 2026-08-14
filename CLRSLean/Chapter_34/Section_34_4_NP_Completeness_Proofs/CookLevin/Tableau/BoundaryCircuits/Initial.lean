import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Static

/-!
# CLRS Section 34.4 - Exact concrete initial-row constraints

The concrete initial boundary is a total circuit constructor.  A fitting input
is compared against the complete canonical {lit}`Turing.initList` row.  An input
longer than the public row height returns the shared constant-false wire, so no
height premise is exported to the semantic theorem.

Main results:

- Definition {lit}`initialCfgCircuit`: total exact initial-row constraint.
- Theorem {lit}`initialCfgCircuit_eval_iff`: the output is true exactly for the
  complete {lit}`Turing.initList` configuration.
- Theorem {lit}`initialCfgCircuit_gate_delta`: exact conditional gate cost.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Total construction -/

/-- Exact gate cost of a concrete initial-row constraint.

Fitting inputs use complete-row equality; oversized inputs use the existing
false pool wire and emit no gates. -/
def initialCfgCircuitGateCost (tm : _root_.Turing.FinTM2) (H : Nat)
    (input : List (tm.Γ tm.k₀)) : Nat :=
  if input.length ≤ H then 6 * cfgBitCount tm H + 1 else 0

/-- Build a total concrete initial-row constraint.

The caller supplies a shared Boolean pool and an already allocated public row.
Every fixed target coordinate aliases the pool; only complete-row equality
emits gates.  Oversized inputs return a real constant-false output. -/
def initialCfgCircuit (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (input : List (tm.Γ tm.k₀)) :
    BoundaryCircuitResult base := by
  classical
  by_cases hfit : input.length ≤ H
  · let target := _root_.Turing.initList tm input
    let halphabet : CfgAlphabetBounded tm target :=
      initList_alphabetBounded tm input
    let hheight : ∀ k, (target.stk k).length ≤ H := by
      intro k
      by_cases hk : k = tm.k₀
      · subst k
        simpa [target, _root_.Turing.initList] using hfit
      · simp [target, _root_.Turing.initList, hk]
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    let equal := cfgEqBoundaryCircuit base row targetWires hrow
      (staticBoundedCfgWires_valid pool code)
    exact equal
  · exact falseBoundaryCircuit base pool

/-! ## Structural contracts -/

/-- Initial-row construction preserves the complete input builder prefix. -/
theorem initialCfgCircuit_extends (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (input : List (tm.Γ tm.k₀)) :
    base.Extends (initialCfgCircuit tm H base pool row hrow input).builder :=
  (initialCfgCircuit tm H base pool row hrow input).extension

/-- The concrete initial-boundary output belongs to its result builder. -/
theorem initialCfgCircuit_wireValid (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (input : List (tm.Γ tm.k₀)) :
    (initialCfgCircuit tm H base pool row hrow input).builder.WireValid
      (initialCfgCircuit tm H base pool row hrow input).wire :=
  (initialCfgCircuit tm H base pool row hrow input).valid

/-- The concrete initial boundary has its exact conditional gate delta. -/
theorem initialCfgCircuit_gate_delta (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (input : List (tm.Γ tm.k₀)) :
    (initialCfgCircuit tm H base pool row hrow input).builder.gates.length =
      base.gates.length + initialCfgCircuitGateCost tm H input :=
  by
    classical
    by_cases hfit : input.length ≤ H
    · let target := _root_.Turing.initList tm input
      let halphabet : CfgAlphabetBounded tm target :=
        initList_alphabetBounded tm input
      let hheight : ∀ k, (target.stk k).length ≤ H := by
        intro k
        by_cases hk : k = tm.k₀
        · subst k
          simpa [target, _root_.Turing.initList] using hfit
        · simp [target, _root_.Turing.initList, hk]
      let code := encodeCfg tm halphabet hheight
      let targetWires := staticBoundedCfgWires pool code
      have htargetValid : targetWires.ValidIn base :=
        staticBoundedCfgWires_valid pool code
      rw [show initialCfgCircuit tm H base pool row hrow input =
          cfgEqBoundaryCircuit base row targetWires hrow htargetValid by
        simp only [initialCfgCircuit, hfit]
        rfl]
      change (cfgEq base row targetWires hrow htargetValid).builder.gates.length =
        base.gates.length + initialCfgCircuitGateCost tm H input
      simpa [initialCfgCircuitGateCost, hfit] using
        cfgEq_gate_delta base row targetWires hrow htargetValid
    · rw [show initialCfgCircuit tm H base pool row hrow input =
          falseBoundaryCircuit base pool by
        simp only [initialCfgCircuit, hfit]
        rfl]
      change base.gates.length =
        base.gates.length + initialCfgCircuitGateCost tm H input
      simp [initialCfgCircuitGateCost, hfit]

/-- Initial-row construction is independent of row-validity proof choices. -/
theorem initialCfgCircuit_proof_irrel (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow₁ hrow₂ : row.ValidIn base)
    (input : List (tm.Γ tm.k₀)) :
    initialCfgCircuit tm H base pool row hrow₁ input =
      initialCfgCircuit tm H base pool row hrow₂ input := by
  rfl

/-! ## Exact semantics -/

/-- The total concrete initial constraint accepts exactly the complete
{lit}`Turing.initList` row.  In particular, oversized inputs are rejected by an
actual false circuit output instead of an external fit premise. -/
theorem initialCfgCircuit_eval_iff_of_decoded
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (row : CfgWires tm H)
    (hrow : row.ValidIn base) (input : List (tm.Γ tm.k₀)) {c : tm.Cfg}
    (hdecoded : evalBundle base inputs row hrow = some c) :
    (initialCfgCircuit tm H base pool row hrow input).builder.evalWire inputs
        (initialCfgCircuit tm H base pool row hrow input).wire = true ↔
      c = _root_.Turing.initList tm input := by
  classical
  by_cases hfit : input.length ≤ H
  · let target := _root_.Turing.initList tm input
    let halphabet : CfgAlphabetBounded tm target :=
      initList_alphabetBounded tm input
    let hheight : ∀ k, (target.stk k).length ≤ H := by
      intro k
      by_cases hk : k = tm.k₀
      · subst k
        simpa [target, _root_.Turing.initList] using hfit
      · simp [target, _root_.Turing.initList, hk]
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    have htargetValid : targetWires.ValidIn base :=
      staticBoundedCfgWires_valid pool code
    have htargetDecoded :
        evalBundle base inputs targetWires htargetValid = some target := by
      apply evalBundle_encodeCfg base inputs targetWires htargetValid
        halphabet hheight
      exact staticBoundedCfgWires_eval pool inputs code
    rw [show initialCfgCircuit tm H base pool row hrow input =
        cfgEqBoundaryCircuit base row targetWires hrow htargetValid by
      simp only [initialCfgCircuit, hfit]
      rfl]
    exact cfgEqBoundaryCircuit_eval_iff_decoded base row targetWires hrow
      htargetValid inputs hdecoded htargetDecoded
  · have htall : H < input.length := Nat.lt_of_not_ge hfit
    have hne : c ≠ _root_.Turing.initList tm input := by
      intro heq
      subst c
      rcases evalBundle_eq_some_canonical base inputs row hrow
          (_root_.Turing.initList tm input) hdecoded with ⟨_, hheight, _⟩
      have hk0 := hheight tm.k₀
      simp [_root_.Turing.initList] at hk0
      omega
    rw [show initialCfgCircuit tm H base pool row hrow input =
        falseBoundaryCircuit base pool by
      simp only [initialCfgCircuit, hfit]
      rfl]
    simp [falseBoundaryCircuit_eval, hne]

/-- The total concrete initial constraint is true exactly when the public row
decodes to the complete canonical {lit}`Turing.initList` target.  This stronger
form also rejects every malformed row without a decoding premise. -/
theorem initialCfgCircuit_eval_iff
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (row : CfgWires tm H)
    (hrow : row.ValidIn base) (input : List (tm.Γ tm.k₀)) :
    (initialCfgCircuit tm H base pool row hrow input).builder.evalWire inputs
        (initialCfgCircuit tm H base pool row hrow input).wire = true ↔
      evalBundle base inputs row hrow =
        some (_root_.Turing.initList tm input) := by
  classical
  by_cases hfit : input.length ≤ H
  · let target := _root_.Turing.initList tm input
    let halphabet : CfgAlphabetBounded tm target :=
      initList_alphabetBounded tm input
    let hheight : ∀ k, (target.stk k).length ≤ H := by
      intro k
      by_cases hk : k = tm.k₀
      · subst k
        simpa [target, _root_.Turing.initList] using hfit
      · simp [target, _root_.Turing.initList, hk]
    let code := encodeCfg tm halphabet hheight
    let targetWires := staticBoundedCfgWires pool code
    have htargetValid : targetWires.ValidIn base :=
      staticBoundedCfgWires_valid pool code
    rw [show initialCfgCircuit tm H base pool row hrow input =
        cfgEqBoundaryCircuit base row targetWires hrow htargetValid by
      simp only [initialCfgCircuit, hfit]
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
  · rw [show initialCfgCircuit tm H base pool row hrow input =
        falseBoundaryCircuit base pool by
      simp only [initialCfgCircuit, hfit]
      rfl]
    constructor
    · intro htrue
      rw [falseBoundaryCircuit_eval] at htrue
      contradiction
    · intro hdecoded
      rcases evalBundle_eq_some_canonical base inputs row hrow
          (_root_.Turing.initList tm input) hdecoded with ⟨_, hheight, _⟩
      have hk0 := hheight tm.k₀
      simp [_root_.Turing.initList] at hk0
      omega

end

end CLRS.Chapter34.Turing.CookLevin
