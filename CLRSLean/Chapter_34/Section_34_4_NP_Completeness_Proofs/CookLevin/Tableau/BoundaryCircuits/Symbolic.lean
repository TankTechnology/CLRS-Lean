import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Accepting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackCircuits

/-!
# CLRS Section 34.4 - Symbolic-input initial-row constraints

The Cook--Levin verifier cannot hard-code certificate-dependent input bits.
This module therefore constructs a complete canonical initial target whose
input stack is supplied by the caller as symbolic wires.  All control fields
and every non-input stack are pool-backed constants; only the designated input
stack remains symbolic.

Main results:

- Definition {lit}`symbolicInitialCfgWires`: complete symbolic initial target.
- Definition {lit}`symbolicInitialCfgCircuit`: complete-row equality constraint.
- Theorem {lit}`symbolicInitialCfgCircuit_eval_iff`: exact initial semantics
  from the symbolic stack's representation relation.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Complete symbolic target row -/

private theorem emptyInitialHeight (tm : _root_.Turing.FinTM2) (H : Nat) :
    ∀ k, ((_root_.Turing.initList tm []).stk k).length ≤ H := by
  intro k
  by_cases hk : k = tm.k₀
  · subst k
    simp [_root_.Turing.initList]
  · simp [_root_.Turing.initList, hk]

/-- Complete canonical initial row with an empty input stack. -/
noncomputable def emptyInitialCode (tm : _root_.Turing.FinTM2) (H : Nat) :
    BoundedCfg tm H :=
  encodeCfg tm (initList_alphabetBounded tm []) (emptyInitialHeight tm H)

/-- Complete symbolic initial target: canonical main label, nonhalted status,
initial state, caller-supplied input stack, and every other stack empty. -/
def symbolicInitialCfgWires (tm : _root_.Turing.FinTM2) (H : Nat)
    {base : CircuitBuilder} (pool : base.BoolWirePool)
    (inputStack : StackWires tm H tm.k₀) : CfgWires tm H :=
  (staticBoundedCfgWires pool (emptyInitialCode tm H)).replaceStack
    tm.k₀ inputStack

/-- The complete symbolic initial target is valid when its symbolic stack is. -/
theorem symbolicInitialCfgWires_valid
    (tm : _root_.Turing.FinTM2) (H : Nat)
    {base : CircuitBuilder} (pool : base.BoolWirePool)
    (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    (symbolicInitialCfgWires tm H pool inputStack).ValidIn base :=
  (staticBoundedCfgWires_valid pool (emptyInitialCode tm H)).replaceStack
    tm.k₀ hinputStack

/-- Evaluation exposes the symbolic input stack and fixes every other row
coordinate through the shared pool. -/
theorem symbolicInitialCfgWires_eval
    (tm : _root_.Turing.FinTM2) (H : Nat)
    {base : CircuitBuilder} (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (inputStack : StackWires tm H tm.k₀) :
    evalCfgBits base inputs (symbolicInitialCfgWires tm H pool inputStack) =
      (encodeRawCfgBits (emptyInitialCode tm H)).replaceStack tm.k₀
        (evalStackBits base inputs inputStack) := by
  rw [symbolicInitialCfgWires, evalCfgBits_replaceStack,
    staticBoundedCfgWires_eval]

/-- Transporting the shared pool leaves the complete symbolic target unchanged. -/
theorem symbolicInitialCfgWires_mono
    (tm : _root_.Turing.FinTM2) (H : Nat)
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (inputStack : StackWires tm H tm.k₀) :
    symbolicInitialCfgWires tm H (pool.mono hext) inputStack =
      symbolicInitialCfgWires tm H pool inputStack := by
  rfl

/-! ## Equality circuit -/

/-- Constrain a public first tableau row to equal the complete symbolic initial
target.  The symbolic stack is supplied by the caller and can therefore be
linked to certificate input bits by whole-tableau assembly. -/
def symbolicInitialCfgCircuit (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) : BoundaryCircuitResult base :=
  cfgEqBoundaryCircuit base row
    (symbolicInitialCfgWires tm H pool inputStack) hrow
    (symbolicInitialCfgWires_valid tm H pool inputStack hinputStack)

theorem symbolicInitialCfgCircuit_extends
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    base.Extends
      (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
        hinputStack).builder :=
  (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
    hinputStack).extension

theorem symbolicInitialCfgCircuit_wireValid
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
      hinputStack).builder.WireValid
      (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
        hinputStack).wire :=
  (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
    hinputStack).valid

/-- Symbolic initial equality emits one exact complete-row comparison. -/
theorem symbolicInitialCfgCircuit_gate_delta
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow : row.ValidIn base)
    (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
      hinputStack).builder.gates.length =
      base.gates.length + (6 * cfgBitCount tm H + 1) :=
  cfgEq_gate_delta base row (symbolicInitialCfgWires tm H pool inputStack)
    hrow (symbolicInitialCfgWires_valid tm H pool inputStack hinputStack)

theorem symbolicInitialCfgCircuit_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (row : CfgWires tm H) (hrow₁ hrow₂ : row.ValidIn base)
    (inputStack : StackWires tm H tm.k₀)
    (hinput₁ hinput₂ : inputStack.ValidIn base) :
    symbolicInitialCfgCircuit tm H base pool row hrow₁ inputStack hinput₁ =
      symbolicInitialCfgCircuit tm H base pool row hrow₂ inputStack hinput₂ := by
  rfl

/-! ## Semantic bridge -/

private theorem symbolicInitialCfgWires_evalBundle
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) (xs : List (tm.Γ tm.k₀))
    (hrep : (evalStackBits base inputs inputStack).Represents xs) :
    evalBundle base inputs (symbolicInitialCfgWires tm H pool inputStack)
        (symbolicInitialCfgWires_valid tm H pool inputStack hinputStack) =
      some (_root_.Turing.initList tm xs) := by
  rcases hrep.eq_encode with ⟨hstackAlphabet, hstackHeight, hstackBits⟩
  let target := _root_.Turing.initList tm xs
  let halphabet : CfgAlphabetBounded tm target := initList_alphabetBounded tm xs
  let hheight : ∀ k, (target.stk k).length ≤ H := by
    intro k
    by_cases hk : k = tm.k₀
    · subst k
      simpa [target, _root_.Turing.initList] using hstackHeight
    · simp [target, _root_.Turing.initList, hk]
  apply evalBundle_encodeCfg base inputs _ _ halphabet hheight
  rw [symbolicInitialCfgWires_eval, hstackBits]
  funext slot
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · rfl
  · rfl
  · rfl
  · by_cases hk : k = tm.k₀
    · subst k
      simp [CfgBundle.replaceStack, encodeRawCfgBits,
        encodeCfg, target, _root_.Turing.initList]
    · simp [CfgBundle.replaceStack, encodeRawCfgBits, emptyInitialCode,
        encodeCfg, target, _root_.Turing.initList, hk]
  · rcases cell with ⟨i, code⟩
    by_cases hk : k = tm.k₀
    · subst k
      simp [CfgBundle.replaceStack, encodeRawCfgBits,
        encodeCfg, target, _root_.Turing.initList]
    · simp [CfgBundle.replaceStack, encodeRawCfgBits, emptyInitialCode,
        encodeCfg, target, _root_.Turing.initList, hk]

/-- Under the caller's exact stack representation, symbolic initial equality
is true exactly when the public row decodes to the complete initial
configuration for that represented list. -/
theorem symbolicInitialCfgCircuit_eval_iff
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (row : CfgWires tm H)
    (hrow : row.ValidIn base) (inputStack : StackWires tm H tm.k₀)
    (hinputStack : inputStack.ValidIn base) (xs : List (tm.Γ tm.k₀))
    (hrep : (evalStackBits base inputs inputStack).Represents xs) :
    (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
      hinputStack).builder.evalWire inputs
        (symbolicInitialCfgCircuit tm H base pool row hrow inputStack
          hinputStack).wire = true ↔
      evalBundle base inputs row hrow =
        some (_root_.Turing.initList tm xs) := by
  let targetWires := symbolicInitialCfgWires tm H pool inputStack
  let htargetValid :=
    symbolicInitialCfgWires_valid tm H pool inputStack hinputStack
  have htargetDecoded :
      evalBundle base inputs targetWires htargetValid =
        some (_root_.Turing.initList tm xs) :=
    symbolicInitialCfgWires_evalBundle tm H base pool inputs inputStack
      hinputStack xs hrep
  change
    (cfgEqBoundaryCircuit base row targetWires hrow htargetValid).builder.evalWire
        inputs
        (cfgEqBoundaryCircuit base row targetWires hrow htargetValid).wire = true ↔
      evalBundle base inputs row hrow = some (_root_.Turing.initList tm xs)
  rw [cfgEqBoundaryCircuit_eval_iff]
  constructor
  · intro hbits
    have hsame : evalBundle base inputs row hrow =
        evalBundle base inputs targetWires htargetValid := by
      unfold evalBundle evalRawBundle
      rw [hbits]
    exact hsame.trans htargetDecoded
  · intro hdecoded
    rcases evalBundle_eq_some_canonical base inputs row hrow
        (_root_.Turing.initList tm xs) hdecoded with
      ⟨hrowAlphabet, hrowHeight, hrowBits⟩
    rcases evalBundle_eq_some_canonical base inputs targetWires htargetValid
        (_root_.Turing.initList tm xs) htargetDecoded with
      ⟨htargetAlphabet, htargetHeight, htargetBits⟩
    have halphabet : hrowAlphabet = htargetAlphabet := Subsingleton.elim _ _
    subst htargetAlphabet
    have hheight : hrowHeight = htargetHeight := Subsingleton.elim _ _
    subst htargetHeight
    rw [hrowBits, htargetBits]

end

end CLRS.Chapter34.Turing.CookLevin
