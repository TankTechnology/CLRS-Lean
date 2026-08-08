import Mathlib.Tactic
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility

/-!
# CIRCUIT-SAT poly-reduces to SAT

The reduction of CLRS Lemma 34.6: a boolean circuit is satisfiable iff the
boolean formula obtained by asserting the consistency of every gate (and the
output) is satisfiable.  The construction introduces a variable per wire and
one `↔`-formula per gate.

Main results:

- Model `Formula` (variables, constants, `not`/`and`/`or`/`iff`) with
  evaluation `Formula.eval` and `satisfiable`.
- Model `Gate` (input, constant, `not`/`and`/`or`) and a circuit as a list of
  gates, with wire evaluation `evalWire` and `circuitSatisfiable`.
- The reduction `circuitToFormula`, and the correctness theorem
  `circuitSatisfiable_iff_satisfiable_circuitToFormula` (Lemma 34.6, the
  semantic half).

**Current gap**: the polynomial-time machine computing the reduction (the
list encoding of `circuitToFormula` over `FormulaSym`) is not yet built, so
`PolyTimeReducible CIRCUIT_SAT SAT` is not yet assembled.  The semantic
equivalence above is the mathematical core.

Design (offset wires so every gate has two predecessors):

- Wire `0` and wire `1` are the circuit's input wires (their value is chosen
  by the assignment `σ`).
- Gate `i` (0-indexed) produces wire `i + 2`, whose inputs are wires
  `i + 1` and `i`.  So a circuit with `n` gates has wires `0..n+1`, and the
  output is the last wire `n + 1`.
- `circuitToFormula gates` is `x_{n+1} ∧ ⋀ᵢ (x_{i+2} ↔ gateExprᵢ)`, where
  `gateExprᵢ` is the value of gate `i` in terms of wires `i+1` and `i`.

With this offset, every wire referenced by a gate exists, so the equivalence
holds for **every** gate list (no well-formedness side condition).
-/

namespace CLRS

namespace Chapter34

/-- A boolean formula: variables indexed by `Nat`, constants, and the standard
connectives (including `↔`, used by the reduction). -/
inductive Formula : Type
  | var (i : Nat)
  | const (b : Bool)
  | not (f : Formula)
  | and (f g : Formula)
  | or (f g : Formula)
  | iff (f g : Formula)
deriving Repr, DecidableEq

namespace Formula

/-- Evaluate a formula under an assignment `σ : Nat → Bool` of its variables. -/
def eval : Formula → (Nat → Bool) → Bool
  | var i, σ => σ i
  | const b, σ => b
  | not f, σ => !eval f σ
  | and f g, σ => eval f σ && eval g σ
  | or f g, σ => eval f σ || eval g σ
  | iff f g, σ => eval f σ == eval g σ

/-- A formula is **satisfiable** when some assignment makes it true. -/
def Satisfiable (f : Formula) : Prop :=
  ∃ σ : Nat → Bool, eval f σ = true

end Formula

/-- A boolean circuit gate: an input wire, a constant, or a `not`/`and`/`or`
gate.  A circuit is a list of gates; gate `i` produces wire `i + 2`. -/
inductive Gate : Type
  | input
  | const (b : Bool)
  | not
  | and
  | or
deriving DecidableEq, Repr, Fintype, Inhabited

/-- The value of a circuit's gate `i` expressed as a formula in the two
predecessor wires `i + 1` and `i` (the wires feeding gate `i`). -/
def gateExpr (i : Nat) (g : Gate) : Formula :=
  match g with
  | Gate.input => Formula.var (i + 2)
  | Gate.const b => Formula.const b
  | Gate.not => Formula.not (Formula.var (i + 1))
  | Gate.and => Formula.and (Formula.var (i + 1)) (Formula.var i)
  | Gate.or => Formula.or (Formula.var (i + 1)) (Formula.var i)

/-- The value of wire `i` of a circuit, given an assignment `σ` to the input
wires `0` and `1`.  Wires `0`/`1` are the inputs; wire `i + 2` is gate `i`'s
output (and `false` when `i` is past the end of the gate list). -/
def evalWire (gates : List Gate) (σ : Nat → Bool) : Nat → Bool
  | 0 => σ 0
  | 1 => σ 1
  | i + 2 =>
      match gates[i]? with
      | none => false
      | some Gate.input => σ (i + 2)
      | some (Gate.const b) => b
      | some Gate.not => !evalWire gates σ (i + 1)
      | some Gate.and => evalWire gates σ (i + 1) && evalWire gates σ i
      | some Gate.or => evalWire gates σ (i + 1) || evalWire gates σ i

/-- The consistency formula for a gate: the gate's output wire equals the
value of its expression in the predecessor wires. -/
def gateFormula (i : Nat) (g : Gate) : Formula :=
  Formula.iff (Formula.var (i + 2)) (gateExpr i g)

/-- The conjunction of the consistency formulas of all gates, in gate order,
tracking the wire index. -/
def gateFormulasAux : Nat → List Gate → Formula
  | _, [] => Formula.const true
  | i, g :: rest => Formula.and (gateFormula i g) (gateFormulasAux (i + 1) rest)

/-- The conjunction of the consistency formulas of all gates, in gate order. -/
def gateFormulas (gates : List Gate) : Formula :=
  gateFormulasAux 0 gates

/-- A circuit is **satisfiable** when some assignment to the input wires makes
the output wire (the last wire, `gates.length + 1`) true. -/
def CircuitSatisfiable (gates : List Gate) : Prop :=
  ∃ σ : Nat → Bool, evalWire gates σ (gates.length + 1) = true

/--
**The CIRCUIT-SAT → SAT reduction** (CLRS Lemma 34.6).  Assert the output wire
and the consistency of every gate.
-/
def circuitToFormula (gates : List Gate) : Formula :=
  Formula.and (Formula.var (gates.length + 1)) (gateFormulas gates)

/-- The value of gate `i`'s output wire equals the evaluation of its
expression formula under the wire-value assignment. -/
lemma evalWire_eq_gateExpr (g : Gate) {gates : List Gate} {σ : Nat → Bool} {i : Nat}
    (h : gates[i]? = some g) :
    evalWire gates σ (i + 2) = Formula.eval (gateExpr i g) (evalWire gates σ) := by
  cases g with
  | input => simp [evalWire, gateExpr, Formula.eval, h]
  | const b => simp [evalWire, gateExpr, Formula.eval, h]
  | not => simp [evalWire, gateExpr, Formula.eval, h]
  | and => simp [evalWire, gateExpr, Formula.eval, h]
  | or => simp [evalWire, gateExpr, Formula.eval, h]

/-- For a wire that is actually produced by gate `i`, its value equals the
evaluation of the gate's expression formula under the wire-value assignment. -/
lemma evalWire_eq_gateExpr' {gates : List Gate} {σ : Nat → Bool} {i : Nat}
    (hi : i < gates.length) :
    evalWire gates σ (i + 2) = Formula.eval (gateExpr i (gates.get ⟨i, hi⟩)) (evalWire gates σ) := by
  exact evalWire_eq_gateExpr (gates.get ⟨i, hi⟩) (List.getElem?_eq_getElem hi)

/-- `Bool` equality reflected as `==` is true exactly when the values are equal. -/
lemma beq_true_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

/-- The `getElem?` at the boundary of `pre ++ g :: rest` is `g`. -/
lemma getElem?_append_cons (pre : List Gate) (g : Gate) (rest : List Gate) :
    (pre ++ g :: rest)[pre.length]? = some g := by
  rw [List.getElem?_append_right (Nat.le_refl pre.length)]
  simpa [Nat.sub_self]

/-- The conjunction of all gate-consistency formulas, from a suffix of the gate
list, evaluates to true under the wire-value assignment. -/
lemma eval_gateFormulasAux (pre rest : List Gate) (σ : Nat → Bool) :
    Formula.eval (gateFormulasAux pre.length rest) (evalWire (pre ++ rest) σ) = true := by
  induction rest generalizing pre with
  | nil => simp [gateFormulasAux, Formula.eval]
  | cons g rest' ih =>
      have hfirst : Formula.eval (gateFormula pre.length g) (evalWire (pre ++ g :: rest') σ) = true := by
        rw [gateFormula]
        simp [Formula.eval]
        rw [evalWire_eq_gateExpr g]
        · exact getElem?_append_cons pre g rest'
      have hrest : Formula.eval (gateFormulasAux (pre.length + 1) rest') (evalWire (pre ++ g :: rest') σ) = true := by
        have hih := ih (pre := pre ++ [g])
        simpa [List.length_append, List.append_assoc] using hih
      simp [gateFormulasAux, Formula.eval, hfirst, hrest]

/-- The conjunction of the consistency formulas of all gates evaluates to true
under the wire-value assignment. -/
lemma eval_gateFormulas (gates : List Gate) (σ : Nat → Bool) :
    Formula.eval (gateFormulas gates) (evalWire gates σ) = true := by
  simpa [gateFormulas] using (eval_gateFormulasAux [] gates σ)

/-- If the conjunction of gate formulas evaluates to true, then every individual
gate's consistency formula evaluates to true. -/
lemma eval_gateFormulasAux_true {τ : Nat → Bool} (i : Nat) : ∀ rest : List Gate,
    Formula.eval (gateFormulasAux i rest) τ = true →
      ∀ j : Nat, (hj : j < rest.length) → Formula.eval (gateFormula (i + j) (rest.get ⟨j, hj⟩)) τ = true := by
  intro rest
  induction rest generalizing i with
  | nil =>
      intro h j hj
      exfalso
      simpa using hj
  | cons g rest' ih =>
      intro h j hj
      cases j with
      | zero =>
          simp [gateFormulasAux, Formula.eval, Bool.and_eq_true] at h
          simpa using h.1
      | succ j' =>
          have hrest : Formula.eval (gateFormulasAux (i + 1) rest') τ = true := by
            simp [gateFormulasAux, Formula.eval, Bool.and_eq_true] at h
            exact h.2
          have hj' : j' < rest'.length := by simpa using hj
          have hgoal := ih (i := i + 1) hrest j' hj'
          have hidx : i + (j' + 1) = (i + 1) + j' := by omega
          have helt : (g :: rest').get ⟨j' + 1, hj⟩ = rest'.get ⟨j', hj'⟩ := by
            simpa [List.getElem_cons_succ]
          rw [hidx, helt]
          exact hgoal

/-- Under a satisfying assignment of `circuitToFormula gates`, every wire's value
matches the assignment's value for that variable. -/
lemma evalWire_eq_tau (gates : List Gate) (τ : Nat → Bool)
    (hτ : Formula.eval (circuitToFormula gates) τ = true) :
    ∀ j : Nat, j ≤ gates.length + 1 → evalWire gates τ j = τ j := by
  have hgf : Formula.eval (gateFormulas gates) τ = true := by
    rw [circuitToFormula] at hτ
    simp [Formula.eval, Bool.and_eq_true] at hτ
    exact hτ.2
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      match j with
      | 0 => simp [evalWire]
      | 1 => simp [evalWire]
      | i + 2 =>
          by_cases hi : i < gates.length
          · have hcons := eval_gateFormulasAux_true (τ := τ) 0 gates hgf i hi
            have hτi1 : evalWire gates τ (i + 1) = τ (i + 1) := ih (i + 1) (by omega) (by omega)
            have hτi : evalWire gates τ i = τ i := ih i (by omega) (by omega)
            cases g : gates.get ⟨i, hi⟩ with
            | input =>
                have hget : gates[i] = Gate.input := by simpa using g
                simp [evalWire, hget, List.getElem?_eq_getElem hi]
            | const b =>
                have hget : gates[i] = Gate.const b := by simpa using g
                have hgate : τ (i + 2) = b := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hgate, List.getElem?_eq_getElem hi]
            | not =>
                have hget : gates[i] = Gate.not := by simpa using g
                have hgate : τ (i + 2) = !τ (i + 1) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hgate, List.getElem?_eq_getElem hi]
            | and =>
                have hget : gates[i] = Gate.and := by simpa using g
                have hgate : τ (i + 2) = (τ (i + 1) && τ i) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hτi, hgate, List.getElem?_eq_getElem hi]
            | or =>
                have hget : gates[i] = Gate.or := by simpa using g
                have hgate : τ (i + 2) = (τ (i + 1) || τ i) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hτi, hgate, List.getElem?_eq_getElem hi]
          · exfalso
            omega

/--
**Theorem (CIRCUIT-SAT poly-reduces to SAT, semantic half, Lemma 34.6).**  A
circuit is satisfiable iff the formula asserting the output wire and the
consistency of every gate is satisfiable.
-/
theorem circuitSatisfiable_iff_satisfiable_circuitToFormula (gates : List Gate) :
    CircuitSatisfiable gates ↔ Formula.Satisfiable (circuitToFormula gates) := by
  constructor
  · intro ⟨σ, hσ⟩
    refine ⟨evalWire gates σ, ?_⟩
    rw [circuitToFormula]
    simp [Formula.eval, hσ, eval_gateFormulas]
  · intro ⟨τ, hτ⟩
    refine ⟨τ, ?_⟩
    have hwire := evalWire_eq_tau gates τ hτ (gates.length + 1) (by omega)
    rw [hwire]
    rw [circuitToFormula] at hτ
    simp [Formula.eval, Bool.and_eq_true] at hτ
    exact hτ.1

end Chapter34

end CLRS
