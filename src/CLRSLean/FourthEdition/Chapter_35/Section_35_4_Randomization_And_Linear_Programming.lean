import CLRSLean.FourthEdition.Chapter_35.Section_35_1_The_Vertex_Cover_Problem
import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# 35.4 Randomization and Linear Programming

This section formalizes the two approximation techniques of CLRS §35.4:
randomization and linear programming.  It covers (1) a randomized algorithm for
**MAX-3-CNF satisfiability** that achieves a randomized `8/7`-approximation
(Theorem 35.5), and (2) an LP-rounding algorithm **APPROX-MIN-WEIGHT-VC** that
achieves a factor-two approximation for the minimum-weight vertex-cover problem
(Theorem 35.6).

Main results:

- Definition `Literal`, `ClauseSatisfied`, `Is3CNFClause`: a MAX-3-CNF clause is
  a set of literals (variable/sign pairs), satisfied by an assignment when one
  of its literals holds.
- Lemma `unsatisfied_prob`: a uniformly random assignment leaves a valid 3-CNF
  clause unsatisfied with probability `1/8` — its three literals are over
  distinct variables, so exactly `2^(n-3)` of the `2^n` assignments take the
  negated value at each of them (`card_assignments_fixing_three`).
- Theorem `max3cnf_clause_satisfied_prob` (Theorem 35.5): the clause is
  satisfied with probability `7/8`.
- Theorem `max3cnf_expect_satisfied` (Theorem 35.5): the expected number of
  satisfied clauses over a family `F` is exactly `7/8 · |F|`, by linearity of
  expectation.
- Theorem `max3cnf_approx` (Theorem 35.5): MAX-3-CNF has a randomized
  `8/7`-approximation — every assignment is matched in expectation to at least
  `7/8` of the clauses it satisfies.
- Definition `IsFractionalCover`: the feasible region of the vertex-cover LP
  relaxation — a vector `x : V → ℚ` with `0 ≤ x v ≤ 1` and `x(u) + x(v) ≥ 1` for
  every edge.
- Definition `roundCover`: APPROX-MIN-WEIGHT-VC's rounding — the vertices with
  fractional value at least `1/2`.
- Theorem `roundCover_isVertexCover` (Theorem 35.6, correctness): the rounded
  vertices form a vertex cover.
- Theorem `approxMinWeightVC_two_approx` (Theorem 35.6): the rounded cover's
  weight is at most twice the LP objective, hence at most twice the optimal
  cover's weight — a factor-two approximation.

Notation conventions used in this section:

- `n` : the number of Boolean variables
- `σ` : an assignment `Fin n → Bool` (the sample space is uniform)
- `(i, b)` : the literal "variable `i` is set to `b`"
- `c` : a clause (a set of literals)
- `G` : an undirected graph (edge-based `Graph V E`)
- `w` : a positive vertex-weight function
- `x` : a fractional vertex cover (the LP relaxation's solution)
- `C` : a vertex cover
-/

noncomputable section

open Finset
open scoped BigOperators

namespace CLRS

namespace RandomizedLP

open CLRS.Probability

/-! ## Randomization: MAX-3-CNF satisfiability (Theorem 35.5)

A *literal* is a pair `(i, b)`: the assertion that variable `i` is set to `b`
(`true` for a positive literal, `false` for a negative one).  A *clause* is a
set of literals, satisfied by an assignment when at least one of its literals
holds.  The randomized algorithm sets every variable independently to `true`
with probability `1/2`; a clause with three literals over three distinct
variables is then satisfied with probability `7/8` (Theorem 35.5). -/

variable {n : ℕ}

/-- A **literal**: the assertion that variable `i` (of `n`) is set to `b`. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- An **assignment**: a setting of every variable to `true` or `false`. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A literal `(i, b)` **holds** under `σ` when `σ i = b`. -/
def litHolds (σ : Assignment n) (l : Literal n) : Prop :=
  σ l.1 = l.2

/-- A **clause** is satisfied by `σ` when at least one of its literals holds. -/
def ClauseSatisfied (c : Finset (Literal n)) (σ : Assignment n) : Prop :=
  ∃ l ∈ c, litHolds σ l

/-- A clause is **unsatisfied** by `σ` when none of its literals holds. -/
def ClauseUnsatisfied (c : Finset (Literal n)) (σ : Assignment n) : Prop :=
  ∀ l ∈ c, ¬ litHolds σ l

/-- Satisfaction of a clause over a finite set of literals is decidable. -/
instance decClauseSatisfied (c : Finset (Literal n)) (σ : Assignment n) :
    Decidable (ClauseSatisfied c σ) := by
  unfold ClauseSatisfied litHolds
  infer_instance

/-- Unsatisfaction of a clause over a finite set of literals is decidable. -/
instance decClauseUnsatisfied (c : Finset (Literal n)) (σ : Assignment n) :
    Decidable (ClauseUnsatisfied c σ) := by
  unfold ClauseUnsatisfied litHolds
  infer_instance

/-- A valid **MAX-3-CNF clause**: exactly three literals, over three distinct
variables (so no clause contains a variable and its negation). -/
def Is3CNFClause (c : Finset (Literal n)) : Prop :=
  c.card = 3 ∧ ∀ ⦃l₁ l₂ : Literal n⦄, l₁ ∈ c → l₂ ∈ c → l₁ ≠ l₂ → l₁.1 ≠ l₂.1

/-- A clause is satisfied iff it is not unsatisfied. -/
lemma clauseSatisfied_iff_not_unsatisfied (c : Finset (Literal n)) (σ : Assignment n) :
    ClauseSatisfied c σ ↔ ¬ ClauseUnsatisfied c σ := by
  unfold ClauseSatisfied ClauseUnsatisfied litHolds
  constructor
  · intro h hnone
    rcases h with ⟨l, hl, hlh⟩
    exact hnone l hl hlh
  · intro h
    by_contra hnone
    apply h
    intro l hl
    exact fun hlt => hnone ⟨l, hl, hlt⟩

/-- In `Bool`, `x ≠ b` holds exactly when `x` is the negation of `b`. -/
lemma bool_ne_iff_not (x b : Bool) : x ≠ b ↔ x = Bool.not b := by
  cases x <;> cases b <;> simp

/--
The number of assignments that fix the value of three distinct variables is
`2^(n-3)`: the remaining `n-3` variables are free.  This is the counting step of
Theorem 35.5 — a uniformly random assignment hits a given triple of values with
probability `2^(n-3) / 2^n = 1/8`.
-/
lemma card_assignments_fixing_three {i₁ i₂ i₃ : Fin n}
    (hi12 : i₁ ≠ i₂) (hi13 : i₁ ≠ i₃) (hi23 : i₂ ≠ i₃) {v₁ v₂ v₃ : Bool} :
    Fintype.card {σ : Assignment n // σ i₁ = v₁ ∧ σ i₂ = v₂ ∧ σ i₃ = v₃} = 2 ^ (n - 3) := by
  classical
  let C : Finset (Fin n) := {i₁, i₂, i₃}
  let Free : Type := {k : Fin n // k ∉ C}
  have hCcard : C.card = 3 := by
    dsimp [C]
    simp [hi12, hi13, hi23]
  have hfree : Fintype.card Free = n - 3 := by
    dsimp [Free, C]
    have hsub := Fintype.card_subtype_compl (fun k : Fin n => k ∈ C)
    rw [hsub]
    simp [hCcard, Fintype.card_fin]
  let e : {σ : Assignment n // σ i₁ = v₁ ∧ σ i₂ = v₂ ∧ σ i₃ = v₃} ≃ (Free → Bool) := {
    toFun := fun σ k => σ.1 k.1
    invFun := fun τ =>
      ⟨fun k => if h₁ : k = i₁ then v₁ else if h₂ : k = i₂ then v₂ else if h₃ : k = i₃ then v₃
        else τ ⟨k, by
          intro hkC
          simp [C] at hkC
          rcases hkC with h | h | h
          · exact h₁ h
          · exact h₂ h
          · exact h₃ h⟩,
        by
          dsimp
          constructor
          · simp
          · constructor
            · simp [hi12.symm]
            · simp [hi13.symm, hi23.symm]⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      funext k
      dsimp
      by_cases h₁ : k = i₁
      · subst k
        simp [σ.2.1]
      · by_cases h₂ : k = i₂
        · subst k
          simp [σ.2.2.1, hi12.symm]
        · by_cases h₃ : k = i₃
          · subst k
            simp [σ.2.2.2, hi13.symm, hi23.symm]
          · simp [h₁, h₂, h₃]
    right_inv := by
      intro τ
      funext k
      dsimp
      have hk1 : k.1 ≠ i₁ := by
        intro h
        apply k.2
        simp [C, h]
      have hk2 : k.1 ≠ i₂ := by
        intro h
        apply k.2
        simp [C, h]
      have hk3 : k.1 ≠ i₃ := by
        intro h
        apply k.2
        simp [C, h]
      simp [hk1, hk2, hk3]
  }
  have hcard : Fintype.card {σ : Assignment n // σ i₁ = v₁ ∧ σ i₂ = v₂ ∧ σ i₃ = v₃} = 2 ^ (n - 3) := by
    rw [Fintype.card_congr e]
    calc
      Fintype.card (Free → Bool) = 2 ^ Fintype.card Free := by
        rw [Fintype.card_fun]
        simp [Fintype.card_bool]
      _ = 2 ^ (n - 3) := by rw [hfree]
  exact hcard

/-- Linearity of `fintypeExpect` for `c - X` on a nonempty sample space:
`E[c - X] = c - E[X]`. -/
lemma fintypeExpect_sub_const {Ω : Type} [Fintype Ω] [DecidableEq Ω] (c : ℝ) (X : Ω → ℝ)
    (hΩ : Fintype.card Ω ≠ 0) :
    fintypeExpect (fun ω => c - X ω) = c - fintypeExpect X := by
  unfold fintypeExpect
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩ
  field_simp [hc]

/-- The sum of the indicator of a predicate over a finite type is the number of
its elements satisfying the predicate. -/
lemma sum_indicator_card {Ω : Type} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    (∑ σ : Ω, if P σ then (1 : ℝ) else 0) = (Fintype.card {σ : Ω // P σ} : ℝ) := by
  calc
    (∑ σ : Ω, if P σ then (1 : ℝ) else 0) = (Finset.univ.filter P).card := by
      exact_mod_cast (Finset.sum_boole P Finset.univ)
    _ = (Fintype.card {σ : Ω // P σ} : ℝ) := by
      exact_mod_cast (Fintype.card_of_subtype (Finset.univ.filter P) (fun σ => by simp)).symm

/-- A uniformly random assignment leaves a valid 3-CNF clause unsatisfied with
probability exactly `1/8`: its three literals are over distinct variables, so
the assignment must take the negated value at each of the three variables, and
exactly `2^(n-3)` of the `2^n` assignments do so (CLRS §35.4, Theorem 35.5). -/
lemma unsatisfied_prob (c : Finset (Literal n)) (hc : Is3CNFClause c) :
    fintypeExpect (fun σ : Assignment n => indicator (ClauseUnsatisfied c σ)) = (1 : ℝ) / 8 := by
  classical
  rcases (Finset.card_eq_three.mp hc.1) with ⟨l₁, l₂, l₃, h12, h13, h23, hc_eq⟩
  have hi12 : l₁.1 ≠ l₂.1 := hc.2 (by simp [hc_eq]) (by simp [hc_eq]) h12
  have hi13 : l₁.1 ≠ l₃.1 := hc.2 (by simp [hc_eq]) (by simp [hc_eq]) h13
  have hi23 : l₂.1 ≠ l₃.1 := hc.2 (by simp [hc_eq]) (by simp [hc_eq]) h23
  have hun : ∀ σ : Assignment n, ClauseUnsatisfied c σ ↔
      σ l₁.1 = Bool.not l₁.2 ∧ σ l₂.1 = Bool.not l₂.2 ∧ σ l₃.1 = Bool.not l₃.2 := by
    intro σ
    simp [ClauseUnsatisfied, litHolds, hc_eq, h12, h13, h23, bool_ne_iff_not]
  have hcard : Fintype.card {σ : Assignment n // ClauseUnsatisfied c σ} = 2 ^ (n - 3) := by
    have hcard3 := card_assignments_fixing_three (i₁ := l₁.1) (i₂ := l₂.1) (i₃ := l₃.1) hi12 hi13 hi23
      (v₁ := Bool.not l₁.2) (v₂ := Bool.not l₂.2) (v₃ := Bool.not l₃.2)
    have hcong : Fintype.card {σ : Assignment n // ClauseUnsatisfied c σ} =
        Fintype.card {σ : Assignment n // σ l₁.1 = Bool.not l₁.2 ∧ σ l₂.1 = Bool.not l₂.2 ∧ σ l₃.1 = Bool.not l₃.2} := by
      exact Fintype.card_congr (Equiv.subtypeEquivProp (funext fun σ => propext (hun σ)))
    rwa [hcong]
  unfold fintypeExpect indicator
  have hsum : (∑ σ : Assignment n, if ClauseUnsatisfied c σ then (1 : ℝ) else 0) = (2 ^ (n - 3) : ℝ) := by
    rw [sum_indicator_card]
    exact_mod_cast hcard
  have hcardA : (Fintype.card (Assignment n) : ℝ) = (2 ^ n : ℝ) := by
    have hnat : Fintype.card (Assignment n) = 2 ^ n := by
      rw [Fintype.card_fun]
      simp [Fintype.card_bool]
    exact_mod_cast hnat
  rw [hsum, hcardA]
  have hn : 3 ≤ n := by
    have hsub : ({l₁.1, l₂.1, l₃.1} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hthree : ({l₁.1, l₂.1, l₃.1} : Finset (Fin n)).card = 3 := by
      simp [hi12, hi13, hi23]
    have hle : 3 ≤ Finset.univ.card := le_trans (by simpa [hthree]) (Finset.card_le_card hsub)
    simpa using hle
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 ^ (n - 3) : ℝ) * 8 = (2 ^ n : ℝ) := by
    have hadd : (2 ^ (n - 3) : ℝ) * (2 ^ 3 : ℝ) = 2 ^ ((n - 3) + 3) := by rw [← pow_add]
    norm_num at hadd
    rwa [Nat.sub_add_cancel hn] at hadd
  calc
    (2 ^ (n - 3) : ℝ) / (2 ^ n : ℝ) = (2 ^ (n - 3) : ℝ) / ((2 ^ (n - 3) : ℝ) * 8) := by rw [hpow]
    _ = (1 : ℝ) / 8 := by
      field_simp [pow_ne_zero (n - 3) h2ne]

/-- A uniformly random assignment satisfies a valid 3-CNF clause with
probability exactly `7/8` (CLRS §35.4, Theorem 35.5). -/
theorem max3cnf_clause_satisfied_prob (c : Finset (Literal n)) (hc : Is3CNFClause c) :
    fintypeExpect (fun σ : Assignment n => indicator (ClauseSatisfied c σ)) = (7 : ℝ) / 8 := by
  classical
  have hU := unsatisfied_prob c hc
  have hfunc : ∀ σ : Assignment n, indicator (ClauseSatisfied c σ) =
      1 - indicator (ClauseUnsatisfied c σ) := by
    intro σ
    have hiff := clauseSatisfied_iff_not_unsatisfied c σ
    unfold indicator
    by_cases h : ClauseSatisfied c σ
    · have hUσ : ¬ ClauseUnsatisfied c σ := hiff.mp h
      simp [h, hUσ]
    · have hUσ : ClauseUnsatisfied c σ := by
        by_contra hU'
        exact h (hiff.2 hU')
      simp [h, hUσ]
  calc
    fintypeExpect (fun σ : Assignment n => indicator (ClauseSatisfied c σ))
        = fintypeExpect (fun σ : Assignment n => 1 - indicator (ClauseUnsatisfied c σ)) := by
          congr 1
          funext σ
          exact hfunc σ
    _ = 1 - fintypeExpect (fun σ : Assignment n => indicator (ClauseUnsatisfied c σ)) := by
      have hne : Fintype.card (Assignment n) ≠ 0 := by
        have hpos : 0 < Fintype.card (Assignment n) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
        exact ne_of_gt hpos
      exact fintypeExpect_sub_const (1 : ℝ) (fun σ : Assignment n => indicator (ClauseUnsatisfied c σ)) hne
    _ = 1 - (1 : ℝ) / 8 := by rw [hU]
    _ = (7 : ℝ) / 8 := by norm_num

/-- The number of clauses of `F` satisfied by the assignment `σ`. -/
def satisfiedCount (F : Finset (Finset (Literal n))) (σ : Assignment n) : ℕ :=
  (F.filter (fun c => ClauseSatisfied c σ)).card

/--
**Theorem 35.5 (expectation).**  For a family `F` of valid 3-CNF clauses, the
expected number of satisfied clauses under a uniformly random assignment is
exactly `7/8 · |F|`, by linearity of expectation over the per-clause
probabilities (CLRS §35.4, Theorem 35.5).
-/
theorem max3cnf_expect_satisfied (F : Finset (Finset (Literal n))) (hF : ∀ c ∈ F, Is3CNFClause c) :
    fintypeExpect (fun σ : Assignment n => (∑ c ∈ F, indicator (ClauseSatisfied c σ) : ℝ)) =
      (7 : ℝ) / 8 * (F.card : ℝ) := by
  rw [fintypeExpect_sum]
  have hper : ∀ c ∈ F, fintypeExpect (fun σ : Assignment n => indicator (ClauseSatisfied c σ)) = (7 : ℝ) / 8 := by
    intro c hc
    exact max3cnf_clause_satisfied_prob c (hF c hc)
  rw [Finset.sum_congr rfl hper]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/--
**Theorem 35.5.**  MAX-3-CNF has a randomized `8/7`-approximation algorithm: for
any assignment `σ₀` — in particular an optimal one — the expected number of
clauses satisfied by a uniformly random assignment is at least `7/8` of the
number that `σ₀` satisfies (CLRS §35.4, Theorem 35.5).
-/
theorem max3cnf_approx (F : Finset (Finset (Literal n))) (hF : ∀ c ∈ F, Is3CNFClause c)
    (σ₀ : Assignment n) :
    (7 : ℝ) / 8 * (satisfiedCount F σ₀ : ℝ) ≤
      fintypeExpect (fun σ : Assignment n => (∑ c ∈ F, indicator (ClauseSatisfied c σ) : ℝ)) := by
  have hle : satisfiedCount F σ₀ ≤ F.card := by
    dsimp [satisfiedCount]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hE := max3cnf_expect_satisfied F hF
  calc
    (7 : ℝ) / 8 * (satisfiedCount F σ₀ : ℝ) ≤ (7 : ℝ) / 8 * (F.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
    _ = fintypeExpect (fun σ : Assignment n => (∑ c ∈ F, indicator (ClauseSatisfied c σ) : ℝ)) := hE.symm

/-! ## Linear programming: weighted vertex cover (Theorem 35.6)

The minimum-weight vertex-cover problem takes a graph with positive vertex
weights `w(v)` and asks for a cover minimizing the total weight.  The 0-1
integer program `x(v) ∈ {0, 1}` with `x(u) + x(v) ≥ 1` on every edge is relaxed
to the linear program `0 ≤ x(v) ≤ 1`.  Any feasible solution of the IP is
feasible for the LP, so the LP optimum lower-bounds the IP optimum (the optimal
cover's weight).  APPROX-MIN-WEIGHT-VC solves the LP and rounds every vertex
with `x(v) ≥ 1/2` up to `1`; the rounding is a vertex cover (for every edge at
least one endpoint has `x ≥ 1/2`) and costs at most `2` times the LP objective
(since each rounded vertex contributes `w(v) ≤ 2·w(v)·x(v)`). -/

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V]

/-- The **weight** of a set of vertices under the weight function `w`. -/
def vertexWeight (w : V → ℚ) (C : Finset V) : ℚ :=
  ∑ v ∈ C, w v

/-- A **fractional vertex cover**: a vector `x : V → ℚ` with `0 ≤ x v ≤ 1`
satisfying `x(u) + x(v) ≥ 1` for every edge of `E₀`.  This is the feasible
region of the linear-programming relaxation (CLRS §35.4, equations (35.15)-(35.18)). -/
def IsFractionalCover (G : ApproxVertexCover.Graph V E) (x : V → ℚ) (E₀ : Finset E) : Prop :=
  (∀ v, 0 ≤ x v) ∧ (∀ v, x v ≤ 1) ∧ ∀ e ∈ E₀, x (G.src e) + x (G.dst e) ≥ 1

/-- The **LP rounding** of a fractional cover: the vertices with fractional
value at least `1/2`.  This is the rounding step of APPROX-MIN-WEIGHT-VC
(CLRS §35.4, lines 3-5). -/
def roundCover (x : V → ℚ) : Finset V :=
  Finset.univ.filter (fun v => (1 : ℚ) / 2 ≤ x v)

/-- A vertex belongs to the rounding exactly when its fractional value is at
least `1/2`. -/
lemma mem_roundCover (x : V → ℚ) (v : V) :
    v ∈ roundCover x ↔ (1 : ℚ) / 2 ≤ x v := by
  simp [roundCover]

/--
**Theorem 35.6 (correctness).**  The rounding of a fractional cover is a vertex
cover of the edge set: for every edge, at least one endpoint has fractional
value at least `1/2` (because the two values sum to at least `1`).
-/
lemma roundCover_isVertexCover (G : ApproxVertexCover.Graph V E) {x : V → ℚ} {E₀ : Finset E}
    (hx : IsFractionalCover G x E₀) :
    G.IsVertexCoverOn E₀ (roundCover x) := by
  intro e he
  have hineq : x (G.src e) + x (G.dst e) ≥ 1 := hx.2.2 e he
  by_cases hsrc : (1 : ℚ) / 2 ≤ x (G.src e)
  · left
    exact (mem_roundCover x (G.src e)).mpr hsrc
  · right
    have hsrc' : x (G.src e) < (1 : ℚ) / 2 := lt_of_not_ge hsrc
    have hdst : (1 : ℚ) / 2 ≤ x (G.dst e) := by
      nlinarith
    exact (mem_roundCover x (G.dst e)).mpr hdst

/-- The weight of the rounded cover is at most twice the LP objective
`Σ v, w(v)·x(v)`: each rounded vertex `v` has `x(v) ≥ 1/2`, so its weight
`w(v) ≤ 2·w(v)·x(v)`. -/
lemma roundCover_weight_le (G : ApproxVertexCover.Graph V E) {w : V → ℚ} {x : V → ℚ}
    {E₀ : Finset E} (hw : ∀ v, 0 < w v) (hx : IsFractionalCover G x E₀) :
    vertexWeight w (roundCover x) ≤ 2 * (∑ v : V, w v * x v) := by
  have hstep : ∀ v, v ∈ roundCover x → w v ≤ 2 * (w v * x v) := by
    intro v hv
    have hx5 : (1 : ℚ) / 2 ≤ x v := (mem_roundCover x v).mp hv
    have hwpos : 0 < w v := hw v
    nlinarith
  have hsum1 : vertexWeight w (roundCover x) ≤ ∑ v ∈ roundCover x, 2 * (w v * x v) := by
    exact Finset.sum_le_sum hstep
  have hsum2 : (∑ v ∈ roundCover x, 2 * (w v * x v)) ≤ ∑ v : V, 2 * (w v * x v) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro v _ hvnot
    exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (hw v)) (hx.1 v))
  calc
    vertexWeight w (roundCover x) = ∑ v ∈ roundCover x, w v := rfl
    _ ≤ ∑ v ∈ roundCover x, 2 * (w v * x v) := hsum1
    _ ≤ ∑ v : V, 2 * (w v * x v) := hsum2
    _ = 2 * (∑ v : V, w v * x v) := by rw [Finset.mul_sum]

/--
**Theorem 35.6.**  APPROX-MIN-WEIGHT-VC is a 2-approximation algorithm for the
minimum-weight vertex-cover problem: for any positive weights `w`, any
fractional cover `x` whose LP objective is at most the weight of a vertex cover
`C*` (in particular the LP optimum, which lower-bounds the IP optimum), the
rounded cover has weight at most `2 · w(C*)` (CLRS §35.4, Theorem 35.6).
-/
theorem approxMinWeightVC_two_approx (G : ApproxVertexCover.Graph V E) {w : V → ℚ} {x : V → ℚ}
    {E₀ : Finset E} (hw : ∀ v, 0 < w v) (hx : IsFractionalCover G x E₀)
    (Cstar : Finset V) (hCstar : G.IsVertexCoverOn E₀ Cstar)
    (hLP : (∑ v : V, w v * x v) ≤ vertexWeight w Cstar) :
    vertexWeight w (roundCover x) ≤ 2 * vertexWeight w Cstar := by
  have h1 := roundCover_weight_le (G := G) hw hx
  calc
    vertexWeight w (roundCover x) ≤ 2 * (∑ v : V, w v * x v) := h1
    _ ≤ 2 * vertexWeight w Cstar := by
      exact mul_le_mul_of_nonneg_left hLP (by norm_num)

end RandomizedLP

end CLRS
