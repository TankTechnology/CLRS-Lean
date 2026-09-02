import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions

/-!
# 29.1 General-form normalization

CLRS §29.1 lists the general form of a linear program (equations (29.16)--
(29.19)): the objective may be maximized or minimized, each constraint may be
{lit}`=`, {lit}`≥`, or {lit}`≤`, and each variable is either nonnegative or
free.  This module converts any such program into a finite standard-form
{lit}`StandardLP` (maximize a linear objective subject to {lit}`Ax ≤ b`,
{lit}`x ≥ 0`) while preserving feasibility and the objective value up to the
maximization/minimization sign.

Main results:

- {lit}`GeneralLP`: the general-form program representation.
- {lit}`GeneralLP.toStandardLP`: the normalization.
- {lit}`GeneralLP.lift` / {lit}`GeneralLP.proj`: the variable expansion and
  its inverse.
- {lit}`GeneralLP.feasible_iff_lift`: feasibility is exactly preserved.
- {lit}`GeneralLP.objective_lift`: the objective is preserved up to sign.
- {lit}`GeneralLP.solve` / {lit}`GeneralLP.solve_complete`: a canonical
  main-text solver wrapper around the initialized SIMPLEX.

Each original variable {lit}`x j` is expanded to two nonnegative variables
{lit}`x j⁺` and {lit}`x j⁻` with {lit}`x j = x j⁺ - x j⁻`; for a nonnegative
variable an extra constraint forces {lit}`x j⁻ = 0`.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

/-- The relation of a general-form constraint row. -/
inductive ConstraintRel where
  | le | eq | ge
  deriving DecidableEq, Repr

/-- A general-form linear program: optimize {lit}`cᵀx` over constraint rows of
mixed relation and nonnegative or free variables (CLRS (29.16)--(29.19)). -/
structure GeneralLP where
  /-- Number of variables. -/
  n : ℕ
  /-- Number of constraints. -/
  m : ℕ
  /-- `true` when the objective is maximized, `false` when minimized. -/
  maximize : Bool
  /-- Objective coefficients. -/
  c : Fin n → ℝ
  /-- The relation of each constraint row. -/
  rel : Fin m → ConstraintRel
  /-- Constraint coefficient matrix. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- Constraint right-hand side. -/
  b : Fin m → ℝ
  /-- `true` when variable {lit}`j` is free (unrestricted). -/
  free : Fin n → Bool

namespace GeneralLP

variable (G : GeneralLP)

/-- An assignment is feasible when every nonnegative variable is nonnegative
and every constraint holds under its relation. -/
def IsFeasible (x : Fin G.n → ℝ) : Prop :=
  (∀ j, ¬ G.free j → 0 ≤ x j) ∧
    ∀ i, match G.rel i with
      | ConstraintRel.le => (G.A *ᵥ x) i ≤ G.b i
      | ConstraintRel.eq => (G.A *ᵥ x) i = G.b i
      | ConstraintRel.ge => G.b i ≤ (G.A *ᵥ x) i

/-- The objective {lit}`cᵀx` (before the maximization/minimization sign). -/
def objective (x : Fin G.n → ℝ) : ℝ :=
  G.c ⬝ᵥ x

/-- The sign {lit}`+1` for maximization and {lit}`-1` for minimization, so that
{lit}`objectiveSign · objective` is always the quantity being maximized. -/
def objectiveSign : ℝ :=
  if G.maximize then 1 else -1

/-- An assignment is optimal when it is feasible and its signed objective
dominates every other feasible assignment. -/
def IsOptimal (x : Fin G.n → ℝ) : Prop :=
  G.IsFeasible x ∧
    ∀ z, G.IsFeasible z → G.objectiveSign * G.objective z ≤ G.objectiveSign * G.objective x

/-- The signed objective is unbounded above on feasible assignments. -/
def IsUnbounded : Prop :=
  ∀ M : ℝ, ∃ x, G.IsFeasible x ∧ M < G.objectiveSign * G.objective x

/-- Positive part of the expanded variable {lit}`j`. -/
abbrev posIndex (j : Fin G.n) : Fin (G.n + G.n) :=
  Fin.castAdd G.n j

/-- Negative part of the expanded variable {lit}`j`. -/
abbrev negIndex (j : Fin G.n) : Fin (G.n + G.n) :=
  Fin.natAdd G.n j

/-- Upper form of constraint row {lit}`i`. -/
abbrev upperIndex (i : Fin G.m) : Fin ((G.m + G.m) + G.n) :=
  Fin.castAdd G.n (Fin.castAdd G.m i)

/-- Lower form of constraint row {lit}`i`. -/
abbrev lowerIndex (i : Fin G.m) : Fin ((G.m + G.m) + G.n) :=
  Fin.castAdd G.n (Fin.natAdd G.m i)

/-- The nonnegativity-lock row for variable {lit}`j`. -/
abbrev lockIndex (j : Fin G.n) : Fin ((G.m + G.m) + G.n) :=
  Fin.natAdd (G.m + G.m) j

/-- The normalized constraint matrix: each equality contributes an upper and
lower inequality, each {lit}`≥` contributes a lower inequality, and each
nonnegative variable contributes a lock row forcing its negative part to zero. -/
def normalizedA : Matrix (Fin ((G.m + G.m) + G.n)) (Fin (G.n + G.n)) ℝ :=
  fun i =>
    Fin.addCases (motive := fun _ => Fin (G.n + G.n) → ℝ)
      (fun ij =>
        Fin.addCases (motive := fun _ => Fin (G.n + G.n) → ℝ)
          (fun iU =>
            fun j =>
              Fin.addCases (motive := fun _ => ℝ)
                (fun jP => if G.rel iU = ConstraintRel.ge then 0 else G.A iU jP)
                (fun jN => if G.rel iU = ConstraintRel.ge then 0 else -(G.A iU jN))
                j)
          (fun iL =>
            fun j =>
              Fin.addCases (motive := fun _ => ℝ)
                (fun jP => if G.rel iL = ConstraintRel.le then 0 else -(G.A iL jP))
                (fun jN => if G.rel iL = ConstraintRel.le then 0 else G.A iL jN)
                j)
          ij)
      (fun jL =>
        fun j =>
          Fin.addCases (motive := fun _ => ℝ)
            (fun _ => 0)
            (fun jN => if G.free jL then 0 else (if jN = jL then 1 else 0))
            j)
      i

/-- The normalized right-hand side, mirroring {lit}`normalizedA`. -/
def normalizedB : Fin ((G.m + G.m) + G.n) → ℝ :=
  fun i =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun ij =>
        Fin.addCases (motive := fun _ => ℝ)
          (fun iU => if G.rel iU = ConstraintRel.ge then 0 else G.b iU)
          (fun iL => if G.rel iL = ConstraintRel.le then 0 else -(G.b iL))
          ij)
      (fun _ => 0)
      i

/-- The normalized objective: {lit}`sign · c` on positive parts and
{lit}`-sign · c` on negative parts. -/
def normalizedC : Fin (G.n + G.n) → ℝ :=
  fun j =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun jP => G.objectiveSign * G.c jP)
      (fun jN => -(G.objectiveSign * G.c jN))
      j

/-- The normalized standard-form program. -/
abbrev toStandardLP : StandardLP ((G.m + G.m) + G.n) (G.n + G.n) :=
  { A := G.normalizedA, b := G.normalizedB, c := G.normalizedC }

/-- Expand an assignment to the nonnegative positive/negative parts. -/
def lift (x : Fin G.n → ℝ) : Fin (G.n + G.n) → ℝ :=
  fun j =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun jP => max (x jP) 0)
      (fun jN => max (-(x jN)) 0)
      j

/-- Collapse an expanded assignment back to the signed difference. -/
def proj (x' : Fin (G.n + G.n) → ℝ) : Fin G.n → ℝ :=
  fun j => x' (G.posIndex j) - x' (G.negIndex j)

/-- {lit}`max a 0 - max (-a) 0 = a`. -/
lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · have hneg : -a ≤ 0 := by linarith
    simp [max_eq_left h, max_eq_right hneg]
  · have hneg : 0 ≤ -a := by linarith
    have ha : a ≤ 0 := by linarith
    simp [max_eq_right ha, max_eq_left hneg]

/-! ## Index reductions -/

lemma lift_pos (x : Fin G.n → ℝ) (j : Fin G.n) :
    G.lift x (G.posIndex j) = max (x j) 0 := by
  simp [lift, posIndex, Fin.addCases, Fin.castAdd, Fin.castLT]

lemma lift_neg (x : Fin G.n → ℝ) (j : Fin G.n) :
    G.lift x (G.negIndex j) = max (-(x j)) 0 := by
  simp [lift, negIndex, Fin.addCases, Fin.natAdd]

lemma normalizedA_upper_pos (iU : Fin G.m) (jP : Fin G.n) :
    G.normalizedA (G.upperIndex iU) (G.posIndex jP) =
      if G.rel iU = ConstraintRel.ge then 0 else G.A iU jP := by
  have hlt : ↑iU < G.m + G.m := by omega
  simp [normalizedA, upperIndex, posIndex, Fin.addCases, Fin.castAdd, Fin.castLT, hlt]

lemma normalizedA_upper_neg (iU : Fin G.m) (jN : Fin G.n) :
    G.normalizedA (G.upperIndex iU) (G.negIndex jN) =
      if G.rel iU = ConstraintRel.ge then 0 else -(G.A iU jN) := by
  have hlt : ↑iU < G.m + G.m := by omega
  simp [normalizedA, upperIndex, negIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd, hlt]

lemma normalizedA_lower_pos (iL : Fin G.m) (jP : Fin G.n) :
    G.normalizedA (G.lowerIndex iL) (G.posIndex jP) =
      if G.rel iL = ConstraintRel.le then 0 else -(G.A iL jP) := by
  simp [normalizedA, lowerIndex, posIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd]

lemma normalizedA_lower_neg (iL : Fin G.m) (jN : Fin G.n) :
    G.normalizedA (G.lowerIndex iL) (G.negIndex jN) =
      if G.rel iL = ConstraintRel.le then 0 else G.A iL jN := by
  simp [normalizedA, lowerIndex, negIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd]

lemma normalizedA_lock_pos (jL jP : Fin G.n) :
    G.normalizedA (G.lockIndex jL) (G.posIndex jP) = 0 := by
  simp [normalizedA, lockIndex, posIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd]

lemma normalizedA_lock_neg (jL jN : Fin G.n) :
    G.normalizedA (G.lockIndex jL) (G.negIndex jN) =
      if G.free jL then 0 else (if jN = jL then 1 else 0) := by
  simp [normalizedA, lockIndex, negIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd]

lemma normalizedB_upper (iU : Fin G.m) :
    G.normalizedB (G.upperIndex iU) = if G.rel iU = ConstraintRel.ge then 0 else G.b iU := by
  have hlt : ↑iU < G.m + G.m := by omega
  simp [normalizedB, upperIndex, Fin.addCases, Fin.castAdd, Fin.castLT, hlt]

lemma normalizedB_lower (iL : Fin G.m) :
    G.normalizedB (G.lowerIndex iL) = if G.rel iL = ConstraintRel.le then 0 else -(G.b iL) := by
  simp [normalizedB, lowerIndex, Fin.addCases, Fin.castAdd, Fin.castLT, Fin.natAdd]

lemma normalizedB_lock (jL : Fin G.n) : G.normalizedB (G.lockIndex jL) = 0 := by
  simp [normalizedB, lockIndex, Fin.addCases, Fin.natAdd]

lemma normalizedC_pos (jP : Fin G.n) :
    G.normalizedC (G.posIndex jP) = G.objectiveSign * G.c jP := by
  simp [normalizedC, posIndex, Fin.addCases, Fin.castAdd, Fin.castLT]

lemma normalizedC_neg (jN : Fin G.n) :
    G.normalizedC (G.negIndex jN) = -(G.objectiveSign * G.c jN) := by
  simp [normalizedC, negIndex, Fin.addCases, Fin.natAdd]

/-! ## Row-vector identities -/

lemma normalizedA_mulVec_upper (x' : Fin (G.n + G.n) → ℝ) (iU : Fin G.m)
    (hge : G.rel iU ≠ ConstraintRel.ge) :
    (G.normalizedA *ᵥ x') (G.upperIndex iU) =
      ∑ j : Fin G.n, G.A iU j * (x' (G.posIndex j) - x' (G.negIndex j)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  have h1 : (∑ j : Fin G.n, G.normalizedA (G.upperIndex iU) (G.posIndex j) * x' (G.posIndex j)) =
      ∑ j : Fin G.n, G.A iU j * x' (G.posIndex j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalizedA_upper_pos, if_neg hge]
  have h2 : (∑ j : Fin G.n, G.normalizedA (G.upperIndex iU) (G.negIndex j) * x' (G.negIndex j)) =
      ∑ j : Fin G.n, (-(G.A iU j)) * x' (G.negIndex j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalizedA_upper_neg, if_neg hge]
  rw [h1, h2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma normalizedA_mulVec_upper_ge (x' : Fin (G.n + G.n) → ℝ) (iU : Fin G.m)
    (hge : G.rel iU = ConstraintRel.ge) :
    (G.normalizedA *ᵥ x') (G.upperIndex iU) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  have h1 : (∑ j : Fin G.n, G.normalizedA (G.upperIndex iU) (G.posIndex j) * x' (G.posIndex j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_upper_pos, if_pos hge, zero_mul]
  have h2 : (∑ j : Fin G.n, G.normalizedA (G.upperIndex iU) (G.negIndex j) * x' (G.negIndex j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_upper_neg, if_pos hge, zero_mul]
  rw [h1, h2]
  simp

lemma normalizedA_mulVec_lower (x' : Fin (G.n + G.n) → ℝ) (iL : Fin G.m)
    (hle : G.rel iL ≠ ConstraintRel.le) :
    (G.normalizedA *ᵥ x') (G.lowerIndex iL) =
      -(∑ j : Fin G.n, G.A iL j * (x' (G.posIndex j) - x' (G.negIndex j))) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  have h1 : (∑ j : Fin G.n, G.normalizedA (G.lowerIndex iL) (G.posIndex j) * x' (G.posIndex j)) =
      ∑ j : Fin G.n, -(G.A iL j * x' (G.posIndex j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalizedA_lower_pos, if_neg hle, neg_mul]
  have h2 : (∑ j : Fin G.n, G.normalizedA (G.lowerIndex iL) (G.negIndex j) * x' (G.negIndex j)) =
      ∑ j : Fin G.n, G.A iL j * x' (G.negIndex j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalizedA_lower_neg, if_neg hle]
  rw [h1, h2]
  rw [Finset.sum_neg_distrib]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

lemma normalizedA_mulVec_lower_le (x' : Fin (G.n + G.n) → ℝ) (iL : Fin G.m)
    (hle : G.rel iL = ConstraintRel.le) :
    (G.normalizedA *ᵥ x') (G.lowerIndex iL) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  have h1 : (∑ j : Fin G.n, G.normalizedA (G.lowerIndex iL) (G.posIndex j) * x' (G.posIndex j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_lower_pos, if_pos hle, zero_mul]
  have h2 : (∑ j : Fin G.n, G.normalizedA (G.lowerIndex iL) (G.negIndex j) * x' (G.negIndex j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_lower_neg, if_pos hle, zero_mul]
  rw [h1, h2]
  simp

lemma normalizedA_mulVec_lock (x' : Fin (G.n + G.n) → ℝ) (jL : Fin G.n) :
    (G.normalizedA *ᵥ x') (G.lockIndex jL) = if G.free jL then 0 else x' (G.negIndex jL) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  have h1 : (∑ j : Fin G.n, G.normalizedA (G.lockIndex jL) (G.posIndex j) * x' (G.posIndex j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_lock_pos, zero_mul]
  rw [h1]
  simp only [zero_add]
  by_cases hfree : G.free jL
  · rw [if_pos hfree]
    apply Finset.sum_eq_zero
    intro j hj
    rw [normalizedA_lock_neg, if_pos hfree, zero_mul]
  · rw [if_neg hfree]
    have hsum : (∑ j : Fin G.n, (if j = jL then 1 else 0) * x' (G.negIndex j)) = x' (G.negIndex jL) := by
      rw [Finset.sum_eq_single jL]
      · simp
      · intro j hj hne
        simp [hne]
      · intro h
        exact False.elim (h (Finset.mem_univ jL))
    calc
      (∑ j : Fin G.n, G.normalizedA (G.lockIndex jL) (G.negIndex j) * x' (G.negIndex j))
          = ∑ j : Fin G.n, (if G.free jL then 0 else (if j = jL then 1 else 0)) * x' (G.negIndex j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [normalizedA_lock_neg]
      _ = ∑ j : Fin G.n, (if j = jL then 1 else 0) * x' (G.negIndex j) := by
              simp [hfree]
      _ = x' (G.negIndex jL) := hsum

/-! ## Feasibility -/

/-- An expanded assignment is coordinatewise nonnegative. -/
theorem lift_nonnegative (x : Fin G.n → ℝ) : IsNonnegative (G.lift x) := by
  intro j
  exact Fin.addCases (motive := fun j => 0 ≤ G.lift x j)
    (fun jP => by rw [G.lift_pos]; exact le_max_right _ _)
    (fun jN => by rw [G.lift_neg]; exact le_max_right _ _)
    j

/-- The upper form of a constraint holds for the expanded assignment. -/
lemma feasible_constraint_upper {x : Fin G.n → ℝ} (hx : G.IsFeasible x) (iU : Fin G.m) :
    (G.normalizedA *ᵥ G.lift x) (G.upperIndex iU) ≤ G.normalizedB (G.upperIndex iU) := by
  by_cases hge : G.rel iU = ConstraintRel.ge
  · simp [G.normalizedA_mulVec_upper_ge (G.lift x) iU hge, G.normalizedB_upper, hge]
  · rw [G.normalizedA_mulVec_upper (G.lift x) iU hge]
    rw [G.normalizedB_upper]
    simp only [hge, if_false]
    have hsum : (∑ j : Fin G.n, G.A iU j * (G.lift x (G.posIndex j) - G.lift x (G.negIndex j))) =
        (G.A *ᵥ x) iU := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j hj
      rw [G.lift_pos, G.lift_neg, max_sub_max_neg]
    rw [hsum]
    cases hrel : G.rel iU with
    | le => exact by simpa [hrel] using hx.2 iU
    | eq => exact le_of_eq (by simpa [hrel] using hx.2 iU)
    | ge => exact False.elim (hge hrel)

/-- The lower form of a constraint holds for the expanded assignment. -/
lemma feasible_constraint_lower {x : Fin G.n → ℝ} (hx : G.IsFeasible x) (iL : Fin G.m) :
    (G.normalizedA *ᵥ G.lift x) (G.lowerIndex iL) ≤ G.normalizedB (G.lowerIndex iL) := by
  by_cases hle : G.rel iL = ConstraintRel.le
  · simp [G.normalizedA_mulVec_lower_le (G.lift x) iL hle, G.normalizedB_lower, hle]
  · rw [G.normalizedA_mulVec_lower (G.lift x) iL hle]
    rw [G.normalizedB_lower]
    simp only [hle, if_false]
    have hsum : (∑ j : Fin G.n, G.A iL j * (G.lift x (G.posIndex j) - G.lift x (G.negIndex j))) =
        (G.A *ᵥ x) iL := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j hj
      rw [G.lift_pos, G.lift_neg, max_sub_max_neg]
    rw [hsum]
    cases hrel : G.rel iL with
    | le => exact False.elim (hle hrel)
    | eq => exact le_of_eq (by simpa [hrel] using hx.2 iL)
    | ge => exact neg_le_neg (by simpa [hrel] using hx.2 iL)

/-- The nonnegativity-lock row holds for the expanded assignment. -/
lemma feasible_constraint_lock {x : Fin G.n → ℝ} (hx : G.IsFeasible x) (jL : Fin G.n) :
    (G.normalizedA *ᵥ G.lift x) (G.lockIndex jL) ≤ G.normalizedB (G.lockIndex jL) := by
  rw [G.normalizedA_mulVec_lock, G.normalizedB_lock]
  by_cases hfree : G.free jL
  · simp [hfree]
  · rw [if_neg hfree]
    have hnn : 0 ≤ x jL := hx.1 jL hfree
    rw [G.lift_neg]
    have hneg : -(x jL) ≤ 0 := by linarith
    rw [max_eq_right hneg]

/-- A feasible assignment expands to a feasible standard-form assignment. -/
theorem normalized_feasible_of_feasible {x : Fin G.n → ℝ} (hx : G.IsFeasible x) :
    (G.toStandardLP).IsFeasible (G.lift x) := by
  refine ⟨G.lift_nonnegative x, ?_⟩
  intro i
  exact Fin.addCases (motive := fun i => (G.normalizedA *ᵥ G.lift x) i ≤ G.normalizedB i)
    (fun ij =>
      Fin.addCases (motive := fun ij => (G.normalizedA *ᵥ G.lift x) (Fin.castAdd G.n ij) ≤ G.normalizedB (Fin.castAdd G.n ij))
        (fun iU => G.feasible_constraint_upper hx iU)
        (fun iL => G.feasible_constraint_lower hx iL)
        ij)
    (fun jL => G.feasible_constraint_lock hx jL)
    i

/-- Every standard-form-feasible expanded assignment collapses to a feasible
general-form assignment. -/
theorem feasible_of_normalized_feasible {x' : Fin (G.n + G.n) → ℝ}
    (hx' : (G.toStandardLP).IsFeasible x') : G.IsFeasible (G.proj x') := by
  refine ⟨?_, ?_⟩
  · intro j hjfree
    have hlock : (G.normalizedA *ᵥ x') (G.lockIndex j) ≤ G.normalizedB (G.lockIndex j) :=
      hx'.2 (G.lockIndex j)
    rw [G.normalizedA_mulVec_lock, G.normalizedB_lock] at hlock
    by_cases hfree : G.free j
    · exfalso
      exact hjfree hfree
    · rw [if_neg hfree] at hlock
      have hneg_nonneg := hx'.1 (G.negIndex j)
      have hneg_zero : x' (G.negIndex j) = 0 := le_antisymm hlock hneg_nonneg
      unfold proj
      rw [hneg_zero]
      simpa using hx'.1 (G.posIndex j)
  · intro i
    cases hrel : G.rel i with
    | le =>
        have hne : G.rel i ≠ ConstraintRel.ge := by
          intro hc
          rw [hrel] at hc
          cases hc
        have hupper : (G.normalizedA *ᵥ x') (G.upperIndex i) ≤ G.normalizedB (G.upperIndex i) :=
          hx'.2 (G.upperIndex i)
        rw [G.normalizedA_mulVec_upper x' i hne, G.normalizedB_upper] at hupper
        simp only [hrel, if_false] at hupper
        simpa [Matrix.mulVec, dotProduct, proj] using hupper
    | eq =>
        have hne_ge : G.rel i ≠ ConstraintRel.ge := by
          intro hc
          rw [hrel] at hc
          cases hc
        have hne_le : G.rel i ≠ ConstraintRel.le := by
          intro hc
          rw [hrel] at hc
          cases hc
        have hupper : (G.normalizedA *ᵥ x') (G.upperIndex i) ≤ G.normalizedB (G.upperIndex i) :=
          hx'.2 (G.upperIndex i)
        have hlower : (G.normalizedA *ᵥ x') (G.lowerIndex i) ≤ G.normalizedB (G.lowerIndex i) :=
          hx'.2 (G.lowerIndex i)
        rw [G.normalizedA_mulVec_upper x' i hne_ge, G.normalizedB_upper] at hupper
        rw [G.normalizedA_mulVec_lower x' i hne_le, G.normalizedB_lower] at hlower
        simp only [hrel, if_false] at hupper hlower
        have hle : (G.A *ᵥ G.proj x') i ≤ G.b i := by
          simpa [Matrix.mulVec, dotProduct, proj] using hupper
        have hge : G.b i ≤ (G.A *ᵥ G.proj x') i := by
          have h := neg_le_neg_iff.mp hlower
          simpa [Matrix.mulVec, dotProduct, proj] using h
        exact le_antisymm hle hge
    | ge =>
        have hne : G.rel i ≠ ConstraintRel.le := by
          intro hc
          rw [hrel] at hc
          cases hc
        have hlower : (G.normalizedA *ᵥ x') (G.lowerIndex i) ≤ G.normalizedB (G.lowerIndex i) :=
          hx'.2 (G.lowerIndex i)
        rw [G.normalizedA_mulVec_lower x' i hne, G.normalizedB_lower] at hlower
        simp only [hrel, if_false] at hlower
        have h := neg_le_neg_iff.mp hlower
        simpa [Matrix.mulVec, dotProduct, proj] using h

/-- The expansion collapses to the original assignment. -/
theorem proj_lift (x : Fin G.n → ℝ) : G.proj (G.lift x) = x := by
  funext j
  unfold proj
  rw [G.lift_pos, G.lift_neg]
  exact max_sub_max_neg (x j)

/-- Feasibility is exactly preserved under the expansion. -/
theorem feasible_iff_lift (x : Fin G.n → ℝ) :
    G.IsFeasible x ↔ (G.toStandardLP).IsFeasible (G.lift x) := by
  constructor
  · exact G.normalized_feasible_of_feasible
  · intro h
    simpa [G.proj_lift x] using G.feasible_of_normalized_feasible h

/-- Existence of a feasible assignment is preserved under the normalization. -/
theorem feasible_iff_exists :
    (∃ x : Fin G.n → ℝ, G.IsFeasible x) ↔
      (∃ x' : Fin (G.n + G.n) → ℝ, (G.toStandardLP).IsFeasible x') := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨G.lift x, G.normalized_feasible_of_feasible hx⟩
  · rintro ⟨x', hx'⟩
    exact ⟨G.proj x', G.feasible_of_normalized_feasible hx'⟩

/-! ## Objective preservation -/

/-- The normalized objective of an arbitrary expanded assignment is the signed
objective of its collapse. -/
theorem objective_eq_sign_objective_proj (x' : Fin (G.n + G.n) → ℝ) :
    (G.toStandardLP).objective x' = G.objectiveSign * G.objective (G.proj x') := by
  simp only [StandardLP.objective, objective, proj, dotProduct]
  rw [Fin.sum_univ_add]
  simp only [normalizedC_pos, normalizedC_neg]
  calc
    (∑ jP : Fin G.n, (G.objectiveSign * G.c jP) * x' (G.posIndex jP))
        + ∑ jN : Fin G.n, (-(G.objectiveSign * G.c jN)) * x' (G.negIndex jN)
        = (∑ jP : Fin G.n, G.objectiveSign * (G.c jP * x' (G.posIndex jP)))
          + ∑ jN : Fin G.n, (-(G.objectiveSign)) * (G.c jN * x' (G.negIndex jN)) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              ring
            · apply Finset.sum_congr rfl
              intro j hj
              ring
    _ = G.objectiveSign * (∑ jP : Fin G.n, G.c jP * x' (G.posIndex jP))
          + (-(G.objectiveSign)) * (∑ jN : Fin G.n, G.c jN * x' (G.negIndex jN)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = G.objectiveSign * (∑ j : Fin G.n, G.c j * (x' (G.posIndex j) - x' (G.negIndex j))) := by
            simp only [mul_sub]
            rw [Finset.sum_sub_distrib]
            ring

/-- The normalized objective of an expanded assignment is the signed general
objective. -/
theorem objective_lift (x : Fin G.n → ℝ) :
    (G.toStandardLP).objective (G.lift x) = G.objectiveSign * G.objective x := by
  rw [G.objective_eq_sign_objective_proj]
  congr 1
  rw [G.proj_lift x]

end GeneralLP
end Chapter29
end CLRS
