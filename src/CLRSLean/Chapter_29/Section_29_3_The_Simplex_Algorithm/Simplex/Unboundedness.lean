import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Optimality

/-!
# 29.3 The SIMPLEX unbounded branch

If an improving entering column has no positive constraint coefficient, the
textbook ray remains feasible for every nonnegative parameter and its objective
grows without bound.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- The assignment obtained by increasing one entering nonbasic variable to
{lit}`t`, keeping the others zero, and reading the forced basic row values. -/
def enteringRay (D : Dictionary m n) (e : Fin n) (t : ℝ) : LPVar m n → ℝ :=
  fun q =>
    match D.labels.symm q with
    | .inl i => D.b i - D.a i e * t
    | .inr j => if j = e then t else 0

@[simp] theorem enteringRay_basicVar (D : Dictionary m n)
    (e : Fin n) (t : ℝ) (i : Fin m) :
    D.enteringRay e t (D.basicVar i) = D.b i - D.a i e * t := by
  simp [enteringRay, basicVar]

@[simp] theorem enteringRay_nonbasicVar_same (D : Dictionary m n)
    (e : Fin n) (t : ℝ) :
    D.enteringRay e t (D.nonbasicVar e) = t := by
  simp [enteringRay, nonbasicVar]

@[simp] theorem enteringRay_nonbasicVar_of_ne (D : Dictionary m n)
    (e : Fin n) (t : ℝ) (j : Fin n) (hj : j ≠ e) :
    D.enteringRay e t (D.nonbasicVar j) = 0 := by
  simp [enteringRay, nonbasicVar, hj]

/-- Every point on the entering ray satisfies the dictionary equations. -/
theorem enteringRay_satisfies (D : Dictionary m n) (e : Fin n) (t : ℝ) :
    D.Satisfies (D.enteringRay e t) := by
  intro i
  rw [rowRhs, sum_eq_term_add_sumExcept e,
    enteringRay_basicVar, enteringRay_nonbasicVar_same]
  have hzero : sumExcept e (fun j =>
      D.a i j * D.enteringRay e t (D.nonbasicVar j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [D.enteringRay_nonbasicVar_of_ne e t j hje, mul_zero]
  rw [hzero]
  ring

/-- A nonpositive entering column gives a nonnegative ray from every
basic-feasible dictionary. -/
theorem enteringRay_nonnegative (D : Dictionary m n) (hD : D.IsBasicFeasible)
    (e : Fin n) (ha : ∀ i, D.a i e ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    IsNonnegativeAssignment (D.enteringRay e t) := by
  intro q
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [enteringRay_basicVar]
    have hprod : D.a i e * t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (ha i) ht
    linarith [hD i]
  · by_cases hj : j = e
    · subst j
      simpa using ht
    · rw [D.enteringRay_nonbasicVar_of_ne e t j hj]

/-- The objective along the entering ray is affine with slope equal to the
entering reduced cost. -/
theorem enteringRay_objectiveRhs (D : Dictionary m n) (e : Fin n) (t : ℝ) :
    D.objectiveRhs (D.enteringRay e t) = D.v + D.c e * t := by
  rw [objectiveRhs, sum_eq_term_add_sumExcept e,
    enteringRay_nonbasicVar_same]
  have hzero : sumExcept e (fun j =>
      D.c j * D.enteringRay e t (D.nonbasicVar j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [D.enteringRay_nonbasicVar_of_ne e t j hje, mul_zero]
  rw [hzero, add_zero]

/-- The represented nonnegative optimization problem has values above every
real bound. -/
def IsUnbounded (D : Dictionary m n) : Prop :=
  ∀ M : ℝ, ∃ x : LPVar m n → ℝ,
    IsNonnegativeAssignment x ∧ D.Satisfies x ∧ M < D.objectiveRhs x

/-- A positive-reduced-cost column with no positive constraint coefficient
certifies unboundedness. -/
theorem unbounded_of_entering_column (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (e : Fin n) (hc : 0 < D.c e)
    (ha : ∀ i, D.a i e ≤ 0) : D.IsUnbounded := by
  intro M
  let t : ℝ := |M - D.v| / D.c e + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hcancel : D.c e * (|M - D.v| / D.c e) = |M - D.v| := by
    field_simp [hc.ne']
  refine ⟨D.enteringRay e t,
    D.enteringRay_nonnegative hD e ha ht,
    D.enteringRay_satisfies e t, ?_⟩
  rw [D.enteringRay_objectiveRhs e t]
  dsimp [t]
  rw [mul_add, hcancel, mul_one]
  have habs : M - D.v ≤ |M - D.v| := le_abs_self (M - D.v)
  linarith

namespace SimplexStepResult

/-- Recover the entering slot exactly from the unbounded terminal branch. -/
def unboundedEntering {D : Dictionary m n} :
    D.SimplexStepResult → Option (Fin n)
  | .optimal _ => none
  | .unbounded e _ _ => some e
  | .pivot _ _ _ _ => none

/-- Any step-result value exposing an unbounded entering slot carries a valid
unboundedness certificate. -/
theorem unbounded_correct {D : Dictionary m n} (hD : D.IsBasicFeasible)
    (result : D.SimplexStepResult) {e : Fin n}
    (hresult : result.unboundedEntering = some e) : D.IsUnbounded := by
  cases result with
  | optimal _ =>
      cases hresult
  | unbounded entering he ha =>
      have heq : entering = e := Option.some.inj hresult
      subst e
      exact D.unbounded_of_entering_column hD entering he.1 ha
  | pivot _ _ _ _ =>
      cases hresult

end SimplexStepResult

/-- Correctness of the unbounded terminal branch returned by one SIMPLEX
step. -/
theorem simplexStep_unbounded_correct (D : Dictionary m n)
    (hD : D.IsBasicFeasible) {e : Fin n}
    (hresult : D.simplexStep.unboundedEntering = some e) : D.IsUnbounded :=
  D.simplexStep.unbounded_correct hD hresult

end Dictionary
end Chapter29
end CLRS
