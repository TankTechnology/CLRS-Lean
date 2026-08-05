import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.LockVariable

/-!
# 29.5 Restoring the original objective

After phase I, CLRS substitutes the current basic equations into the original
objective.  The construction below performs that substitution for arbitrary
stable-variable weights and proves its semantic contract.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- Replace a dictionary's objective by the linear form with stable-variable
weights {lit}`w`, already substituted into the current nonbasic coordinates. -/
def withObjective (D : Dictionary m n) (w : LPVar m n → ℝ) :
    Dictionary m n where
  labels := D.labels
  b := D.b
  a := D.a
  v := ∑ i, w (D.basicVar i) * D.b i
  c := fun j => w (D.nonbasicVar j) -
    ∑ i, w (D.basicVar i) * D.a i j

@[simp] theorem withObjective_basicVar (D : Dictionary m n)
    (w : LPVar m n → ℝ) (i : Fin m) :
    (D.withObjective w).basicVar i = D.basicVar i :=
  rfl

@[simp] theorem withObjective_nonbasicVar (D : Dictionary m n)
    (w : LPVar m n → ℝ) (j : Fin n) :
    (D.withObjective w).nonbasicVar j = D.nonbasicVar j :=
  rfl

@[simp] theorem withObjective_b (D : Dictionary m n)
    (w : LPVar m n → ℝ) :
    (D.withObjective w).b = D.b :=
  rfl

@[simp] theorem withObjective_a (D : Dictionary m n)
    (w : LPVar m n → ℝ) :
    (D.withObjective w).a = D.a :=
  rfl

/-- Restoring an objective leaves all represented equations unchanged. -/
@[simp] theorem withObjective_satisfies_iff (D : Dictionary m n)
    (w : LPVar m n → ℝ) (x : LPVar m n → ℝ) :
    (D.withObjective w).Satisfies x ↔ D.Satisfies x :=
  Iff.rfl

/-- Exchange the two finite sums created by objective substitution. -/
theorem substituted_double_sum (D : Dictionary m n)
    (w : LPVar m n → ℝ) (x : LPVar m n → ℝ) :
    (∑ j, (∑ i, w (D.basicVar i) * D.a i j) *
        x (D.nonbasicVar j)) =
      ∑ i, w (D.basicVar i) *
        (∑ j, D.a i j * x (D.nonbasicVar j)) := by
  calc
    (∑ j, (∑ i, w (D.basicVar i) * D.a i j) *
        x (D.nonbasicVar j)) =
        ∑ j, ∑ i, (w (D.basicVar i) * D.a i j) *
          x (D.nonbasicVar j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (w (D.basicVar i) * D.a i j) *
          x (D.nonbasicVar j) := Finset.sum_comm
    _ = ∑ i, w (D.basicVar i) *
        (∑ j, D.a i j * x (D.nonbasicVar j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- On every satisfying assignment, the restored objective is exactly the
requested stable-variable linear form. -/
theorem withObjective_objectiveRhs (D : Dictionary m n)
    (w : LPVar m n → ℝ) {x : LPVar m n → ℝ}
    (hx : D.Satisfies x) :
    (D.withObjective w).objectiveRhs x = ∑ q, w q * x q := by
  rw [D.sum_eq_sum_labels, Fintype.sum_sum_type]
  change
    (∑ i, w (D.basicVar i) * D.b i) +
        ∑ j, (w (D.nonbasicVar j) -
          ∑ i, w (D.basicVar i) * D.a i j) *
            x (D.nonbasicVar j) =
      (∑ i, w (D.basicVar i) * x (D.basicVar i)) +
        ∑ j, w (D.nonbasicVar j) * x (D.nonbasicVar j)
  have hbasic : ∀ i, x (D.basicVar i) =
      D.b i - ∑ j, D.a i j * x (D.nonbasicVar j) := by
    intro i
    simpa [rowRhs] using hx i
  simp_rw [hbasic, sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, D.substituted_double_sum w x,
    Finset.sum_sub_distrib]
  ring

namespace Equivalent

/-- Equivalent row systems remain equivalent after restoring the same stable
linear objective. -/
theorem withObjective {D E : Dictionary m n} (h : D.Equivalent E)
    (w : LPVar m n → ℝ) :
    (D.withObjective w).Equivalent (E.withObjective w) := by
  constructor
  · intro x
    simpa using h.1 x
  · intro x hx
    have hxD : D.Satisfies x :=
      ((D.withObjective_satisfies_iff w x).1 hx)
    have hxE : E.Satisfies x := (h.1 x).1 hxD
    rw [D.withObjective_objectiveRhs w hxD,
      E.withObjective_objectiveRhs w hxE]

end Equivalent

end Dictionary

namespace StandardLP

/-- Stable original/slack weights of a standard-form objective. -/
def objectiveWeight (P : StandardLP m n) : LPVar m n → ℝ
  | .inl j => P.c j
  | .inr _ => 0

/-- Restoring a standard program's own objective in its initial dictionary is
the identity. -/
theorem initialDictionary_withObjective_eq (P : StandardLP m n) :
    P.initialDictionary.withObjective P.objectiveWeight =
      P.initialDictionary := by
  cases P
  simp [Dictionary.withObjective, objectiveWeight, initialDictionary,
    Dictionary.basicVar, Dictionary.nonbasicVar]

end StandardLP

end Chapter29
end CLRS
