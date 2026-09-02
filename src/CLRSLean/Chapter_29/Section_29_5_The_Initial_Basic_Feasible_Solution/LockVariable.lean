import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseOne

/-!
# 29.5 Locking the artificial variable

The textbook removes the artificial variable after phase I.  With fixed
finite index types, it is equivalent and more stable to add its nonnegative
lock row {lit}`x₀ ≤ 0`: together with {lit}`x₀ ≥ 0`, this forces
{lit}`x₀ = 0`.
This module implements that one-row dictionary extension generically.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- Embed an old original/slack variable after prepending one new slack row. -/
def embedOldVar : LPVar m n → LPVar (m + 1) n
  | .inl j => .inl j
  | .inr i => .inr i.succ

/-- Restrict an extended assignment to the old original/slack variables. -/
def dropAddedSlack (z : LPVar (m + 1) n → ℝ) : LPVar m n → ℝ :=
  fun q => z (embedOldVar q)

/-- The newly prepended slack variable. -/
def addedSlackVar (m n : ℕ) : LPVar (m + 1) n :=
  .inr 0

@[simp] theorem dropAddedSlack_apply (z : LPVar (m + 1) n → ℝ)
    (q : LPVar m n) :
    dropAddedSlack z q = z (embedOldVar q) :=
  rfl

/-- Split {lit}`Fin (m+1)` into old rows and one distinguished new row. -/
def finAddOneEquiv (m : ℕ) : Fin (m + 1) ≃ Fin m ⊕ PUnit.{1} :=
  (finSuccEquiv m).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin m))

/-- Extend a dictionary's slot labeling by one new basic slack variable. -/
def lockLabels (D : Dictionary m n) :
    (Fin (m + 1) ⊕ Fin n) ≃ LPVar (m + 1) n :=
  (Equiv.sumCongr (finAddOneEquiv m) (Equiv.refl (Fin n))).trans
    ((Equiv.sumAssoc (Fin m) PUnit.{1} (Fin n)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin m))
        (Equiv.sumComm PUnit.{1} (Fin n))).trans
        ((Equiv.sumAssoc (Fin m) (Fin n) PUnit.{1}).symm.trans
          ((Equiv.sumCongr D.labels (Equiv.refl PUnit.{1})).trans
            ((Equiv.sumAssoc (Fin n) (Fin m) PUnit.{1}).trans
              (Equiv.sumCongr (Equiv.refl (Fin n))
                (finAddOneEquiv m).symm))))))

/-- Coefficients representing one stable variable in the current nonbasic
coordinates. -/
def variableRowCoeff (D : Dictionary m n) (q : LPVar m n) (j : Fin n) : ℝ :=
  match D.labels.symm q with
  | .inl i => D.a i j
  | .inr e => if j = e then -1 else 0

/-- Add a new basic slack equation {lit}`s = -q`, thereby forcing the already
nonnegative stable variable {lit}`q` to zero in every nonnegative assignment. -/
def lockVariable (D : Dictionary m n) (q : LPVar m n) :
    Dictionary (m + 1) n where
  labels := D.lockLabels
  b := Fin.cases (-D.basicAssignment q) D.b
  a := Fin.cases (fun j => -D.variableRowCoeff q j) D.a
  v := D.v
  c := D.c

@[simp] theorem lockVariable_basicVar_zero (D : Dictionary m n)
    (q : LPVar m n) :
    (D.lockVariable q).basicVar 0 = addedSlackVar m n := by
  simp [lockVariable, basicVar, lockLabels, finAddOneEquiv, addedSlackVar]

@[simp] theorem lockVariable_basicVar_succ (D : Dictionary m n)
    (q : LPVar m n) (i : Fin m) :
    (D.lockVariable q).basicVar i.succ = embedOldVar (D.basicVar i) := by
  change D.lockLabels (.inl i.succ) = embedOldVar (D.labels (.inl i))
  generalize hv : D.labels (.inl i) = v
  cases v <;>
    simp [lockLabels, finAddOneEquiv, embedOldVar, hv]

@[simp] theorem lockVariable_nonbasicVar (D : Dictionary m n)
    (q : LPVar m n) (j : Fin n) :
    (D.lockVariable q).nonbasicVar j = embedOldVar (D.nonbasicVar j) := by
  change D.lockLabels (.inr j) = embedOldVar (D.labels (.inr j))
  generalize hv : D.labels (.inr j) = v
  cases v <;>
    simp [lockLabels, finAddOneEquiv, embedOldVar, hv]

@[simp] theorem lockVariable_b_zero (D : Dictionary m n) (q : LPVar m n) :
    (D.lockVariable q).b 0 = -D.basicAssignment q :=
  rfl

@[simp] theorem lockVariable_b_succ (D : Dictionary m n)
    (q : LPVar m n) (i : Fin m) :
    (D.lockVariable q).b i.succ = D.b i :=
  rfl

@[simp] theorem lockVariable_a_zero (D : Dictionary m n)
    (q : LPVar m n) (j : Fin n) :
    (D.lockVariable q).a 0 j = -D.variableRowCoeff q j :=
  rfl

@[simp] theorem lockVariable_a_succ (D : Dictionary m n)
    (q : LPVar m n) (i : Fin m) (j : Fin n) :
    (D.lockVariable q).a i.succ j = D.a i j :=
  rfl

/-- A satisfying assignment evaluates any stable variable by its represented
constant and nonbasic coefficients. -/
theorem value_eq_variableRow (D : Dictionary m n) {x : LPVar m n → ℝ}
    (hx : D.Satisfies x) (q : LPVar m n) :
    x q = D.basicAssignment q -
      ∑ j, D.variableRowCoeff q j * x (D.nonbasicVar j) := by
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨e, rfl⟩
  · rw [D.basicAssignment_basicVar]
    simpa [rowRhs, variableRowCoeff, basicVar] using hx i
  · rw [D.basicAssignment_nonbasicVar]
    rw [sum_eq_term_add_sumExcept e]
    have hzero : sumExcept e (fun j =>
        D.variableRowCoeff (D.nonbasicVar e) j *
          x (D.nonbasicVar j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hje : j ≠ e := (Finset.mem_erase.mp hj).1
      simp [variableRowCoeff, nonbasicVar, hje]
    rw [hzero]
    simp [variableRowCoeff, nonbasicVar]

/-- Old row right-hand sides are unchanged by the lock extension. -/
theorem lockVariable_rowRhs_succ (D : Dictionary m n) (q : LPVar m n)
    (z : LPVar (m + 1) n → ℝ) (i : Fin m) :
    (D.lockVariable q).rowRhs z i.succ =
      D.rowRhs (dropAddedSlack z) i := by
  simp [rowRhs]

/-- The new row is exactly the equation for the negated locked variable. -/
theorem lockVariable_rowRhs_zero (D : Dictionary m n) (q : LPVar m n)
    (z : LPVar (m + 1) n → ℝ) :
    (D.lockVariable q).rowRhs z 0 =
      -(D.basicAssignment q -
        ∑ j, D.variableRowCoeff q j *
          dropAddedSlack z (D.nonbasicVar j)) := by
  simp [rowRhs]
  ring

/-- Semantic contract of the lock extension. -/
theorem lockVariable_satisfies_iff (D : Dictionary m n) (q : LPVar m n)
    (z : LPVar (m + 1) n → ℝ) :
    (D.lockVariable q).Satisfies z ↔
      D.Satisfies (dropAddedSlack z) ∧
        z (addedSlackVar m n) = -dropAddedSlack z q := by
  constructor
  · intro hz
    have hold : D.Satisfies (dropAddedSlack z) := by
      intro i
      have hi := hz i.succ
      simpa [D.lockVariable_rowRhs_succ q z i] using hi
    refine ⟨hold, ?_⟩
    have hzero := hz 0
    rw [D.lockVariable_basicVar_zero,
      D.lockVariable_rowRhs_zero] at hzero
    rw [D.value_eq_variableRow hold q]
    exact hzero
  · rintro ⟨hold, hlock⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [D.lockVariable_basicVar_zero,
        D.lockVariable_rowRhs_zero, hlock,
        D.value_eq_variableRow hold q]
    · simpa [D.lockVariable_rowRhs_succ q z k] using hold k

/-- The lock extension preserves the old objective expression. -/
theorem lockVariable_objectiveRhs (D : Dictionary m n) (q : LPVar m n)
    (z : LPVar (m + 1) n → ℝ) :
    (D.lockVariable q).objectiveRhs z =
      D.objectiveRhs (dropAddedSlack z) := by
  rw [objectiveRhs, objectiveRhs]
  change D.v + ∑ j, D.c j * z ((D.lockVariable q).nonbasicVar j) =
    D.v + ∑ j, D.c j * dropAddedSlack z (D.nonbasicVar j)
  simp

/-- Locking a variable whose basic value is zero preserves basic feasibility. -/
theorem lockVariable_isBasicFeasible_of_value_eq_zero (D : Dictionary m n)
    (q : LPVar m n) (hD : D.IsBasicFeasible)
    (hq : D.basicAssignment q = 0) :
    (D.lockVariable q).IsBasicFeasible := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [hq]
  · simpa using hD k

namespace Equivalent

/-- Locking the same stable variable preserves dictionary equivalence. -/
theorem lockVariable {D E : Dictionary m n} (h : D.Equivalent E)
    (q : LPVar m n) :
    (D.lockVariable q).Equivalent (E.lockVariable q) := by
  constructor
  · intro z
    rw [D.lockVariable_satisfies_iff, E.lockVariable_satisfies_iff]
    exact and_congr (h.1 (dropAddedSlack z)) Iff.rfl
  · intro z hz
    rw [D.lockVariable_objectiveRhs, E.lockVariable_objectiveRhs]
    exact h.2 (dropAddedSlack z)
      ((D.lockVariable_satisfies_iff q z).1 hz).1

end Equivalent

end Dictionary
end Chapter29
end CLRS
