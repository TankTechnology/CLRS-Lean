import CLRSLean.Chapter_29.Section_29_4_Duality

/-!
# 29.5 The auxiliary linear program

The phase-I program prepends the artificial variable {lit}`x₀`, subtracts it
from every constraint, and maximizes {lit}`-x₀`.  Setting {lit}`x₀ = 0` recovers
the original standard-form program exactly.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace StandardLP

/-- The distinguished phase-I artificial variable {lit}`x₀`. -/
def auxiliaryArtificial (n : ℕ) : Fin (n + 1) := 0

/-- Embed an original variable as `x₁, …, xₙ` in the auxiliary program. -/
def auxiliaryOriginal (j : Fin n) : Fin (n + 1) := j.succ

/-- Prepend an artificial coordinate to an original assignment. -/
def auxiliaryAssignment (t : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases t x

/-- Remove the artificial coordinate from an auxiliary assignment. -/
def auxiliaryTail (z : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun j => z (auxiliaryOriginal j)

@[simp] theorem auxiliaryAssignment_artificial (t : ℝ) (x : Fin n → ℝ) :
    auxiliaryAssignment t x (auxiliaryArtificial n) = t :=
  rfl

@[simp] theorem auxiliaryAssignment_original (t : ℝ) (x : Fin n → ℝ)
    (j : Fin n) :
    auxiliaryAssignment t x (auxiliaryOriginal j) = x j :=
  rfl

@[simp] theorem auxiliaryTail_assignment (t : ℝ) (x : Fin n → ℝ) :
    auxiliaryTail (auxiliaryAssignment t x) = x := by
  funext j
  rfl

/-- Every auxiliary vector splits into its artificial head and original tail. -/
theorem auxiliaryAssignment_parts (z : Fin (n + 1) → ℝ) :
    auxiliaryAssignment (z (auxiliaryArtificial n)) (auxiliaryTail z) = z := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  rfl

/-- CLRS-AUX: maximize {lit}`-x₀` subject to {lit}`Ax - x₀ ≤ b`. -/
def auxiliary (P : StandardLP m n) : StandardLP m (n + 1) where
  A i := Fin.cases (-1) (P.A i)
  b := P.b
  c := Fin.cases (-1) (fun _ => 0)

@[simp] theorem auxiliary_A_artificial (P : StandardLP m n) (i : Fin m) :
    P.auxiliary.A i (auxiliaryArtificial n) = -1 :=
  rfl

@[simp] theorem auxiliary_A_original (P : StandardLP m n)
    (i : Fin m) (j : Fin n) :
    P.auxiliary.A i (auxiliaryOriginal j) = P.A i j :=
  rfl

@[simp] theorem auxiliary_b (P : StandardLP m n) :
    P.auxiliary.b = P.b :=
  rfl

/-- Every auxiliary constraint has left side {lit}`Ax - x₀`. -/
theorem auxiliary_mulVec (P : StandardLP m n) (t : ℝ)
    (x : Fin n → ℝ) (i : Fin m) :
    (P.auxiliary.A *ᵥ auxiliaryAssignment t x) i =
      (P.A *ᵥ x) i - t := by
  simp [Matrix.mulVec, dotProduct, auxiliary, auxiliaryAssignment,
    Fin.sum_univ_succ]
  ring

/-- The auxiliary objective is exactly {lit}`-x₀`. -/
@[simp] theorem auxiliary_objective (P : StandardLP m n) (t : ℝ)
    (x : Fin n → ℝ) :
    P.auxiliary.objective (auxiliaryAssignment t x) = -t := by
  simp [objective, dotProduct, auxiliary, auxiliaryAssignment,
    Fin.sum_univ_succ]

/-- At artificial value zero, auxiliary feasibility is exactly original
primal feasibility. -/
theorem auxiliary_feasible_lift_iff (P : StandardLP m n)
    (x : Fin n → ℝ) :
    P.auxiliary.IsFeasible (auxiliaryAssignment 0 x) ↔
      P.IsFeasible x := by
  constructor
  · intro h
    refine ⟨fun j => h.1 (auxiliaryOriginal j), ?_⟩
    intro i
    have hi := h.2 i
    rw [P.auxiliary_mulVec] at hi
    simpa using hi
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun k => h.1 k) j
      exact le_rfl
    · intro i
      have hi := h.2 i
      rw [P.auxiliary_mulVec]
      simpa using hi

/-- The objective of an arbitrary auxiliary vector reads only its artificial
coordinate. -/
theorem auxiliary_objective_eq_neg_artificial (P : StandardLP m n)
    (z : Fin (n + 1) → ℝ) :
    P.auxiliary.objective z = -z (auxiliaryArtificial n) := by
  rw [← auxiliaryAssignment_parts z]
  exact P.auxiliary_objective _ _

/-- Every feasible auxiliary assignment has objective at most zero. -/
theorem auxiliary_objective_nonpositive_of_feasible (P : StandardLP m n)
    {z : Fin (n + 1) → ℝ} (hz : P.auxiliary.IsFeasible z) :
    P.auxiliary.objective z ≤ 0 := by
  rw [P.auxiliary_objective_eq_neg_artificial z]
  exact neg_nonpos.mpr (hz.1 (auxiliaryArtificial n))

/-- The auxiliary objective is bounded above by zero. -/
theorem auxiliary_not_isUnbounded (P : StandardLP m n) :
    ¬P.auxiliary.IsUnbounded := by
  intro hunbounded
  obtain ⟨z, hz, hpositive⟩ := hunbounded 0
  exact (not_lt_of_ge (P.auxiliary_objective_nonpositive_of_feasible hz))
    hpositive

/-- If a feasible auxiliary vector has artificial coordinate zero, its tail
is feasible for the original program. -/
theorem auxiliary_feasible_of_artificial_eq_zero (P : StandardLP m n)
    {z : Fin (n + 1) → ℝ} (hz : P.auxiliary.IsFeasible z)
    (hzero : z (auxiliaryArtificial n) = 0) :
    P.IsFeasible (auxiliaryTail z) := by
  apply (P.auxiliary_feasible_lift_iff (auxiliaryTail z)).1
  rw [← hzero, auxiliaryAssignment_parts]
  exact hz

end StandardLP
end Chapter29
end CLRS
