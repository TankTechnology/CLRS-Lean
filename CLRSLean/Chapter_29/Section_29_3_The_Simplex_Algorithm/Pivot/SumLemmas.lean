import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Algebra

/-!
# 29.3 PIVOT finite-sum lemmas

Small erased-column sum identities isolate the finite algebra used by the
PIVOT semantic proof.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- Sum a column-indexed expression over every column except {lit}`e`. -/
def sumExcept (e : Fin n) (f : Fin n → ℝ) : ℝ :=
  (Finset.univ.erase e).sum f

/-- Split a finite sum into its {lit}`e` term and all remaining terms. -/
theorem sum_eq_term_add_sumExcept (e : Fin n) (f : Fin n → ℝ) :
    (∑ j, f j) = f e + sumExcept e f := by
  rw [← Finset.univ.add_sum_erase f (Finset.mem_univ e)]
  rfl

/-- Division by a fixed scalar distributes over an erased-column sum. -/
theorem sumExcept_div_mul (e : Fin n) (a x : Fin n → ℝ) (p : ℝ) :
    sumExcept e (fun j => (a j / p) * x j) =
      sumExcept e (fun j => a j * x j) / p := by
  simp only [sumExcept, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The nonpivot coefficient update distributes across an erased-column sum. -/
theorem sumExcept_pivot_update (e : Fin n)
    (a r x : Fin n → ℝ) (q p : ℝ) :
    sumExcept e (fun j => (a j - q * (r j / p)) * x j) =
      sumExcept e (fun j => a j * x j) -
        q * (sumExcept e (fun j => r j * x j) / p) := by
  calc
    sumExcept e (fun j => (a j - q * (r j / p)) * x j) =
        sumExcept e (fun j => a j * x j) -
          sumExcept e (fun j => q * ((r j / p) * x j)) := by
      simp only [sumExcept, sub_mul, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = sumExcept e (fun j => a j * x j) -
        q * sumExcept e (fun j => (r j / p) * x j) := by
      simp only [sumExcept, Finset.mul_sum]
    _ = sumExcept e (fun j => a j * x j) -
        q * (sumExcept e (fun j => r j * x j) / p) := by
      rw [sumExcept_div_mul]

end Dictionary
end Chapter29
end CLRS
