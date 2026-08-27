import Mathlib

/-!
# Finite unordered-pair sums

This module isolates the finite reindexing used by the operational quicksort
bridge.  An off-diagonal sum over ordered pairs is rewritten as one sum over
strict pairs, with the two orientations added at each strict pair.

Main result:

- Theorem {lit}`CLRS.Chapter07.sum_offDiagonal_eq_sum_strictPairs`:
  off-diagonal and strict-pair sums agree.
-/

namespace CLRS
namespace Chapter07

/-- Summing both orientations of every strict pair is the same as summing an
off-diagonal matrix. -/
theorem sum_offDiagonal_eq_sum_strictPairs {n : Nat}
    (f : Fin n → Fin n → Nat) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n,
        if i.val < j.val then f i j + f j i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Fin.sum_univ_succ]
      have hsub :
          (∑ i : Fin n, ∑ j : Fin n,
              if i.succ ≠ j.succ then f i.succ j.succ else 0) =
            ∑ i : Fin n, ∑ j : Fin n,
              if i.val < j.val then
                f i.succ j.succ + f j.succ i.succ else 0 := by
        simpa using ih (fun i j => f i.succ j.succ)
      simp_rw [Finset.sum_add_distrib]
      rw [hsub]
      have hzero (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ :=
        (Fin.succ_ne_zero i).symm
      simp [Fin.succ_ne_zero, Finset.sum_add_distrib, add_assoc,
        add_left_comm, add_comm, hzero]

end Chapter07
end CLRS
