import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.Bridge
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.OperationalBridge.PairTraceToBST

/-!
# Pointwise operational bridge for randomized quicksort

The abstract CLRS rank-pair trace and the recursive executable quicksort
counter have independently been normalized to the total depth of the same
randomly built BST.  Their composition gives the pointwise operational
refinement and transfers the exact expectation and asymptotic theorem to the
actual recursive comparison counter.
-/

namespace CLRS
namespace Chapter07

open CLRS.Probability
open Chapter03

/-- The CLRS pair-trace counter is pointwise identical to the comparisons made
by the recursive executable quicksort on the sampled permutation input. -/
theorem randomizedQuicksortComparisonCount_eq_quickSortComparisons {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortComparisonCount priority =
      quickSortComparisons (randomizedQuicksortInput priority) := by
  rw [randomizedQuicksortComparisonCount_eq_totalDepth priority]
  exact (quickSortComparisons_randomizedInput_eq_totalDepth priority).symm

/-- Expected comparison count of the actual recursive quicksort counter over
the uniform finite permutation sample space. -/
noncomputable def operationalRandomizedQuicksortExpectedComparisons
    (n : Nat) : Real :=
  fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
    (quickSortComparisons (randomizedQuicksortInput priority) : Real))

/-- The operational and pair-trace expectations are equal because their
counters agree for every individual permutation. -/
theorem operationalRandomizedQuicksortExpectedComparisons_eq_explicit
    (n : Nat) :
    operationalRandomizedQuicksortExpectedComparisons n =
      explicitRandomizedQuicksortExpectedComparisons n := by
  unfold operationalRandomizedQuicksortExpectedComparisons
  unfold explicitRandomizedQuicksortExpectedComparisons
  congr 1
  funext priority
  exact_mod_cast
    (randomizedQuicksortComparisonCount_eq_quickSortComparisons priority).symm

/-- The actual recursive comparison counter has exactly the textbook closed
form in expectation. -/
theorem operationalRandomizedQuicksortExpectedComparisons_eq (n : Nat) :
    operationalRandomizedQuicksortExpectedComparisons n =
      expectedComparisonsReal n := by
  rw [operationalRandomizedQuicksortExpectedComparisons_eq_explicit]
  exact explicitRandomizedQuicksortExpectedComparisons_eq n

/-- The expected number of comparisons performed by the actual recursive
quicksort implementation is `Theta(n log n)`. -/
theorem operationalRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn :
    isBigTheta operationalRandomizedQuicksortExpectedComparisons
      (fun n : Nat => (n : Real) * Real.log (n : Real)) := by
  have hfun : operationalRandomizedQuicksortExpectedComparisons =
      explicitRandomizedQuicksortExpectedComparisons := by
    funext n
    exact operationalRandomizedQuicksortExpectedComparisons_eq_explicit n
  rw [hfun]
  exact explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn

end Chapter07
end CLRS
