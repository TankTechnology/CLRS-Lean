import CLRSLean.FourthEdition.Chapter_07.Section_07_2_Performance_Of_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.Probability

/-!
# Executable random-priority quicksort model

A sample `priority : Equiv.Perm (Fin n)` is read as the input order of the
distinct ranks `0, ..., n-1`.  Running the existing first-pivot functional
quicksort on that list is therefore the standard random-permutation
implementation of randomized quicksort.

The comparison trace uses CLRS's exact pair characterization: ranks `i < j`
are compared precisely when `i` or `j` has minimum priority among the ranks in
`[i,j]`.  This predicate is executable after unfolding its finite quantifier,
so the total trace cardinality is a natural-number random variable on the same
permutation sample.
-/

namespace CLRS
namespace Chapter07

open CLRS.Probability

/-- Turn a priority permutation into the concrete list of distinct ranks fed
to the existing first-pivot quicksort. -/
def randomizedQuicksortInput {n : Nat} (priority : Equiv.Perm (Fin n)) : List Nat :=
  (List.finRange n).map (fun position => (priority position).val)

@[simp] theorem randomizedQuicksortInput_length {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    (randomizedQuicksortInput priority).length = n := by
  simp [randomizedQuicksortInput]

/-- The concrete randomized input contains every rank exactly once. -/
theorem randomizedQuicksortInput_perm_range {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    (randomizedQuicksortInput priority).Perm (List.range n) := by
  have hperm := (Equiv.Perm.map_finRange_perm priority).map (fun rank => rank.val)
  simpa [randomizedQuicksortInput, List.map_map, Function.comp_def] using hperm

/-- The output of the existing executable first-pivot quicksort on the sampled
priority order. -/
def randomizedQuicksortOutput {n : Nat} (priority : Equiv.Perm (Fin n)) : List Nat :=
  quickSort (randomizedQuicksortInput priority)

/-- Definitional refinement to the executable Chapter 7 quicksort.  This
theorem deliberately concerns the returned list; identifying the abstract
CLRS pair trace below with `quickSortComparisons` is a separate operational
counter-refinement obligation. -/
theorem randomizedQuicksortOutput_eq_quickSort {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortOutput priority =
      quickSort (randomizedQuicksortInput priority) := rfl

/-- Exact relation to the executable Chapter 7 quicksort: the sampled run is
ordered and preserves precisely the ranks `0, ..., n-1`. -/
theorem randomizedQuicksortOutput_correct {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    Ordered (randomizedQuicksortOutput priority) ∧
      (randomizedQuicksortOutput priority).Perm (List.range n) := by
  refine ⟨quickSort_ordered _, ?_⟩
  exact (quickSort_perm _).trans (randomizedQuicksortInput_perm_range priority)

/-- A constructive decision procedure for the CLRS comparison event. -/
def comparedInQuicksortDecidable (n : Nat) (i j : Fin n)
    (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    Decidable (comparedInQuicksort n i.val j.val hij j.isLt priority) := by
  unfold comparedInQuicksort IsFirstIn pos
  infer_instance

/-- The executable `0/1` contribution of one ordered rank pair. -/
def randomizedQuicksortComparisonBit {n : Nat} (i j : Fin n)
    (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) : Nat :=
  @ite Nat (comparedInQuicksort n i.val j.val hij j.isLt priority)
    (comparedInQuicksortDecidable n i j hij priority) 1 0

/-- Total cardinality of the CLRS rank-pair comparison trace induced by the
same priority sample that supplies `randomizedQuicksortInput`. -/
def randomizedQuicksortComparisonCount {n : Nat}
    (priority : Equiv.Perm (Fin n)) : Nat :=
  ∑ i : Fin n, ∑ j : Fin n,
    if hij : i.val < j.val then
      randomizedQuicksortComparisonBit i j hij priority
    else 0

/-- Casting an executable comparison bit to `Real` gives the corresponding
indicator random variable. -/
theorem randomizedQuicksortComparisonBit_cast {n : Nat} (i j : Fin n)
    (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    (randomizedQuicksortComparisonBit i j hij priority : Real) =
      @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
        (Classical.propDecidable _) := by
  unfold randomizedQuicksortComparisonBit indicator
  split <;> simp_all

/-- The natural comparison counter is pointwise equal, after casting, to the
finite sum of its pairwise indicators. -/
theorem randomizedQuicksortComparisonCount_cast {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    (randomizedQuicksortComparisonCount priority : Real) =
      ∑ i : Fin n, ∑ j : Fin n,
        if hij : i.val < j.val then
          @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
            (Classical.propDecidable _)
        else 0 := by
  unfold randomizedQuicksortComparisonCount
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split
  · apply randomizedQuicksortComparisonBit_cast
  · norm_num

end Chapter07
end CLRS
