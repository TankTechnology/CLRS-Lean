import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.MergeSort.Correctness
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge_Sort_Recurrence

/-!
# CLRS Section 2.3 - Execution-derived merge-sort cost

The work recurrence in this module is derived from the counter accumulated by
the executable split--recurse--{lit}`mergeWithCost` program.  In particular, the
linear combine term follows from {lit}`merge_outputWrites_eq`; it is not installed
as an unrelated cost formula.
-/

namespace CLRS
namespace Chapter02

/-- Exact comparison-counter equation at a non-base execution node. -/
theorem mergeSortWithCost_comparisons_two_or_more (x y : Nat) (rest : List Nat) :
    let input := x :: y :: rest
    let middle := input.length / 2
    let leftRun := mergeSortWithCost (input.take middle)
    let rightRun := mergeSortWithCost (input.drop middle)
    (mergeSortWithCost input).comparisons =
      leftRun.comparisons + rightRun.comparisons +
        (mergeWithCost leftRun.value rightRun.value).comparisons := by
  dsimp only
  rw [mergeSortWithCost.eq_def]

/-- Exact output-write-counter equation at a non-base execution node. -/
theorem mergeSortWithCost_outputWrites_two_or_more (x y : Nat) (rest : List Nat) :
    let input := x :: y :: rest
    let middle := input.length / 2
    let leftRun := mergeSortWithCost (input.take middle)
    let rightRun := mergeSortWithCost (input.drop middle)
    (mergeSortWithCost input).outputWrites =
      leftRun.outputWrites + rightRun.outputWrites +
        (mergeWithCost leftRun.value rightRun.value).outputWrites := by
  dsimp only
  rw [mergeSortWithCost.eq_def]

/-- In a non-base execution, the work counter is the two recursive counters
plus exactly one output write for every input element. -/
theorem mergeSortWithCost_work_two_or_more (x y : Nat) (rest : List Nat) :
    let input := x :: y :: rest
    let middle := input.length / 2
    (mergeSortWithCost input).work =
      (mergeSortWithCost (input.take middle)).work +
        (mergeSortWithCost (input.drop middle)).work + input.length := by
  dsimp only
  rw [mergeSortWithCost.eq_def]
  dsimp only
  rw [merge_outputWrites_eq]
  have hleft := (mergeSortWithCost_perm
    ((x :: y :: rest).take ((x :: y :: rest).length / 2))).length_eq
  have hright := (mergeSortWithCost_perm
    ((x :: y :: rest).drop ((x :: y :: rest).length / 2))).length_eq
  rw [hleft, hright]
  rw [List.length_take, List.length_drop,
    Nat.min_eq_left (Nat.div_le_self (x :: y :: rest).length 2)]
  omega

/-- The execution work is determined only by input length. -/
theorem mergeSortWithCost_work_eq_of_length_eq {xs ys : List Nat}
    (hlen : xs.length = ys.length) :
    (mergeSortWithCost xs).work = (mergeSortWithCost ys).work := by
  refine WellFounded.induction (measure List.length).wf xs
    (C := fun xs => ∀ ys, xs.length = ys.length →
      (mergeSortWithCost xs).work = (mergeSortWithCost ys).work) ?_ ys hlen
  intro xs ih ys hlen
  cases xs with
  | nil =>
    have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    rfl
  | cons x tail =>
    cases tail with
    | nil =>
      have hys : ys.length = 1 := by simpa using hlen.symm
      obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hys
      simp [mergeSortWithCost.eq_def]
    | cons y rest =>
      cases ys with
      | nil => simp at hlen
      | cons x' tail' =>
        cases tail' with
        | nil => simp at hlen
        | cons y' rest' =>
          let input := x :: y :: rest
          let input' := x' :: y' :: rest'
          let middle := input.length / 2
          let middle' := input'.length / 2
          have hinput : input.length = input'.length := by simpa [input, input'] using hlen
          have hmiddle : middle = middle' := by simp [middle, middle', hinput]
          have hleftLength : (input.take middle).length < input.length := by
            simp [middle, input]
            omega
          have hrightLength : (input.drop middle).length < input.length := by
            simp [middle, input]
            omega
          have htakeLength :
              (input.take middle).length = (input'.take middle').length := by
            simp [List.length_take, hinput, hmiddle]
          have hdropLength :
              (input.drop middle).length = (input'.drop middle').length := by
            simp [List.length_drop, hinput, hmiddle]
          have ihLeft := ih (input.take middle) (by
            change (input.take middle).length < input.length
            exact hleftLength) (input'.take middle') htakeLength
          have ihRight := ih (input.drop middle) (by
            change (input.drop middle).length < input.length
            exact hrightLength) (input'.drop middle') hdropLength
          rw [mergeSortWithCost_work_two_or_more,
            mergeSortWithCost_work_two_or_more]
          rw [ihLeft, ihRight, hinput]

/-- Every execution's work counter is the canonical length-indexed work. -/
theorem mergeSortWithCost_work_eq_length (xs : List Nat) :
    (mergeSortWithCost xs).work = mergeSortWork xs.length := by
  unfold mergeSortWork
  apply mergeSortWithCost_work_eq_of_length_eq
  simp

/-- Actual head comparisons are bounded by the execution work charged from
the same recursive run. -/
theorem mergeSortWithCost_comparisons_le_work (xs : List Nat) :
    (mergeSortWithCost xs).comparisons ≤ (mergeSortWithCost xs).work := by
  refine WellFounded.induction (measure List.length).wf xs
    (C := fun xs => (mergeSortWithCost xs).comparisons ≤
      (mergeSortWithCost xs).work) ?_
  intro xs ih
  cases xs with
  | nil => simp [mergeSortWithCost.eq_def]
  | cons x tail =>
    cases tail with
    | nil => simp [mergeSortWithCost.eq_def]
    | cons y rest =>
      let input := x :: y :: rest
      let middle := input.length / 2
      let left := input.take middle
      let right := input.drop middle
      let leftRun := mergeSortWithCost left
      let rightRun := mergeSortWithCost right
      have hleftLength : left.length < input.length := by
        simp [left, middle, input]
        omega
      have hrightLength : right.length < input.length := by
        simp [right, middle, input]
        omega
      have ihLeft : leftRun.comparisons ≤ leftRun.work := by
        apply ih left
        change left.length < input.length
        exact hleftLength
      have ihRight : rightRun.comparisons ≤ rightRun.work := by
        apply ih right
        change right.length < input.length
        exact hrightLength
      have hmerge := merge_comparisons_le leftRun.value rightRun.value
      have hwrites := merge_outputWrites_eq leftRun.value rightRun.value
      rw [mergeSortWithCost.eq_def]
      dsimp only
      simp only [leftRun, rightRun, left, right, middle, input] at ihLeft ihRight hmerge hwrites ⊢
      omega

/-- Base work for the empty input. -/
@[simp] theorem mergeSortWork_zero : mergeSortWork 0 = 0 := by
  simp [mergeSortWork, mergeSortWithCost.eq_def]

/-- Base work for a singleton input. -/
@[simp] theorem mergeSortWork_one : mergeSortWork 1 = 1 := by
  simp [mergeSortWork, mergeSortWithCost.eq_def]

/-- Exact floor/ceiling recurrence derived from the executable work counter. -/
theorem mergeSortWork_recurrence_nat (n : Nat) (hn : 2 ≤ n) :
    mergeSortWork n =
      mergeSortWork (n / 2) + mergeSortWork ((n + 1) / 2) + n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by exact ⟨n - 2, by omega⟩
  change (mergeSortWithCost (List.replicate (k + 2) 0)).work =
    mergeSortWork ((k + 2) / 2) +
      mergeSortWork ((k + 2 + 1) / 2) + (k + 2)
  rw [show List.replicate (k + 2) 0 = 0 :: 0 :: List.replicate k 0 by
    simp [List.replicate_succ]]
  rw [mergeSortWithCost_work_two_or_more]
  rw [mergeSortWithCost_work_eq_length, mergeSortWithCost_work_eq_length]
  rw [List.length_take, List.length_drop]
  simp only [List.length_cons, List.length_replicate]
  have hnorm : k + 1 + 1 = k + 2 := by omega
  rw [hnorm]
  have hceil : k + 2 - (k + 2) / 2 = (k + 2 + 1) / 2 := by omega
  rw [Nat.min_eq_left (Nat.div_le_self (k + 2) 2), hceil]

/-- The real cast of the execution-derived work satisfies the textbook
all-input merge-sort recurrence. -/
theorem mergeSortWork_recurrence :
    MergeSortRecurrence.Recurrence (fun n => (mergeSortWork n : Real)) := by
  intro n hn
  change (mergeSortWork n : Real) =
    (mergeSortWork (n / 2) : Real) +
      (mergeSortWork ((n + 1) / 2) : Real) + (n : Real)
  exact_mod_cast mergeSortWork_recurrence_nat n hn

/-- The execution-derived work does not decrease when the input length grows
by one. -/
private theorem mergeSortWork_le_succ : ∀ n, mergeSortWork n ≤ mergeSortWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ 1
      · interval_cases n
        · simp
        · rw [mergeSortWork_recurrence_nat 2 (by norm_num)]
          norm_num
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hfloorEven : 2 * m / 2 = m := by omega
          have hceilEven : (2 * m + 1) / 2 = m := by omega
          have hceilOdd : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [mergeSortWork_recurrence_nat (2 * m) (by omega),
            mergeSortWork_recurrence_nat (2 * m + 1) (by omega),
            hfloorEven, hceilEven, hceilOdd]
          have ihm := ih m (by omega)
          omega
        · have hfloorOdd : (2 * m + 1) / 2 = m := by omega
          have hceilOdd : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have hceilEven : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
          rw [mergeSortWork_recurrence_nat (2 * m + 1) (by omega),
            mergeSortWork_recurrence_nat (2 * m + 1 + 1) (by omega),
            hfloorOdd, hceilOdd, hceilEven]
          have ihm := ih m (by omega)
          omega

/-- The work read from the executable merge sort is monotone in input size. -/
theorem mergeSortWork_monotone : Monotone mergeSortWork :=
  monotone_nat_of_le_succ mergeSortWork_le_succ

/-- The real-valued view of the execution work satisfies the all-input
absolute-value monotonicity interface. -/
theorem mergeSortWork_monotoneAbs :
    Chapter04.MonotoneAbs (fun n => (mergeSortWork n : Real)) :=
  Chapter04.monotoneAbs_natCast mergeSortWork_monotone

/-- The work counter of the executable merge sort is {lit}`Theta(n log n)` on all
natural input lengths. -/
theorem mergeSortWork_isBigTheta_nlogn :
    Chapter03.isBigTheta (fun n => (mergeSortWork n : Real))
      (fun n => (n : Real) * Real.log (n : Real)) := by
  exact MergeSortRecurrence.theta_n_log_n_all_inputs
    (fun n => (mergeSortWork n : Real))
    mergeSortWork_recurrence
    (by norm_num)
    mergeSortWork_monotoneAbs

end Chapter02
end CLRS
