import CLRSLean.FourthEdition.Chapter_35.Section_35_5_The_Subset_Sum_Problem.Costed.LocalCorrectness

/-!
# CLRS Section 35.5 - Costed APPROX-SUBSET-SUM execution

The outer recursion composes the costed map, merge, trim, and filter scans.
The final wrapper scans the resulting list for its maximum.
-/

noncomputable section

namespace CLRS
namespace ApproxSubsetSum

/-- Costed construction of the trimmed lists.  The stored work is exactly the
sum of the recursively executed local scan counters plus one outer-loop unit. -/
def approxListsWithCost (δ : Real) (t : Nat) : List Nat → ListExecution
  | [] => ⟨[0], 0⟩
  | x :: xs =>
      let prior := approxListsWithCost δ t xs
      let shifted := mapAddWithCost x prior.value
      let merged := mergeWithCost prior.value shifted.value
      let trimmed := trimWithCost δ merged.value
      let kept := filterAtMostWithCost t trimmed.value
      ⟨kept.value,
        prior.work + shifted.work + merged.work + trimmed.work + kept.work + 1⟩

/-- Erasing the outer counter gives the existing semantic trimmed-list
construction. -/
theorem approxListsWithCost_value (δ : Real) (t : Nat) (xs : List Nat) :
    (approxListsWithCost δ t xs).value = approxLists δ t xs := by
  induction xs with
  | nil => simp [approxListsWithCost, approxLists]
  | cons x xs ih =>
      simp [approxListsWithCost, approxLists, ih, mapAddWithCost_value,
        mergeWithCost_value, trimWithCost_value, filterAtMostWithCost_value]

/-- A fold by {lit}`max` never drops its initial accumulator. -/
theorem le_foldl_max (best : Nat) (L : List Nat) :
    best ≤ L.foldl max best := by
  induction L generalizing best with
  | nil => simp
  | cons y ys ih =>
      exact (Nat.le_max_left best y).trans (ih (max best y))

/-- Every list member is bounded by a fold by {lit}`max`. -/
theorem mem_le_foldl_max (best : Nat) {L : List Nat} {x : Nat}
    (hx : x ∈ L) : x ≤ L.foldl max best := by
  induction L generalizing best with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with hxy | hx
      · subst x
        exact (Nat.le_max_right best y).trans (le_foldl_max (max best y) ys)
      · exact ih (max best y) hx

/-- A fold by {lit}`max` is below every common upper bound for its accumulator
and list elements. -/
theorem foldl_max_le (L : List Nat) (best bound : Nat)
    (hbest : best ≤ bound) (hmem : ∀ x ∈ L, x ≤ bound) :
    L.foldl max best ≤ bound := by
  induction L generalizing best with
  | nil => simpa using hbest
  | cons y ys ih =>
      simp only [List.foldl_cons]
      apply ih (max best y)
      · exact max_le hbest (hmem y (by simp))
      · intro x hx
        exact hmem x (by simp [hx])

/-- On a list containing {lit}`0`, the maximum scan agrees with the nonempty
Finset maximum used by {lit}`approxSum`. -/
theorem foldl_max_eq_toFinset_max' {L : List Nat} (h0 : 0 ∈ L) :
    L.foldl max 0 = L.toFinset.max' ⟨0, by simpa using h0⟩ := by
  apply le_antisymm
  · apply foldl_max_le
    · exact L.toFinset.le_max' 0 (by simpa using h0)
    · intro x hx
      exact L.toFinset.le_max' x (by simpa using hx)
  · have hmax : L.toFinset.max' ⟨0, by simpa using h0⟩ ∈ L := by
      simpa using L.toFinset.max'_mem ⟨0, by simpa using h0⟩
    exact mem_le_foldl_max 0 hmax

/-- Costed APPROX-SUBSET-SUM, including the final maximum scan. -/
def approxSubsetSumWithCost (xs : List Nat) (t : Nat) (ε : Real) : NatExecution :=
  let lists := approxListsWithCost (ε / (2 * (xs.length : Real))) t xs
  let answer := maximumWithCost lists.value
  ⟨answer.value, lists.work + answer.work⟩

/-- Erasing the complete execution counter gives the existing
{lit}`approxSum` result. -/
theorem approxSubsetSumWithCost_value (xs : List Nat) (t : Nat) (ε : Real) :
    (approxSubsetSumWithCost xs t ε).value = approxSum xs t ε := by
  rw [approxSubsetSumWithCost]
  simp only
  rw [maximumWithCost_value, approxListsWithCost_value]
  unfold approxSum
  apply foldl_max_eq_toFinset_max'
  exact zero_mem_approxLists _ _ _

end ApproxSubsetSum
end CLRS
