import CLRSLean.FourthEdition.Chapter_02

open CLRS.Chapter02

#check insertionSortComparisons_le_worst
#check insertionSortWorstInput
#check insertionSortWorstInput_length
#check insertionSortComparisons_worst_input
#check insertionSortWorstComparisons_isGreatest
#check insertionSortComparisons_worst_case_theta

example (xs : List Nat) :
    insertionSortComparisons xs ≤ insertionSortWorstComparisons xs.length :=
  insertionSortComparisons_le_worst xs

example (n : Nat) : ∃ xs : List Nat, xs.length = n ∧
    insertionSortComparisons xs = insertionSortWorstComparisons n := by
  exact ⟨insertionSortWorstInput n, insertionSortWorstInput_length n,
    insertionSortComparisons_worst_input n⟩

example (n : Nat) : IsGreatest
    {c | ∃ xs : List Nat, xs.length = n ∧ insertionSortComparisons xs = c}
    (insertionSortWorstComparisons n) :=
  insertionSortWorstComparisons_isGreatest n

example : insertionSortComparisons [] = 0 := rfl
example : insertionSortComparisons [7] = 0 := rfl
example : insertionSortComparisons [4, 3, 2, 1, 0] = 10 := by decide
example : insertionSortComparisons [2, 2, 2, 2] = 3 := by decide
