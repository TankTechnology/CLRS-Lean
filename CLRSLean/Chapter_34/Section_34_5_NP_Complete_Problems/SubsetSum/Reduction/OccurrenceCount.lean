import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.ColumnSemantics

/-!
# Counting true literal occurrences

The selected item for variable `i` represents exactly the literal made true by
the assignment.  Summing its multiplicity in a clause over all variables
therefore counts the clause's true literal occurrences, including duplicates.
-/

namespace CLRS.Chapter34.SubsetSumReduction

@[simp] theorem literalIndex_itemLiteral (index : Nat) (truth : Bool) :
    literalIndex (itemLiteral index truth) = index := by
  cases truth <;> simp [literalIndex, itemLiteral]

theorem itemLiteral_eq_iff
    (assignment : Nat → Bool) (index : Nat) (literal : Literal) :
    itemLiteral index (assignment index) = literal ↔
      index = literalIndex literal ∧ evalLit assignment literal := by
  cases literal with
  | pos x =>
      constructor
      · intro heq
        by_cases htrue : assignment index = true
        · have hindex : index = x := by
            simpa [itemLiteral, htrue] using heq
          subst index
          exact ⟨rfl, by simpa [literalIndex, evalLit] using htrue⟩
        · have hfalse : assignment index = false :=
            Bool.eq_false_of_not_eq_true htrue
          simp [itemLiteral, hfalse] at heq
      · rintro ⟨rfl, heval⟩
        simpa [literalIndex, evalLit, itemLiteral] using heval
  | neg x =>
      constructor
      · intro heq
        by_cases hfalse : assignment index = false
        · have hindex : index = x := by
            simpa [itemLiteral, hfalse] using heq
          subst index
          exact ⟨rfl, by simpa [literalIndex, evalLit] using hfalse⟩
        · have htrue : assignment index = true :=
            Bool.eq_true_of_not_eq_false hfalse
          simp [itemLiteral, htrue] at heq
      · rintro ⟨rfl, heval⟩
        simpa [literalIndex, evalLit, itemLiteral] using heval

theorem sum_itemLiteral_indicator
    (assignment : Nat → Bool) {variableCount : Nat} {literal : Literal}
    (hbound : literalIndex literal < variableCount) :
    (∑ index ∈ Finset.range variableCount,
        if (literal == itemLiteral index (assignment index)) = true then 1 else 0) =
      if evalLitBool assignment literal then 1 else 0 := by
  by_cases heval : evalLit assignment literal
  · have hevalBool : evalLitBool assignment literal = true :=
      (evalLitBool_eq_true assignment literal).2 heval
    rw [Finset.sum_eq_single (literalIndex literal)]
    · simp [hevalBool, (itemLiteral_eq_iff assignment _ literal).2
        ⟨rfl, heval⟩]
    · intro index hindex hne
      have hnot : itemLiteral index (assignment index) ≠ literal := by
        intro heq
        exact hne ((itemLiteral_eq_iff assignment index literal).1 heq).1
      simp [Ne.symm hnot]
    · simp [hbound]
  · have hevalBool : evalLitBool assignment literal = false :=
      (evalLitBool_eq_false assignment literal).2 heval
    simp only [hevalBool, Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro index hindex
    have hnot : itemLiteral index (assignment index) ≠ literal := by
      intro heq
      exact heval ((itemLiteral_eq_iff assignment index literal).1 heq).2
    simp [Ne.symm hnot]

/-- Number of true literal occurrences in a clause, expressed through the
variable-choice item multiplicities used by the reduction. -/
def assignmentClauseCount (variableCount : Nat)
    (assignment : Nat → Bool) (clause : Clause) : Nat :=
  ∑ index ∈ Finset.range variableCount,
    clause.count (itemLiteral index (assignment index))

theorem assignmentClauseCount_eq_filter_length
    (assignment : Nat → Bool) {variableCount : Nat} {clause : Clause}
    (hbound : ∀ literal ∈ clause, literalIndex literal < variableCount) :
    assignmentClauseCount variableCount assignment clause =
      (clause.filter (fun literal => evalLitBool assignment literal)).length := by
  induction clause with
  | nil => simp [assignmentClauseCount]
  | cons literal rest ih =>
      have hliteral : literalIndex literal < variableCount :=
        hbound literal (by simp)
      have hrest : ∀ current ∈ rest, literalIndex current < variableCount := by
        intro current hmem
        exact hbound current (by simp [hmem])
      simp only [assignmentClauseCount, List.count_cons,
        Finset.sum_add_distrib]
      have hih := ih hrest
      unfold assignmentClauseCount at hih
      rw [hih, sum_itemLiteral_indicator assignment hliteral]
      by_cases heval : evalLitBool assignment literal = true <;>
        simp [heval]

theorem assignmentClauseCount_pos
    (assignment : Nat → Bool) {variableCount : Nat} {clause : Clause}
    (hbound : ∀ literal ∈ clause, literalIndex literal < variableCount)
    (heval : evalClause assignment clause) :
    0 < assignmentClauseCount variableCount assignment clause := by
  rw [assignmentClauseCount_eq_filter_length assignment hbound]
  rcases heval with ⟨literal, hliteral, heval⟩
  have hbool : evalLitBool assignment literal = true :=
    (evalLitBool_eq_true assignment literal).2 heval
  have : literal ∈ clause.filter (fun current => evalLitBool assignment current) := by
    simp [hliteral, hbool]
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem this)

theorem assignmentClauseCount_le_length
    (assignment : Nat → Bool) {variableCount : Nat} {clause : Clause}
    (hbound : ∀ literal ∈ clause, literalIndex literal < variableCount) :
    assignmentClauseCount variableCount assignment clause ≤ clause.length := by
  rw [assignmentClauseCount_eq_filter_length assignment hbound]
  exact List.length_filter_le _ _

end CLRS.Chapter34.SubsetSumReduction
