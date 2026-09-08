import CLRSLean.FourthEdition.Chapter_08.Section_08_1_Lower_Bound_For_Sorting

/-!
# A comparison lower bound attained by a reachable run

Structural height can include infeasible branches. The counted interpreter
follows the actual comparisons of the original interpreter. Truncating a tree
at a uniform bound on these runs preserves every answer, so the factorial leaf
argument applies to that bound. Maximizing the counter over the finite input
permutations then gives an actual witness.
-/

namespace CLRS.Chapter08

/-- Interpret the comparison tree, returning the reached leaf and comparison count. -/
def SortTree.runWithCost (T : SortTree n) (π : Equiv.Perm (Fin n)) : SortTree n × Nat :=
  match T with
  | .leaf p => (.leaf p, 0)
  | .node i j l r =>
      let result := if π i ≤ π j then l.runWithCost π else r.runWithCost π
      (result.1, result.2 + 1)

theorem SortTree.runWithCost_result (T : SortTree n) (π : Equiv.Perm (Fin n)) :
    (T.runWithCost π).1 = T.run π := by
  induction T with
  | leaf p => rfl
  | node i j l r ihl ihr =>
      by_cases h : π i ≤ π j <;> simp [runWithCost, run, h, ihl, ihr]

/-- Truncate only for the counting argument, using an arbitrary leaf at the cutoff. -/
private def truncate (d : Nat) (T : SortTree n) : SortTree n :=
  match d, T with
  | _, .leaf p => .leaf p
  | 0, .node _ _ _ _ => .leaf 1
  | d + 1, .node i j l r => .node i j (truncate d l) (truncate d r)

private theorem truncate_height (d : Nat) (T : SortTree n) :
    (truncate d T).height ≤ d := by
  induction d generalizing T with
  | zero => cases T <;> simp [truncate, SortTree.height]
  | succ d ih =>
      cases T with
      | leaf p => simp [truncate, SortTree.height]
      | node i j l r =>
          simp only [truncate, SortTree.height]
          have hl := ih l
          have hr := ih r
          omega

private theorem truncate_run (d : Nat) (T : SortTree n) (π : Equiv.Perm (Fin n))
    (h : (T.runWithCost π).2 ≤ d) : (truncate d T).run π = T.run π := by
  induction d generalizing T with
  | zero =>
      cases T with
      | leaf p => rfl
      | node i j l r =>
          by_cases hc : π i ≤ π j <;> simp [SortTree.runWithCost, hc] at h
  | succ d ih =>
      cases T with
      | leaf p => rfl
      | node i j l r =>
          by_cases hc : π i ≤ π j
          · simp only [SortTree.runWithCost, hc, if_true, Nat.add_le_add_iff_right] at h
            simpa only [truncate, SortTree.run, hc, if_true] using ih l h
          · simp only [SortTree.runWithCost, hc, if_false, Nat.add_le_add_iff_right] at h
            simpa only [truncate, SortTree.run, hc, if_false] using ih r h

/-- Any bound on all reachable comparison counts must accommodate all input permutations. -/
theorem factorial_le_two_pow_run_bound {T : SortTree n} (hT : CorrectSort T)
    (d : Nat) (hbound : ∀ π, (T.runWithCost π).2 ≤ d) : n.factorial ≤ 2 ^ d := by
  have htr : CorrectSort (truncate d T) := by
    intro π
    rw [truncate_run d T π (hbound π)]
    exact hT π
  exact (factorial_le_leafCount_of_correctSort htr).trans
    ((leafCount_le_two_pow_height _).trans
      (Nat.pow_le_pow_right (by norm_num) (truncate_height d T)))

/-- There is an input attaining the information-theoretic comparison lower bound. -/
theorem comparisonSort_exists_run_log_factorial {T : SortTree n} (hT : CorrectSort T) :
    ∃ π : Equiv.Perm (Fin n),
      Real.logb 2 (n.factorial : ℝ) ≤ ((T.runWithCost π).2 : ℝ) := by
  classical
  obtain ⟨π, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun π => (T.runWithCost π).2)
    Finset.univ_nonempty
  refine ⟨π, ?_⟩
  have hfac := factorial_le_two_pow_run_bound hT (T.runWithCost π).2
    (fun ρ => hmax ρ (Finset.mem_univ _))
  have hreal : (n.factorial : ℝ) ≤ (2 : ℝ) ^ (T.runWithCost π).2 := by
    exact_mod_cast hfac
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (n.factorial : ℝ)) hreal
  simpa [Real.logb_pow, Real.logb_self_eq_one] using hlog

/-- The comparison lower bound concerns an actual input, even with unreachable branches. -/
theorem comparisonSort_exists_run_lowerBound (n : Nat) (hn : 2 ≤ n)
    {T : SortTree n} (hT : CorrectSort T) :
    ∃ π : Equiv.Perm (Fin n),
      ((n : ℝ) / 2) * Real.logb 2 (n : ℝ) ≤ ((T.runWithCost π).2 : ℝ) := by
  obtain ⟨π, hπ⟩ := comparisonSort_exists_run_log_factorial hT
  exact ⟨π, (logb_factorial_ge_half_mul_logb n (by omega)).trans hπ⟩

end CLRS.Chapter08
