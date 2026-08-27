import CLRSLean.FourthEdition.Chapter_35.Section_35_5_The_Subset_Sum_Problem.Costed.Execution

/-!
# CLRS Section 35.5 - Work bounds for costed APPROX-SUBSET-SUM

The bounds in this file concern the counters produced by the concrete
execution in `Costed.Execution`.  The model charges one unit for each list
addition, comparison, or outer-loop composition step.
-/

noncomputable section

namespace CLRS
namespace ApproxSubsetSum

/-- Every intermediate list is bounded using the one trimming parameter
selected from the original input length {lit}`n`.  In particular, the parameter is
not recomputed from the length of the remaining suffix. -/
theorem approxLists_uniform_length_bound {n t : Nat} {ε : Real}
    (hn : 0 < n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 1 ≤ t) (ys : List Nat) :
    ((approxLists (ε / (2 * (n : Real))) t ys).length : Real) ≤
      4 * (n : Real) * Real.log (t : Real) / ε + 2 := by
  let δ : Real := ε / (2 * (n : Real))
  have hnpos : 0 < (n : Real) := by exact_mod_cast hn
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact div_pos hε0 (by positivity)
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    have h2n : (1 : Real) ≤ 2 * (n : Real) := by nlinarith [hn1]
    have hεn : ε ≤ 2 * (n : Real) := le_trans hε1 h2n
    exact (div_le_iff₀ (by positivity : (0 : Real) < 2 * (n : Real))).mpr
      (by simpa using hεn)
  have hlogpos : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hlogt : 0 ≤ Real.log (t : Real) :=
    Real.log_nonneg (by exact_mod_cast ht)
  have hlogd : δ / 2 ≤ Real.log (1 + δ) :=
    log_one_add_ge_half (le_of_lt hδ0) hδle
  have hscaled : Real.log (t : Real) / Real.log (1 + δ) ≤
      4 * (n : Real) * Real.log (t : Real) / ε := by
    have hδ2 : 0 < δ / 2 := by positivity
    have hinv : (Real.log (1 + δ))⁻¹ ≤ (δ / 2)⁻¹ :=
      (inv_le_inv₀ hlogpos hδ2).2 hlogd
    have hδ2inv : (δ / 2)⁻¹ = 4 * (n : Real) / ε := by
      have h2d : (2 : Real) / δ = 4 * (n : Real) / ε := by
        dsimp [δ]
        field_simp [hε0.ne', ne_of_gt hnpos]
        ring
      calc
        (δ / 2)⁻¹ = 2 / δ := by field_simp [ne_of_gt hδ0]
        _ = 4 * (n : Real) / ε := h2d
    calc
      Real.log (t : Real) / Real.log (1 + δ) =
          Real.log (t : Real) * (Real.log (1 + δ))⁻¹ := by ring
      _ ≤ Real.log (t : Real) * (δ / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hlogt
      _ = Real.log (t : Real) * (4 * (n : Real) / ε) := by rw [hδ2inv]
      _ = 4 * (n : Real) * Real.log (t : Real) / ε := by ring
  have hlen := approxLists_length_bound (δ := δ) hδ0 t ht ys
  have hfinal : Real.log (t : Real) / Real.log (1 + δ) + 2 ≤
      4 * (n : Real) * Real.log (t : Real) / ε + 2 := by
    linarith
  have hgoal : ((approxLists δ t ys).length : Real) ≤
      4 * (n : Real) * Real.log (t : Real) / ε + 2 :=
    le_trans hlen hfinal
  simpa [δ] using hgoal

/-- The five local scans performed in one outer iteration use at most seven
times the prior list length. -/
private theorem localPipeline_work_le (δ : Real) (t x : Nat) (L : List Nat) :
    let shifted := mapAddWithCost x L
    let merged := mergeWithCost L shifted.value
    let trimmed := trimWithCost δ merged.value
    let kept := filterAtMostWithCost t trimmed.value
    shifted.work + merged.work + trimmed.work + kept.work ≤ 7 * L.length := by
  dsimp only
  have hshiftWork := mapAddWithCost_work x L
  have hshiftLen : (mapAddWithCost x L).value.length = L.length := by
    rw [mapAddWithCost_value]
    simp
  have hmergeWork := mergeWithCost_work_le L (mapAddWithCost x L).value
  have hmergeLen := mergeWithCost_length L (mapAddWithCost x L).value
  have htrimWork :=
    trimWithCost_work_le δ (mergeWithCost L (mapAddWithCost x L).value).value
  have htrimLen :=
    trimWithCost_length_le δ (mergeWithCost L (mapAddWithCost x L).value).value
  have hfilterWork := filterAtMostWithCost_work t
    (trimWithCost δ (mergeWithCost L (mapAddWithCost x L).value).value).value
  omega

/-- If all semantic intermediate lists are bounded by {lit}`B`, the actual outer
execution counter is at most `length * (7B + 1)`. -/
theorem approxListsWithCost_work_le_of_length_bound {δ B : Real} {t : Nat}
    (_hB : 0 ≤ B)
    (hbound : ∀ ys, ((approxLists δ t ys).length : Real) ≤ B) (xs : List Nat) :
    ((approxListsWithCost δ t xs).work : Real) ≤
      (xs.length : Real) * (7 * B + 1) := by
  induction xs with
  | nil => simp [approxListsWithCost]
  | cons x xs ih =>
      let prior := approxListsWithCost δ t xs
      let shifted := mapAddWithCost x prior.value
      let merged := mergeWithCost prior.value shifted.value
      let trimmed := trimWithCost δ merged.value
      let kept := filterAtMostWithCost t trimmed.value
      have hprior : (prior.work : Real) ≤ (xs.length : Real) * (7 * B + 1) := by
        simpa [prior] using ih
      have hlen : (prior.value.length : Real) ≤ B := by
        rw [approxListsWithCost_value]
        exact hbound xs
      have hpipeline :
          shifted.work + merged.work + trimmed.work + kept.work ≤
            7 * prior.value.length := by
        simpa [shifted, merged, trimmed, kept] using
          localPipeline_work_le δ t x prior.value
      have hpipelineReal :
          ((shifted.work + merged.work + trimmed.work + kept.work : Nat) : Real) ≤
            7 * (prior.value.length : Real) := by
        exact_mod_cast hpipeline
      push_cast at hpipelineReal
      have hstep :
          ((shifted.work + merged.work + trimmed.work + kept.work + 1 : Nat) : Real) ≤
            7 * B + 1 := by
        push_cast
        nlinarith
      rw [approxListsWithCost]
      dsimp only
      change ((prior.work + shifted.work + merged.work + trimmed.work + kept.work + 1 : Nat) : Real) ≤
        (((xs.length + 1 : Nat) : Real) * (7 * B + 1))
      push_cast
      push_cast at hstep
      ring_nf at hprior hstep ⊢
      nlinarith

/-- The counter returned by the complete execution is polynomial in the input
length, {lit}`log t`, and {lit}`1 / ε`.  The bound includes construction of every
intermediate list and the final maximum scan. -/
theorem approxSubsetSumWithCost_work_le {xs : List Nat} {t : Nat} {ε : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 1 ≤ t) :
    ((approxSubsetSumWithCost xs t ε).work : Real) ≤
      48 * ((xs.length : Real) + 1) ^ 2 *
        (Real.log (t : Real) + 1) / ε := by
  have hlog : 0 ≤ Real.log (t : Real) :=
    Real.log_nonneg (by exact_mod_cast ht)
  by_cases hnil : xs = []
  · subst xs
    have hratio : 1 ≤ (Real.log (t : Real) + 1) / ε := by
      apply (le_div_iff₀ hε0).2
      linarith
    have h48 : (0 : Real) ≤ 48 := by norm_num
    simp only [List.length_nil, Nat.cast_zero, zero_add, one_pow]
    rw [approxSubsetSumWithCost]
    simp [approxListsWithCost, maximumWithCost, maximumAuxWithCost]
    calc
      (1 : Real) ≤ 48 := by norm_num
      _ ≤ 48 * ((Real.log (t : Real) + 1) / ε) :=
        by simpa using mul_le_mul_of_nonneg_left hratio h48
      _ = 48 * (Real.log (t : Real) + 1) / ε := by ring
  · have hn : 0 < xs.length := by
      exact Nat.pos_of_ne_zero (fun hlen => hnil (List.eq_nil_of_length_eq_zero hlen))
    let n : Real := xs.length
    let B : Real := 4 * n * Real.log (t : Real) / ε + 2
    have hn0 : 0 ≤ n := by positivity
    have hn1 : 1 ≤ n := by
      dsimp [n]
      exact_mod_cast hn
    have hB0 : 0 ≤ B := by
      dsimp [B]
      have : 0 ≤ 4 * n * Real.log (t : Real) / ε := by positivity
      linarith
    have hbound : ∀ ys,
        ((approxLists (ε / (2 * (xs.length : Real))) t ys).length : Real) ≤ B := by
      intro ys
      simpa [B, n] using
        (approxLists_uniform_length_bound (n := xs.length) hn hε0 hε1 ht ys)
    have hlists := approxListsWithCost_work_le_of_length_bound
      (δ := ε / (2 * (xs.length : Real))) (B := B) hB0 hbound xs
    have hvalueLen :
        ((approxListsWithCost (ε / (2 * (xs.length : Real))) t xs).value.length : Real) ≤ B := by
      rw [approxListsWithCost_value]
      exact hbound xs
    have htotal :
        ((approxSubsetSumWithCost xs t ε).work : Real) ≤
          n * (7 * B + 1) + B := by
      rw [approxSubsetSumWithCost]
      simp only
      rw [maximumWithCost_work]
      push_cast
      simpa [n] using add_le_add hlists hvalueLen
    have hBstep : B ≤ 7 * B + 1 := by nlinarith
    have hcoarse :
        ((approxSubsetSumWithCost xs t ε).work : Real) ≤
          (n + 1) * (7 * B + 1) := by
      calc
        ((approxSubsetSumWithCost xs t ε).work : Real)
            ≤ n * (7 * B + 1) + B := htotal
        _ ≤ n * (7 * B + 1) + (7 * B + 1) := add_le_add_right hBstep _
        _ = (n + 1) * (7 * B + 1) := by ring
    have hnlog : n * Real.log (t : Real) ≤
        (n + 1) * (Real.log (t : Real) + 1) := by
      nlinarith [mul_nonneg hn0 hlog]
    have hεprod : ε ≤ (n + 1) * (Real.log (t : Real) + 1) := by
      have hone : 1 ≤ (n + 1) * (Real.log (t : Real) + 1) := by
        nlinarith [mul_nonneg hn0 hlog]
      exact le_trans hε1 hone
    have hinside :
        28 * n * Real.log (t : Real) + 15 * ε ≤
          48 * (n + 1) * (Real.log (t : Real) + 1) := by
      nlinarith
    have hpoly : (n + 1) * (7 * B + 1) ≤
        48 * (n + 1) ^ 2 * (Real.log (t : Real) + 1) / ε := by
      have hleft : (n + 1) * (7 * B + 1) =
          ((n + 1) * (28 * n * Real.log (t : Real) + 15 * ε)) / ε := by
        dsimp [B]
        field_simp [hε0.ne']
        ring
      rw [hleft]
      apply (div_le_div_iff_of_pos_right hε0).2
      have hmul := mul_le_mul_of_nonneg_left hinside (by linarith : 0 ≤ n + 1)
      nlinarith
    simpa [n] using le_trans hcoarse hpoly

/-- Kernel-checked FPTAS bundle for the costed execution: feasibility,
approximation quality, and polynomial work all refer to the same run. -/
theorem approxSubsetSumWithCost_fptas {xs : List Nat} {t : Nat} {ε : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 1 ≤ t) :
    let run := approxSubsetSumWithCost xs t ε
    run.value ∈ subsetSums xs ∧
      run.value ≤ t ∧
      (optimalSum xs t : Real) ≤ (1 + ε) * (run.value : Real) ∧
      (run.work : Real) ≤
        48 * ((xs.length : Real) + 1) ^ 2 *
          (Real.log (t : Real) + 1) / ε := by
  dsimp only
  refine ⟨?_, ?_, ?_, approxSubsetSumWithCost_work_le hε0 hε1 ht⟩
  · rw [approxSubsetSumWithCost_value]
    exact approxSum_mem_subsetSums xs t ε
  · rw [approxSubsetSumWithCost_value]
    exact approxSum_le_t xs t ε
  · rw [approxSubsetSumWithCost_value]
    exact approxSubsetSum_approx_lt xs t ε hε0 hε1

end ApproxSubsetSum
end CLRS
