import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B2_Dev

/-!
# Dev B3: the `(J, J']` window after the good event

Development file for the resident (B2) repair machinery: after `q`'s first
request at `J = t + 1 + j`, the repair schedule's cache is either `E − q'`
(subtraction) or `insert x (E − q')` (swap with an arbitrary page `x`)
throughout the rest of the window up to `J' = t + 1 + j'`.

Main results:

- `repairSchedule_after_J_step'`: one generic step — if the relation holds
  at `s`, it holds at `s + 1` (generalizes `repairSchedule_after_J_rel1` /
  `rel2` to an arbitrary swap page and request)
- `repairSchedule_after_J_window`: the `(J, J']` window relation, by
  induction from `repairSchedule_after_J`

This file is part of the `fifo_optimal` iteration (see `Dev/DESIGN.md`); it
will be merged into `S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

/-- Generic single step in the `(J, J')` window: if the repair cache at `s` is
subtractive (`E − q'`) or a swap (`insert x (E − q')`), then the same holds at `s + 1`. -/
lemma repairSchedule_after_J_step' (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq : q = e t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (hjj' : j < j')
    {s : ℕ} (hs1 : t + 1 + j < s) (hs2 : s < t + 1 + j')
    (hrel : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
        (schedCache e C₀ σ s).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
        insert x ((schedCache e C₀ σ s).erase q')) :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (s + 1) =
        (schedCache e C₀ σ (s + 1)).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (s + 1) =
        insert x ((schedCache e C₀ σ (s + 1)).erase q') := by
  let r : Page := σ.getD s 0
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t :=
    first_disagree_fault e σ C₀ ht hagree hdis
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, ← hq']; exact hqq')
  have hneq : r ≠ q' := by
    unfold r
    exact getD_ne_nextUse (k := s) hj' (by omega) hs2
  have hdsJ : repairSchedule e t q' (t + 1 + j') s = e s := by
    unfold repairSchedule
    simp [show s ≠ t by omega, show s ≠ t + 1 + j' by omega]
  rcases hrel with hsub | ⟨x, hswap⟩
  · -- subtractive input: the output is still subtractive
    rw [schedCache, schedCache]
    rw [hsub, hdsJ]
    left
    by_cases hr : r ∈ schedCache e C₀ σ s
    · rw [if_pos hr]
      have hr' : r ∈ (schedCache e C₀ σ s).erase q' := by
        rw [Finset.mem_erase]
        exact ⟨hneq, hr⟩
      rw [if_pos hr']
    · rw [if_neg hr]
      have hr' : r ∉ (schedCache e C₀ σ s).erase q' := by
        intro hm
        exact hr (Finset.mem_erase.mp hm).2
      rw [if_neg hr']
      rw [Finset.erase_insert_of_ne hneq]
      congr 1
      ext x
      simp [Finset.mem_erase, and_left_comm, and_assoc]
  · -- swap input (swap page `x`)
    rw [schedCache, schedCache]
    rw [hswap, hdsJ]
    by_cases hxr : x = r
    · -- the requested page is exactly the swap page `r`: repair hits
      subst x
      rw [if_pos (by simp [Finset.mem_insert, r])]
      by_cases hrE : r ∈ schedCache e C₀ σ s
      · -- `e` also hits: swap is preserved
        rw [if_pos hrE]
        right
        refine ⟨r, ?_⟩
        have hrE' : r ∈ (schedCache e C₀ σ s).erase q' := by
          rw [Finset.mem_erase]
          exact ⟨hneq, hrE⟩
        simp [hrE', r]
      · -- `e` faults: split on the case of `e s`
        rw [if_neg hrE]
        by_cases heq' : e s = q'
        · -- `e` evicts `q'`: subtractive
          left
          rw [heq']
          rw [Finset.erase_insert_of_ne hneq]
          congr 1
          ext x
          simp [Finset.mem_erase]
        · by_cases her : e s = r
          · -- `e` evicts `r` (`e`'s cache has no `r`): subtractive
            left
            rw [her]
            rw [Finset.erase_eq_of_notMem hrE]
            rw [Finset.erase_insert_of_ne hneq]
          · by_cases heE : e s ∈ (schedCache e C₀ σ s).erase q'
            · -- `e` evicts a page in `E − q'`: swap is preserved (the swap page becomes `e s`)
              right
              refine ⟨e s, ?_⟩
              rw [Finset.erase_insert_of_ne hneq]
              rw [Finset.insert_comm]
              congr 1
              have herase : ((schedCache e C₀ σ s).erase (e s)).erase q' =
                  ((schedCache e C₀ σ s).erase q').erase (e s) := by
                ext x
                simp [Finset.mem_erase, and_left_comm, and_assoc]
              rw [herase]
              exact (Finset.insert_erase heE).symm
            · -- `e` evicts a page outside the cache: subtractive
              left
              have heE' : e s ∉ schedCache e C₀ σ s := by
                intro hmem
                exact heE (Finset.mem_erase.mpr ⟨heq', hmem⟩)
              rw [Finset.erase_eq_of_notMem heE']
              rw [Finset.erase_insert_of_ne hneq]
    · -- the requested page is not the swap page
      by_cases hrE : r ∈ schedCache e C₀ σ s
      · -- double hit: swap is preserved
        have hr' : r ∈ insert x ((schedCache e C₀ σ s).erase q') := by
          rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_erase.mpr ⟨hneq, hrE⟩)
        rw [if_pos hr']
        rw [if_pos hrE]
        right
        refine ⟨x, ?_⟩
        rfl
      · -- double fault: split on the case of `e s`
        have hr' : r ∉ insert x ((schedCache e C₀ σ s).erase q') := by
          intro hm
          rcases Finset.mem_insert.mp hm with hxr' | hm
          · exact hxr hxr'.symm
          · exact hrE (Finset.mem_erase.mp hm).2
        rw [if_neg hr']
        rw [if_neg hrE]
        by_cases heq' : e s = q'
        · -- `e` evicts `q'`: subtractive when `x ∈ E − q'`, otherwise swap
          rw [heq']
          by_cases hxE : x ∈ (schedCache e C₀ σ s).erase q'
          · left
            rw [Finset.erase_insert_of_ne hneq]
            congr 1
            ext x
            simp [Finset.mem_erase, Finset.mem_insert, and_left_comm, and_assoc,
              hneq, hxE, r]
          · by_cases hxq' : x = q'
            · -- `x = q'`: `e` evicts `q'` and the swap page is also `q'` — subtractive
              subst x
              left
              rw [Finset.erase_insert_of_ne hneq]
              congr 1
              ext x
              simp [Finset.mem_erase, Finset.mem_insert]
            · -- `x ≠ q'`: swap is preserved
              right
              refine ⟨x, ?_⟩
              rw [Finset.erase_insert_of_ne hxq']
              rw [Finset.erase_insert_of_ne hneq]
              rw [Finset.insert_comm]
        · by_cases hxe : e s = x
          · -- `e` evicts `x`: subtractive
            rw [hxe]
            by_cases hxE : x ∈ (schedCache e C₀ σ s).erase q'
            · left
              rw [Finset.erase_insert_of_ne hneq]
              congr 1
              rw [Finset.insert_eq_of_mem hxE]
              ext x
              simp [Finset.mem_erase, and_left_comm, and_assoc]
            · left
              by_cases hxq' : x = q'
              · rw [hxq']
                have herase : (insert q' ((schedCache e C₀ σ s).erase q')).erase q' =
                    (schedCache e C₀ σ s).erase q' := by
                  exact Finset.erase_insert (by simp [Finset.mem_erase])
                rw [herase]
                rw [Finset.erase_insert_of_ne hneq]
                congr 1
                ext x
                simp [Finset.mem_erase]
              · have hxE' : x ∉ schedCache e C₀ σ s := by
                  intro hmem
                  exact hxE (Finset.mem_erase.mpr ⟨hxq', hmem⟩)
                rw [Finset.erase_insert hxE]
                rw [Finset.erase_insert_of_ne hneq]
                rw [Finset.erase_eq_of_notMem hxE']
          · -- `e` evicts some other page: swap is preserved
            right
            refine ⟨x, ?_⟩
            rw [Finset.erase_insert_of_ne hneq]
            rw [Finset.insert_comm]
            congr 1
            have herase1 : (insert x ((schedCache e C₀ σ s).erase q')).erase (e s) =
                insert x (((schedCache e C₀ σ s).erase q').erase (e s)) := by
              exact Finset.erase_insert_of_ne (by intro hx; exact hxe hx.symm)
            rw [herase1]
            congr 1
            ext x
            simp [Finset.mem_erase, and_left_comm, and_assoc]

/-- The `(J, J']` window: between `q`'s first request and `q'`'s first request, the repair
cache is `E − q'` (subtractive) or `insert x (E − q')` (swap). -/
lemma repairSchedule_after_J_window (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq : q = e t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (hjj' : j < j')
    {s : ℕ} (hs1 : t + 1 + j < s) (hs2 : s ≤ t + 1 + j') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
        (schedCache e C₀ σ s).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
        insert x ((schedCache e C₀ σ s).erase q') := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hsJ : s = t + 1 + j
      · subst s
        exact repairSchedule_after_J e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj'
      · have hs1' : t + 1 + j < s := by omega
        have hs2' : s < t + 1 + j' := by omega
        have hrel : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
              (schedCache e C₀ σ s).erase q'
            ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
              insert x ((schedCache e C₀ σ s).erase q') := by
          exact ih (by omega) (by omega)
        exact repairSchedule_after_J_step' e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj'
          hs1' hs2' hrel


end Caching

end CLRS
