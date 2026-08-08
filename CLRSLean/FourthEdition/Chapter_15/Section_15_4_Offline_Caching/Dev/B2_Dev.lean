import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S3_Optimality

namespace CLRS

namespace Caching

open Finset

/-- 在首次分歧 `t` 处双方 fault。 -/
lemma first_disagree_fault (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1)) :
    σ.getD t 0 ∉ schedCache e C₀ σ t := by
  intro hft
  have hFt : σ.getD t 0 ∈ schedCache (fifoSchedule σ C₀) C₀ σ t := by
    rw [← hagree t le_rfl]
    exact hft
  have hD : schedCache e C₀ σ (t + 1) = schedCache e C₀ σ t := by
    rw [schedCache]
    rw [if_pos hft]
  have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
      schedCache (fifoSchedule σ C₀) C₀ σ t := by
    rw [schedCache]
    rw [if_pos hFt]
  exact hdis ((hD.trans (hagree t le_rfl)).trans hF.symm)

/-- B2 好事件后的关系(swap 情形):`q` 的首次请求处 `d̂` 命中。 -/
lemma repairSchedule_after_J_rel1 (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
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
    (hrel1 : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) =
        insert q ((schedCache e C₀ σ (t + 1 + j)).erase q')) :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        (schedCache e C₀ σ (t + 1 + j + 1)).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        insert x ((schedCache e C₀ σ (t + 1 + j + 1)).erase q') := by
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t :=
    first_disagree_fault e σ C₀ ht hagree hdis
  have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
  have hqnotJ : q ∉ schedCache e C₀ σ (t + 1 + j) := by
    exact swap_q_not_mem e σ C₀ hq.symm (by rw [hq]; exact hqin) hft hj
      (by omega) le_rfl
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, ← hq']; exact hqq')
    have hrE : σ.getD (t + 1 + j) 0 ∈ insert q ((schedCache e C₀ σ (t + 1 + j)).erase q') := by
      rw [hsig]
      rw [Finset.mem_insert]
      left
      rfl
    by_cases hej : e (t + 1 + j) ∈ (schedCache e C₀ σ (t + 1 + j)).erase q'
    · -- e J ∈ E − q':swap 对 (e J, q')
      right
      refine ⟨e (t + 1 + j), ?_⟩
      change (if σ.getD (t + 1 + j) 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) then
          schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)
        else insert (σ.getD (t + 1 + j) 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)).erase
          (repairSchedule e t q' (t + 1 + j') (t + 1 + j)))) =
        insert (e (t + 1 + j)) ((if σ.getD (t + 1 + j) 0 ∈ schedCache e C₀ σ (t + 1 + j) then schedCache e C₀ σ (t + 1 + j)
          else insert (σ.getD (t + 1 + j) 0) ((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j)))).erase q')
      rw [hrel1]
      have hdsJ : repairSchedule e t q' (t + 1 + j') (t + 1 + j) = e (t + 1 + j) := by
        unfold repairSchedule
        simp [show t + 1 + j ≠ t by omega, show j ≠ j' by omega]
      rw [hdsJ]
      rw [if_pos hrE]
      rw [if_neg (by intro h; exact hqnotJ (hsig ▸ h))]
      rw [hsig]
      -- 目标:insert q (E − q') = insert (e J) ((insert q (E − e J)) − q')
      have hej1 : e (t + 1 + j) ≠ q' := (Finset.mem_erase.mp hej).1
      have hejE : e (t + 1 + j) ∈ schedCache e C₀ σ (t + 1 + j) := (Finset.mem_erase.mp hej).2
      have hEj : q ≠ e (t + 1 + j) := by
        intro h
        exact hqnotJ (h ▸ hejE)
      rw [Finset.erase_insert_of_ne hqne]
      rw [Finset.insert_comm]
      have hEq : (schedCache e C₀ σ (t + 1 + j)).erase q' =
          insert (e (t + 1 + j)) (((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j))).erase q') := by
        ext x
        constructor
        · intro hx
          have hxq' : x ≠ q' := (Finset.mem_erase.mp hx).1
          have hxin : x ∈ schedCache e C₀ σ (t + 1 + j) := (Finset.mem_erase.mp hx).2
          rw [Finset.mem_insert]
          by_cases hxe : x = e (t + 1 + j)
          · exact Or.inl hxe
          · exact Or.inr (Finset.mem_erase.mpr ⟨hxq', Finset.mem_erase.mpr ⟨hxe, hxin⟩⟩)
        · intro hx
          rw [Finset.mem_insert] at hx
          rcases hx with hxe | hxin
          · rw [hxe]
            exact Finset.mem_erase.mpr ⟨hej1, hejE⟩
          · have hx' := Finset.mem_erase.mp (Finset.mem_erase.mp hxin).2
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxin).1, hx'.2⟩
      rw [hEq]
    · -- e J ∉ E − q':减式
      left
      change (if σ.getD (t + 1 + j) 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) then
          schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)
        else insert (σ.getD (t + 1 + j) 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)).erase
          (repairSchedule e t q' (t + 1 + j') (t + 1 + j)))) =
        (if σ.getD (t + 1 + j) 0 ∈ schedCache e C₀ σ (t + 1 + j) then schedCache e C₀ σ (t + 1 + j)
          else insert (σ.getD (t + 1 + j) 0) ((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j)))).erase q'
      rw [hrel1]
      have hdsJ : repairSchedule e t q' (t + 1 + j') (t + 1 + j) = e (t + 1 + j) := by
        unfold repairSchedule
        simp [show t + 1 + j ≠ t by omega, show j ≠ j' by omega]
      rw [hdsJ]
      rw [if_pos hrE]
      rw [if_neg (by intro h; exact hqnotJ (hsig ▸ h))]
      rw [hsig]
      by_cases hejq' : e (t + 1 + j) = q'
      · rw [hejq']
        rw [Finset.erase_insert_of_ne hqne]
        have hErase : ((schedCache e C₀ σ (t + 1 + j)).erase q').erase q' =
            (schedCache e C₀ σ (t + 1 + j)).erase q' := by
          ext x
          simp [Finset.mem_erase]
        rw [hErase]
        rfl
      · have hejnotE : e (t + 1 + j) ∉ schedCache e C₀ σ (t + 1 + j) := by
          intro hmem
          exact hej (Finset.mem_erase.mpr ⟨hejq', hmem⟩)
        rw [Finset.erase_eq_of_notMem hejnotE]
        rw [Finset.erase_insert_of_ne hqne]
        rfl

/-- B2 好事件后的关系(减式情形):`q` 的首次请求处双方 fault。 -/
lemma repairSchedule_after_J_rel2 (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
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
    (hrel2 : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) =
        (schedCache e C₀ σ (t + 1 + j)).erase q') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        (schedCache e C₀ σ (t + 1 + j + 1)).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        insert x ((schedCache e C₀ σ (t + 1 + j + 1)).erase q') := by
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t :=
    first_disagree_fault e σ C₀ ht hagree hdis
  have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
  have hqnotJ : q ∉ schedCache e C₀ σ (t + 1 + j) := by
    exact swap_q_not_mem e σ C₀ hq.symm (by rw [hq]; exact hqin) hft hj
      (by omega) le_rfl
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, ← hq']; exact hqq')
    have hqnotÊ : q ∉ (schedCache e C₀ σ (t + 1 + j)).erase q' := by
      intro h
      exact hqnotJ (Finset.mem_erase.mp h).2
    have hrE' : σ.getD (t + 1 + j) 0 ∉ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) := by
      intro h
      exact hqnotÊ (by rwa [hrel2, ← hsig] at h)
    left
    change (if σ.getD (t + 1 + j) 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j) then
        schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)
      else insert (σ.getD (t + 1 + j) 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j)).erase
        (repairSchedule e t q' (t + 1 + j') (t + 1 + j)))) =
      (if σ.getD (t + 1 + j) 0 ∈ schedCache e C₀ σ (t + 1 + j) then schedCache e C₀ σ (t + 1 + j)
        else insert (σ.getD (t + 1 + j) 0) ((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j)))).erase q'
    rw [hrel2]
    have hdsJ : repairSchedule e t q' (t + 1 + j') (t + 1 + j) = e (t + 1 + j) := by
      unfold repairSchedule
      simp [show t + 1 + j ≠ t by omega, show t + 1 + j ≠ t + 1 + j' by omega]
    rw [hdsJ]
    rw [if_neg hrE']
    rw [if_neg (by intro h; exact hqnotJ (hsig ▸ h))]
    rw [hsig]
    -- 目标:insert q ((E − q') − e J) = (insert q (E − e J)) − q'
    rw [Finset.erase_insert_of_ne hqne]
    have herase_comm : ((schedCache e C₀ σ (t + 1 + j)).erase q').erase (e (t + 1 + j)) =
        ((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j))).erase q' := by
      ext x
      simp [Finset.mem_erase, and_left_comm, and_assoc]
    rw [herase_comm]

end Caching


/-- B2 中,在 `q` 的首次请求之后,repair 的 cache 是 `E − q'`(减式)或
`insert x (E − q')`(swap 对,`x` 是 `d̂` 保留而 `e` 逐出的页面)。 -/
lemma repairSchedule_after_J (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq : q = e t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (hjj' : j < j') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        (schedCache e C₀ σ (t + 1 + j + 1)).erase q'
      ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j + 1) =
        insert x ((schedCache e C₀ σ (t + 1 + j + 1)).erase q') := by
  have hwinJ := repairSchedule_window_swap' e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj'
    (s := t + 1 + j) (by omega) le_rfl
  rcases hwinJ with hrel1 | hrel2
  · exact repairSchedule_after_J_rel1 e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj' hrel1
  · exact repairSchedule_after_J_rel2 e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj' hrel2


end Caching

end CLRS
