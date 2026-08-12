import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Legacy.StateMachine.B11_CaseOne_B1

/-
# Dev B12: the no-window B1 step (case-one assembly)

After a case-one exchange the state has `win = none` and `hnb' = σ.length + 2`
(B10), so the next disagreement (when one exists) lands exactly on the
branch-1 spot `s₁` and the dispatch is case B with `win = none` (DESIGN.md
"Case-one branch-1 verified").  B11 supplied the no-window B1 step's
accounting (`caseone_b1_reverse_diff` + `caseone_b1_misses_le`); this file
builds the full state construction `step_b1_nowindow`, mirroring
`step_b1_alive` (B9) with the window machinery vacuous:

- the chain `windowExchange none r \ r = ∅` and `hd_eq` are trivial
  (`windowExchange none fb = fb`);
- `hmiss'` is `caseone_b1_misses_le` (the branch-1 spot's `hnoop` — the
  exchange's no-op eviction of the dead `q'` — is the B1 dispatch premise);
- `hdred'` reuses `repairSchedule_superset` (the state's `hdred` is
  vacuous at `σ.length + 2`, so the new bound `max hnb (J'''+1)` still
  only asserts at junk positions).

The branch-1 at-most-once (`case_one_branch1_once`, B10) is the assembly
justification: this no-window B1 step fires at most once per case-one
exchange, at the unique branch-1 spot.

Main results:

- `step_b1_nowindow`: the B1 step construction for `st.win = none` — the
  same `∃ st', st'.t0 = t₂ + 1` interface as `step_b1_alive`, taking the
  `hslack`/`hQ` supplies and the `hwin : st.win = none` premise.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/-- B1(无窗口,分支 1 位置)的完整状态构造:修复 `r` 后 `t0 = t₂+1`,slack
记账 `slack − bad`(`hslack` 前提给出 `bad ≤ slack`),Q/P 扩展
(`extend_h*` 胶水),reduced 界 `max hnb (J'''+1)`(状态 `hdred` 在
`σ.length+2` 起为空 ⟹ 新界仅断在 junk 处),`win = none` 保持。
`hwin : st.win = none` 使链/逐出一致平凡(`windowExchange none r = r`),
miss 记账由 `caseone_b1_misses_le`(B11)给出 —— 该步正是情形一交换后
下一次分歧(分支 1 位置 `s₁`)处的步。 -/
lemma step_b1_nowindow (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hslack : B1SlackHyp σ C₀ M)
    (hQ : HQsupplyHyp σ C₀ M)
    (hwin : st.win = none)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb) (ht₀t₂ : st.t0 ≤ t₂)
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hdis : schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : st.d t₂ ∉ schedCache st.d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''') :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1 := by
  let q'' : Page := fifoSchedule σ C₀ t₂
  let bad : ℕ := if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0
  let r : ℕ → Page := repairSchedule st.d t₂ q'' (t₂ + 1 + j''')
  have hQ_up : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ < tᵢ + 1 + j'' := (hQ st t₂).1
  have hQ_ext : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'' := (hQ st t₂).2
  have hbads : bad ≤ st.slack := by
    dsimp [bad]
    exact hslack st t₂ ht₂ ht₂hnb hagree hdis hnoop hftd hj'''
  have hq''res : q'' ∈ schedCache st.d C₀ σ t₂ := by
    have hfd := first_disagree st.d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hre2 : ∀ s, s ∉ ({t₂, t₂ + 1 + j'''} : Finset ℕ) → r s = st.d s := by
    intro s hs
    unfold r repairSchedule
    simp [show s ≠ t₂ by (intro h; exact hs (by simp [h])),
      show s ≠ t₂ + 1 + j''' by (intro h; exact hs (by simp [h]))]
  have hrt : r t₂ = q'' := by
    simpa [q''] using repairSchedule_at_t st.d t₂ q'' (t₂ + 1 + j''')
  have hrN : r (t₂ + 1 + j''') = q'' := by
    unfold r repairSchedule
    simp [q'']
  have hre : ∀ s, s < t₂ → r s = st.d s := by
    intro s hs
    exact hre2 s (by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with hEq | hmem
      · exact (ne_of_lt hs) hEq
      · exact (by omega : s ≠ t₂ + 1 + j''') (Finset.mem_singleton.mp hmem))
  have hce : ∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache st.d C₀ σ s := by
    intro s hs
    exact schedCache_repairSchedule_eq_e st.d t₂ q'' (t₂ + 1 + j''') (by omega) σ C₀ hs
  have hagree' : agreeWithFIF r C₀ σ (t₂ + 1) := by
    exact (repair_step st.d σ C₀ hC₀ ht₂ hagree hdis hnoop hj''').2
  have hmiss' : schedMisses r C₀ σ ≤ schedMisses st.d C₀ σ + bad := by
    simpa [r, bad] using caseone_b1_misses_le st.d σ C₀ hC₀ ht₂ hagree hdis hnoop hftd rfl hj'''
  have hbook' : schedMisses r C₀ σ + (st.slack - bad) ≤ M := by
    have h1 : schedMisses r C₀ σ + (st.slack - bad) ≤
        (schedMisses st.d C₀ σ + bad) + (st.slack - bad) := by
      exact Nat.add_le_add_right (by simpa [bad] using hmiss') (st.slack - bad)
    have h2 : (schedMisses st.d C₀ σ + bad) + (st.slack - bad) ≤
        schedMisses st.d C₀ σ + st.slack := by
      omega
    exact le_trans (le_trans h1 h2) st.hbook
  have hpast₂ : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q → tᵢ < t₂ := by
    intro tᵢ q''₀ htq
    have h := st.hpast tᵢ q''₀ htq
    omega
  have hwin_inv' : ∀ (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ),
      none = some (d_pre, t₀, q₀, q₀', j₀, j₀') →
      t₀ < t₂ + 1 ∧ d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
      (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
      σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
      nextUse σ (t₀ + 1) q₀ = some j₀ ∧
      (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
      nextUse σ (t₀ + 1) q₀' = some j₀' := by
    intro d_pre t₀ q₀ q₀' j₀ j₀' hEq
    cases hEq
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange none r σ C₀) C₀ σ s \
      schedCache r C₀ σ s ⊆ (insert (t₂, q'') st.Q).image Prod.snd := by
    intro s hs
    intro x hx
    simp [windowExchange] at hx
  have hd_eq' : ∀ s, s ∉ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      r s = windowExchange none r σ C₀ s := by
    intro s hs
    rfl
  have hdred' : ∀ s, max st.hnb (t₂ + 1 + j''' + 1) ≤ s →
      σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s := by
    have hsup : ∀ s, t₂ + 1 + j''' < s → schedCache st.d C₀ σ s ⊆ schedCache r C₀ σ s := by
      intro s hs
      exact repairSchedule_superset st.d σ C₀ hC₀ ht₂ hagree hdis hnoop rfl hj''' (s := s) hs
    intro s hs hfault
    have hnb_le : st.hnb ≤ s := by omega
    have hJ'''lt : t₂ + 1 + j''' < s := by omega
    have hdsin : st.d s ∈ schedCache st.d C₀ σ s := st.hdred s hnb_le (by
      intro h
      exact hfault (hsup s hJ'''lt h))
    rw [show r s = st.d s by
      unfold r repairSchedule
      simp [show s ≠ t₂ by omega, show s ≠ t₂ + 1 + j''' by omega]]
    exact hsup s hJ'''lt hdsin
  have hpast' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q → tᵢ < t₂ + 1 :=
    extend_hpast st.Q hpast₂
  have hQfifo' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      q''₀ = fifoSchedule σ C₀ tᵢ := by
    simpa [q''] using extend_hQfifo σ C₀ st.Q (rfl : q'' = fifoSchedule σ C₀ t₂) st.hQfifo
  have hP' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
    simpa [q''] using extend_hP σ st.Q st.P hj''' st.hP
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) →
      s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) := by
    simpa [q''] using extend_hP_in σ st.Q st.P hj''' hpast₂ st.hP_in
  have hcomp' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
    simpa [q''] using extend_hcomp' σ st.Q st.P r st.d hj''' hrt hrN hre2 st.hcomp
  have hpair' : ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache r C₀ σ tᵢ ∧ q''₀ ∈ schedCache r C₀ σ tᵢ ∧ r tᵢ = q''₀ := by
    simpa [q''] using extend_hpair σ C₀ st.Q r st.d hftd hq''res hrt hre hce hpast₂ st.hpair
  refine ⟨⟨r, t₂ + 1, st.slack - bad, max st.hnb (t₂ + 1 + j''' + 1),
    insert (t₂, q'') st.Q, st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ), none,
    hwin_inv', hagree', hbook', hchain', hd_eq', hdred', hpast', (by simpa [q''] using hQ_ext),
    hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

end Caching

end CLRS
