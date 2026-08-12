import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B8_HnotE

/-
# Dev B9: the iterate_main assembly (checkpoint)

The concrete instantiation of `iterate_main`'s abstract case-step
supplies `hB1`/`hB2`/`hAone` with the kernel-checked case-step lemmas
and the extension glue.  The checkpoint wires everything that is
proved and leaves the genuinely open pieces as **documented
hypotheses** (referencing `Dev/DESIGN.md`) — no `sorry` (the
repository checker forbids them on `main`):

1. `hQ_open`: the hQ-strictness/extension — the state's `hQ` field
   over the full-history `Q` is empirically false (a pair whose nop
   has passed can never satisfy the new bound), and `b2_ehit_ne` /
   `b2_hnotE` / `past_pair_first_request_after` need the upgraded
   bound at the B2 disagreement.  See DESIGN.md "hQ-extension
   blocker".
2. `hslack_open`: the B1 slack invariant `bad ≤ slack` — the q₀'-half
   is proved (`b1_exchange_no_bad_q0` + `b1_bad_le_slack_q0`, up to
   the `1 ≤ slack` derivation — the "q₀'-B1 is the first step after
   the exchange" slack composition), but the non-q₀' half crashes 164
   times under all identified credits.  See DESIGN.md
   "slack-accounting blocker" and "Non-q₀' B1 pairing proposal".
3. `hcaseone_open`: the case-one exchange's reducedness — the state's
   `hdred` field from `t+1` fails at the at-most-one branch-1 fault
   (`d s = q'`, the exchange's no-op eviction of the dead `q'`);
   `iterate_main_case_one` proves the OR-form
   `e s ∈ E_s ∨ d s = q'`.  See DESIGN.md "Case one".
4. `hB2dead_open`: the B2 dead-page step constructions — the case
   steps `iterate_main_case_b2_q_dead` / `iterate_main_case_b2_qp_dead`
   do not exist yet (the keep-swaps `repair_keep_swap_cur_qp_dead` and
   the chain variants are done; the step assembly is not).  See
   DESIGN.md "Remaining for iterate_main" item (3).

The assembled `fifo_optimal_assembled` closes once the four hypotheses
are proved; the Dev → S3 merge happens at that point (the Dev files
import S3, so the assembled proof cannot live in S3 before the merge).

Main results:

- `iterate_main_assembled`: the induction with the concrete case
  constructions (case-one, B1-alive, B1-dead, B2-alive wired; the
  dead-page B2 steps via `hB2dead_open`)
- `fifo_optimal_assembled`: CLRS Theorem 15.5 from the initial state

This file is part of the `fifo_optimal` iteration; it will be merged
into `S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/- ### 开放前提(对应 DESIGN.md 的 blockers)

- `hQ_open`:`Q` 中活对在 B2 分歧处的严格界 `t₂ < tᵢ + 1 + j''`
  (hQ 扩展/严格化,见 DESIGN "hQ-extension blocker");
- `hslack_open`:B1 步骤的 `bad ≤ slack`(q₀' 半边已证到
  `1 ≤ slack` 的推导;非 q₀' 半边见 DESIGN "Non-q₀' B1 pairing
  proposal");
- `hcaseone_open`:情形一交换的 reduced 性 —— 分支 1 位置
  (`d s = q'`)处交换以 no-op 逐出 `q'`,非 resident;`hnb'` 需越过
  至多一次的分支 1 缺页(见 DESIGN "Case one");
- `hB2dead_open`:B2 死页步骤的构造(步骤引理尚不存在,keep-swap
  与链已证,见 DESIGN "Remaining" item (3))。 -/

/-- B1 步骤的 slack 前提:坏事件(`σ[J'''] ∈ D_{J'''}`)发生时
`bad ≤ slack`。q₀'-B1 半边由 `b1_exchange_no_bad_q0` +
`b1_bad_le_slack_q0` 给出(尚需 `1 ≤ slack` 的推导 —— q₀'-B1 是窗口内
第一步,slack 即交换的 `slack + 1`);非 q₀' 半边是开放的配对设计
(见 DESIGN.md "Non-q₀' B1 pairing proposal")。 -/
def B1SlackHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
    agreeWithFIF st.d C₀ σ t₂ →
    schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
    st.d t₂ ∉ schedCache st.d C₀ σ t₂ →
    σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
    ∀ {j''' : ℕ}, nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''' →
      (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0) ≤ st.slack

/-- hQ 的严格化前提:B2 分歧 `t₂` 处,`Q` 中活对的首次请求严格在
`t₂` 之后(`b2_ehit_ne`/`b2_hnotE`/`past_pair_first_request_after`
所需;全历史 Q 上该字段经验性不成立,见 DESIGN "hQ-extension
blocker")。 -/
def HQsupplyHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ),
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'') ∧
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'')

/-- 情形一交换的 reduced 性前提:存在 reduced 界 `hnb'`(在 `t+1` 之后,
越过至多一次的分支 1 缺页)使交换在 `hnb'` 起的缺页处逐出 resident
页。`iterate_main_case_one` 给出 OR 形式 `e s ∈ E_s ∨ d s = q'`
(见 DESIGN "Case one")。 -/
def CaseOneHdredHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t : ℕ) (ht : t < σ.length),
    st.hnb ≤ t →
    agreeWithFIF st.d C₀ σ t →
    schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) →
    nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none →
    ∃ hnb' : ℕ, t + 1 ≤ hnb' ∧
      ∀ s, hnb' ≤ s →
        σ.getD s 0 ∉ schedCache (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s →
        (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) s ∈
          schedCache (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s

/-- B2 死页步骤的构造前提:q-dead 与 q''-dead 的 B2 步骤引理尚不存在
(keep-swap 与链已证:见 DESIGN "Remaining" item (3))。 -/
def B2DeadStepHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
    agreeWithFIF st.d C₀ σ t₂ →
    schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
    st.d t₂ ∈ schedCache st.d C₀ σ t₂ →
    σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
    t₂ ∉ st.P →
    nextUse σ (t₂ + 1) (st.d t₂) = none ∨ nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = none →
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1

/-- B2 步的 hQ 供应(部分 1):旧界 `t₂` 的 strengthened clause 由
`past_pair_first_request_after` 从状态旧 `hQ`(旧界 `st.t0`)给出 —— 这是
hQ-extension blocker 的消费者所需形式("consumers only consult the pair
whose page equals the request, and that pair is never broken" 的形式化;
`past_pair` 的 B2-resident 前提 `hqin` 与状态字段 `hP`/`hcomp`/`hpair`/
`hP_in`/`hQfifo`/`hpast` 均由状态给出)。 -/
lemma b2_hQ_supply_old (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₀t₂ : st.t0 ≤ t₂)
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hqin : st.d t₂ ∈ schedCache st.d C₀ σ t₂) :
    ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'' := by
  exact past_pair_first_request_after σ C₀ hC₀ st.d st.t0 t₂ ht₀t₂ hagree st.Q st.P
    st.hpast st.hP st.hcomp st.hpair st.hQfifo st.hP_in st.hQ ht₂ hqin

/- ### 情形一步的构造(hAone 的实例化)

`iterate_main_case_one` 给出一致、slack 与 OR 形式 reduced 性;
`hcaseone_open` 提供状态字段 `hdred` 的界。Q/P 保持 ∅(无过往对),
窗口 `win = none`(q' 死,无窗口)。 -/

/-- 情形一的完整状态构造:一次 exchange 后,`d' = e`,`t0 = t+1`,
slack 由 `iterate_main_exchange` 的 hnone 枝(q 活 +1,q 死不变),
`hdred` 由 `hcaseone_open` 的界。Q/P 保持 ∅,`win = none`。 -/
lemma step_case_one (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hcaseone : CaseOneHdredHyp σ C₀ M)
    {t : ℕ} (ht : t < σ.length)
    (hnb_le : st.hnb ≤ t)
    (hagree : agreeWithFIF st.d C₀ σ t)
    (hdis : schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnone : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none) :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t + 1 := by
  let q : Page := st.d t
  let q' : Page := fifoSchedule σ C₀ t
  let e : ℕ → Page := exchangeSchedule st.d t q q' σ C₀
  have hdred_t : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache st.d C₀ σ s → st.d s ∈ schedCache st.d C₀ σ s := by
    intro s hs hf
    exact st.hdred s (by omega) hf
  rcases iterate_main_case_one st.d σ C₀ hC₀ ht hagree hdis hdred_t hnone st.slack with
    ⟨slack', hagreeE, hbookE, hredE⟩
  rcases hcaseone st t ht hnb_le hagree hdis hnone with ⟨hnb', hnb'_t, hred'⟩
  have hbook' : schedMisses e C₀ σ + slack' ≤ M := by
    exact le_trans hbookE st.hbook
  have hwin_inv' : ∀ (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ),
      none = some (d_pre, t₀, q₀, q₀', j₀, j₀') →
      t₀ < t + 1 ∧ d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
      (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
      σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
      nextUse σ (t₀ + 1) q₀ = some j₀ ∧
      (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
      nextUse σ (t₀ + 1) q₀' = some j₀' := by
    intro d_pre t₀ q₀ q₀' j₀ j₀' hEq
    cases hEq
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange none e σ C₀) C₀ σ s \
      schedCache e C₀ σ s ⊆ (∅ : Finset (ℕ × Page)).image Prod.snd := by
    intro s hs
    simp [windowExchange]
  have hd_eq' : ∀ s, s ∉ (∅ : Finset ℕ) → e s = windowExchange none e σ C₀ s := by
    intro s hs
    rfl
  have hpast' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) → tᵢ < t + 1 := by
    intro tᵢ q'' h
    simp at h
  have hQ' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
      nextUse σ (tᵢ + 1) q'' = none ∨ ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t + 1 < tᵢ + 1 + j'' := by
    intro tᵢ q'' h
    simp at h
  have hQfifo' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
      q'' = fifoSchedule σ C₀ tᵢ := by
    intro tᵢ q'' h
    simp at h
  have hP' : ∀ s, s ∈ (∅ : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') := by
    intro s h
    simp at h
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ (∅ : Finset ℕ) := by
    intro s h
    rcases h with ⟨tᵢ, q'', htq, hteq⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq⟩
    · simp at htq
    · simp at htq
  have hcomp' : ∀ s, s ∈ (∅ : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ ∧ e s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ e s = q'') := by
    intro s h
    simp at h
  have hpair' : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache e C₀ σ tᵢ ∧ q'' ∈ schedCache e C₀ σ tᵢ ∧ e tᵢ = q'' := by
    intro tᵢ q'' j'' h
    simp at h
  refine ⟨⟨e, t + 1, slack', hnb', ∅, ∅, none, hwin_inv', hagreeE, hbook', hchain', hd_eq', hred',
    hpast', hQ', hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

/-- B1(活)的完整状态构造:修复 `r` 后 `t0 = t₂+1`,slack 记账
`slack − bad`(`hslack` 前提给出 `bad ≤ slack`),Q/P 扩展
(`extend_h*` 胶水),reduced 界 `max hnb (J'''+1)`。 -/
lemma step_b1_alive (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hslack : B1SlackHyp σ C₀ M)
    (hQ : HQsupplyHyp σ C₀ M)
    (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ)
    (hwin : st.win = some (d_pre, t₀, q₀, q₀', j₀, j₀'))
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb)
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hdis : schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : st.d t₂ ∉ schedCache st.d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂)
    (ht₀t₂ : st.t0 ≤ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''') :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1 := by
  let q'' : Page := fifoSchedule σ C₀ t₂
  let bad : ℕ := if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0
  have hQ_up : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ < tᵢ + 1 + j'' := (hQ st t₂).1
  have hQ_ext : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'' := (hQ st t₂).2
  rcases iterate_main_case_b1_alive d_pre st.d t₀ q₀ q₀' σ C₀ hC₀ ht₂ st.hnb ht₂hnb
    hagree hdis hnoop hftd hj''' st.Q (by
      intro s hs
      simpa [windowExchange, hwin] using st.hchain s hs) st.P (by
      intro s hs
      simpa [windowExchange, hwin] using st.hd_eq s hs) st.hdred with
    ⟨r, hagree', hmiss', hchainL, hd_eqL, hdred', hrt, hrN, hre2, hce⟩
  have hbads : bad ≤ st.slack := by
    dsimp [bad]
    exact hslack st t₂ ht₂ ht₂hnb hagree hdis hnoop hftd hj'''
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
  have hq''res : q'' ∈ schedCache st.d C₀ σ t₂ := by
    have hfd := first_disagree st.d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hre : ∀ s, s < t₂ → r s = st.d s := by
    intro s hs
    exact hre2 s (by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with hEq | hmem
      · exact (ne_of_lt hs) hEq
      · exact (by omega : s ≠ t₂ + 1 + j''') (Finset.mem_singleton.mp hmem))
  have hwin_inv' : ∀ (d_pre' : ℕ → Page) (t₀' : ℕ) (q₀'' q₀''' : Page) (j₀'' j₀''' : ℕ),
      st.win = some (d_pre', t₀', q₀'', q₀''', j₀'', j₀''') →
      t₀' < t₂ + 1 ∧ d_pre' t₀' = q₀'' ∧ q₀'' ≠ q₀''' ∧
      (∀ s, t₀' ≤ s → σ.getD s 0 ∉ schedCache d_pre' C₀ σ s → d_pre' s ∈ schedCache d_pre' C₀ σ s) ∧
      σ.getD t₀' 0 ∉ schedCache d_pre' C₀ σ t₀' ∧ q₀''' ∈ schedCache d_pre' C₀ σ t₀' ∧
      nextUse σ (t₀' + 1) q₀'' = some j₀'' ∧
      (∀ k, t₀' + 1 ≤ k → k < t₀' + 1 + j₀'' → σ.getD k 0 ≠ q₀''') ∧
      nextUse σ (t₀' + 1) q₀''' = some j₀''' := by
    intro d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq
    rcases st.hwin_inv d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨by omega, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange st.win r σ C₀) C₀ σ s \
      schedCache r C₀ σ s ⊆ (insert (t₂, q'') st.Q).image Prod.snd := by
    intro s hs
    simpa [Finset.image_insert, windowExchange, hwin, q''] using hchainL s hs
  have hd_eq' : ∀ s, s ∉ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      r s = windowExchange st.win r σ C₀ s := by
    intro s hs
    simpa [windowExchange, hwin] using hd_eqL s hs
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
    insert (t₂, q'') st.Q, st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ), st.win,
    hwin_inv', hagree', hbook', hchain', hd_eq', hdred', hpast', (by simpa [q''] using hQ_ext),
    hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

/-- B2(活-活)的完整状态构造:修复 `r` 后 `t0 = t₂+1`,slack 不变
(强修复免费),Q/P 扩展(`extend_h*` 胶水),reduced 界
`max hnb (J''+1)`。桥接 `hqinE`/`hnotE`/`hnot` 由调用方提供
(分支分析、`b2_hnotE` + hQ 前提、窗口 off-P;`hnot` 经验上在 136
个窗口失效 —— 见 DESIGN "Remaining" item (2))。 -/
lemma step_b2_alive (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hQ : HQsupplyHyp σ C₀ M)
    (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ)
    (hwin : st.win = some (d_pre, t₀, q₀, q₀', j₀, j₀'))
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb)
    (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hdis : schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : st.d t₂ ∈ schedCache st.d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂)
    (ht₀t₂ : st.t0 ≤ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (st.d t₂) = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j'')
    (hjj'' : j < j'')
    (hqinE : st.d t₂ ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ st.P) :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1 := by
  let q : Page := st.d t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  have hQ_up : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ < tᵢ + 1 + j'' := (hQ st t₂).1
  have hQ_ext : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'' := (hQ st t₂).2
  have hwin_facts : d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
      (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
      σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
      nextUse σ (t₀ + 1) q₀ = some j₀ ∧
      (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
      nextUse σ (t₀ + 1) q₀' = some j₀' := by
    rcases st.hwin_inv d_pre t₀ q₀ q₀' j₀ j₀' hwin with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h2, h3, h4, h5, h6, h7, h8, h9⟩
  have ht₂notP : t₂ ∉ st.P := by
    apply no_nop_at_b2 st.d σ C₀ st.Q st.P (t := t₂)
    · intro tᵢ q''₀ htq
      have h := st.hpast tᵢ q''₀ htq
      omega
    · exact st.hP
    · exact st.hcomp
    · exact st.hpair
    · exact ht₂
    · exact hqin
  rcases iterate_main_case_b2_alive d_pre st.d t₀ q₀ q₀' σ C₀ hC₀ hwin_facts.1 hwin_facts.2.1
    hwin_facts.2.2.1 hwin_facts.2.2.2.1 hwin_facts.2.2.2.2.1
    hwin_facts.2.2.2.2.2.1 hwin_facts.2.2.2.2.2.2.1 hwin_facts.2.2.2.2.2.2.2
    ht₂ ht₂₀ ht₂₁ st.hnb ht₂hnb hagree hdis hqin hftd hj hj'' hjj''
    st.Q (by
      intro s hs
      simpa [windowExchange, hwin] using st.hchain s hs) (by
      intro tᵢ q''₀ htq
      have h := st.hpast tᵢ q''₀ htq
      omega) hQ_up hqinE hnotE st.P ht₂notP hnot (by
      intro s hs
      simpa [windowExchange, hwin] using st.hd_eq s hs) st.hdred with
    ⟨r, hagree', hmiss', hchain', hd_eq', hdred', hrt, hrN, hre2, hce⟩
  have hbook' : schedMisses r C₀ σ + st.slack ≤ M := by
    exact le_trans (Nat.add_le_add_right hmiss' st.slack) st.hbook
  have hpast₂ : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q → tᵢ < t₂ := by
    intro tᵢ q''₀ htq
    have h := st.hpast tᵢ q''₀ htq
    omega
  have hq''res : q'' ∈ schedCache st.d C₀ σ t₂ := by
    have hfd := first_disagree st.d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hre : ∀ s, s < t₂ → r s = st.d s := by
    intro s hs
    exact hre2 s (by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with hEq | hmem
      · exact (ne_of_lt hs) hEq
      · exact (by omega : s ≠ t₂ + 1 + j'') (Finset.mem_singleton.mp hmem))
  have hwin_inv' : ∀ (d_pre' : ℕ → Page) (t₀' : ℕ) (q₀'' q₀''' : Page) (j₀'' j₀''' : ℕ),
      st.win = some (d_pre', t₀', q₀'', q₀''', j₀'', j₀''') →
      t₀' < t₂ + 1 ∧ d_pre' t₀' = q₀'' ∧ q₀'' ≠ q₀''' ∧
      (∀ s, t₀' ≤ s → σ.getD s 0 ∉ schedCache d_pre' C₀ σ s → d_pre' s ∈ schedCache d_pre' C₀ σ s) ∧
      σ.getD t₀' 0 ∉ schedCache d_pre' C₀ σ t₀' ∧ q₀''' ∈ schedCache d_pre' C₀ σ t₀' ∧
      nextUse σ (t₀' + 1) q₀'' = some j₀'' ∧
      (∀ k, t₀' + 1 ≤ k → k < t₀' + 1 + j₀'' → σ.getD k 0 ≠ q₀''') ∧
      nextUse σ (t₀' + 1) q₀''' = some j₀''' := by
    intro d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq
    rcases st.hwin_inv d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨by omega, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange st.win r σ C₀) C₀ σ s \
      schedCache r C₀ σ s ⊆ (insert (t₂, q'') st.Q).image Prod.snd := by
    intro s hs
    simpa [Finset.image_insert, windowExchange, hwin, q''] using hchain' s hs
  have hd_eq' : ∀ s, s ∉ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      r s = windowExchange st.win r σ C₀ s := by
    intro s hs
    simpa [windowExchange, hwin] using hd_eq' s hs
  have hpast' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q → tᵢ < t₂ + 1 :=
    extend_hpast st.Q hpast₂
  have hQfifo' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      q''₀ = fifoSchedule σ C₀ tᵢ := by
    simpa [q''] using extend_hQfifo σ C₀ st.Q (rfl : q'' = fifoSchedule σ C₀ t₂) st.hQfifo
  have hP' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
    simpa [q''] using extend_hP σ st.Q st.P hj'' st.hP
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) →
      s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) := by
    simpa [q''] using extend_hP_in σ st.Q st.P hj'' hpast₂ st.hP_in
  have hcomp' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
    simpa [q''] using extend_hcomp' σ st.Q st.P r st.d hj'' hrt hrN hre2 st.hcomp
  have hpair' : ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache r C₀ σ tᵢ ∧ q''₀ ∈ schedCache r C₀ σ tᵢ ∧ r tᵢ = q''₀ := by
    simpa [q''] using extend_hpair σ C₀ st.Q r st.d hftd hq''res hrt hre hce hpast₂ st.hpair
  refine ⟨⟨r, t₂ + 1, st.slack, max st.hnb (t₂ + 1 + j'' + 1),
    insert (t₂, q'') st.Q, st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ), st.win,
    hwin_inv', hagree', hbook', hchain', hd_eq', hdred', hpast', (by simpa [q''] using hQ_ext),
    hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

end Caching

end CLRS
