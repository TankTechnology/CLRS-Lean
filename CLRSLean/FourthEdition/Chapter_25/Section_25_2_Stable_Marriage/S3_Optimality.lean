import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S1_Preference_Model
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S2_Gale_Shapley

/-!
# S3. Optimality of the Gale–Shapley output

The stable-marriage theorems of CLRS §25.2: the Gale–Shapley output is a
stable pairing, every preference profile admits a stable pairing, the output
is a perfect pairing when the two sides have equal size, and the output is
man-optimal and woman-pessimal.

Main results:

- `gs_stable`: the Gale–Shapley output is stable (CLRS Theorem 25.5)
- `stable_matching_exists`: every preference profile has a stable pairing
- `gs_perfect`: with equal numbers of men and women, the Gale–Shapley output
  is a perfect pairing
- `gs_man_optimal`: every man is matched to his best valid partner (CLRS
  Theorem 25.6)
- `gs_man_optimal_perfect`: with equal numbers, every man is matched to his
  best valid partner
- `gs_woman_pessimal`: every woman is matched to her worst valid partner
- `unmatched_man_proposes_to_all`: at the final state an unmatched man has
  proposed to every woman

The man-optimality proof is time-indexed: `runAt n` is the state after `n`
steps, `proposesAt n m w` detects that `m` proposes to `w` at step `n+1`
(`w` leaves his unproposed set), and `rejectedAt n m w` detects that `w`
rejects `m` at step `n+1`.  `no_rejection_of_valid` shows that no man is ever
rejected by a valid partner: a rejection at step `n+1` forces an earlier
rejection of a valid partner (`rejected_valid_earlier`), contradicting
minimality of the first such rejection.  The proposal loop is placed on the
timeline by `gsLoop_eq_gsLoopN`, which identifies the final state with the
indexed run at its pending count.
-/

namespace CLRS

namespace StableMarriage

open Finset Classical Matchings

variable {M : Type*} [Fintype M] [DecidableEq M]
variable {W : Type*} [Fintype W] [DecidableEq W]
variable (P : PreferenceProfile M W)

/-- At the final state of the proposal loop, an unmatched man has proposed to
every woman. -/
lemma unmatched_man_proposes_to_all (P : PreferenceProfile M W) {m : M}
    (hm : (gsLoop (init : GSState P)).mPartner m = none) :
    (gsLoop (init : GSState P)).proposed m = Finset.univ := by
  by_contra hnot
  exact gsLoop_no_pending (init : GSState P) ⟨m, hm, hnot⟩

/-- **Stability of the Gale–Shapley output** (CLRS Theorem 25.5): the
pairing produced by the proposal algorithm is stable. -/
theorem gs_stable (P : PreferenceProfile M W) : Pairing.Stable P (gs P) := by
  let σ : GSState P := gsLoop (init : GSState P)
  have hσ : Invariant σ := by
    unfold σ
    exact gsLoop_invariant (init : GSState P) init_invariant
  have hhalt : ¬ hasPending σ := by
    unfold σ
    exact gsLoop_no_pending (init : GSState P)
  intro m w hblock
  rcases hblock with ⟨hwside, hmside⟩
  have hwprop : w ∈ σ.proposed m := by
    by_cases hmfree : σ.mPartner m = none
    · have hpropall : σ.proposed m = Finset.univ := by
        by_contra hnot
        exact hhalt ⟨m, hmfree, hnot⟩
      rw [hpropall]
      exact Finset.mem_univ w
    · rcases hmside with hmun | ⟨w₀, hw₀, hpref⟩
      · exfalso
        exact hmfree (by simpa [σ, gs, GSState.toPairing] using hmun)
      · have hw₀prop : w₀ ∈ σ.proposed m :=
          hσ.partner_proposed (by simpa [σ, gs, GSState.toPairing] using hw₀)
        exact hσ.downward_closed hw₀prop hpref
  have hwmatched : σ.wPartner w ≠ none := hσ.w_proposed_matched hwprop
  rcases hwside with hwun | ⟨m₀, hwm₀, hpref_w⟩
  · exact False.elim (hwmatched (by simpa [σ, gs, GSState.toPairing] using hwun))
  · have hbest : P.wRank w m₀ ≤ P.wRank w m :=
      hσ.best_among_proposers (by simpa [σ, gs, GSState.toPairing] using hwm₀) hwprop
    exact (lt_irrefl (P.wRank w m₀)) (lt_of_le_of_lt hbest hpref_w)

/-- **Existence of stable matchings** (CLRS §25.2): every preference profile
admits a stable pairing — the Gale–Shapley output is one. -/
theorem stable_matching_exists (P : PreferenceProfile M W) :
    ∃ μ : Pairing M W, Pairing.Stable P μ :=
  ⟨gs P, gs_stable P⟩

/-- A non-`none` option is `some` its value. -/
lemma ne_none_iff_exists {α : Type*} {a : Option α} (h : a ≠ none) :
    ∃ x, a = some x := by
  cases a with
  | none => exact False.elim (h (by rfl))
  | some x => exact ⟨x, rfl⟩

/-- The matched women and the matched men of a consistent pairing have the
same cardinality: the partner map `w ↦ wPartner w` is a bijection between
them. -/
lemma matched_card_eq {σ : GSState P} (hM : Nonempty M) :
    (Finset.univ.filter fun w : W => σ.wPartner w ≠ none).card =
      (Finset.univ.filter fun m : M => σ.mPartner m ≠ none).card := by
  let f : W → M := fun w =>
    if hw : σ.wPartner w ≠ none then
      Classical.choose (ne_none_iff_exists hw)
    else Classical.choice hM
  refine Finset.card_bij (fun w hw => f w) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have hf : f a = Classical.choose (ne_none_iff_exists ha) := by simp [f, ha]
    rw [hf]
    have hs : σ.wPartner a = some (Classical.choose (ne_none_iff_exists ha)) :=
      Classical.choose_spec (ne_none_iff_exists ha)
    intro hnot
    have hm := (σ.h_consistency (Classical.choose (ne_none_iff_exists ha)) a).mpr hs
    simp [hnot] at hm
  · intro a ha b hb hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hfa : f a = Classical.choose (ne_none_iff_exists ha) := by simp [f, ha]
    have hfb : f b = Classical.choose (ne_none_iff_exists hb) := by simp [f, hb]
    rw [hfa, hfb] at hf
    have hsa : σ.wPartner a = some (Classical.choose (ne_none_iff_exists ha)) :=
      Classical.choose_spec (ne_none_iff_exists ha)
    have hsb : σ.wPartner b = some (Classical.choose (ne_none_iff_exists hb)) :=
      Classical.choose_spec (ne_none_iff_exists hb)
    have hma : σ.mPartner (Classical.choose (ne_none_iff_exists ha)) = some a :=
      (σ.h_consistency (Classical.choose (ne_none_iff_exists ha)) a).mpr hsa
    have hmb : σ.mPartner (Classical.choose (ne_none_iff_exists hb)) = some b :=
      (σ.h_consistency (Classical.choose (ne_none_iff_exists hb)) b).mpr hsb
    have : some a = some b := by
      rw [← hma]
      rw [hf]
      rw [hmb]
    exact Option.some.inj this
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases ne_none_iff_exists hb with ⟨w, hw⟩
    have hwm : σ.wPartner w = some b := (σ.h_consistency b w).mp hw
    have hw' : σ.wPartner w ≠ none := by
      rw [hwm]
      simp
    refine ⟨w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hnot
      have hmw := (σ.h_consistency b w).mp hw
      simp [hnot] at hmw
    · have hf : f w = Classical.choose (ne_none_iff_exists hw') := by simp [f, hw']
      rw [hf]
      have hs : σ.wPartner w = some (Classical.choose (ne_none_iff_exists hw')) :=
        Classical.choose_spec (ne_none_iff_exists hw')
      have hs' : some b = some (Classical.choose (ne_none_iff_exists hw')) := by
        simpa [hwm] using hs
      have hEq : Classical.choose (ne_none_iff_exists hw') = b := by
        exact Option.some.inj hs'.symm
      exact hEq

/-- The matched set of a side is everything when its cardinality forces it. -/
lemma filter_eq_univ_of_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (h : (Finset.univ.filter p).card = Fintype.card α) :
    ∀ a : α, p a := by
  intro a
  by_contra hnot
  have hlt : (Finset.univ.filter p).card < Fintype.card α := by
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
        intro heq
        have hmem : a ∈ Finset.univ.filter p := by
          rw [heq]
          exact Finset.mem_univ a
        exact hnot (Finset.mem_filter.mp hmem).2⟩)
  omega

/-- **Perfectness of the Gale–Shapley output** (CLRS §25.2): with equally many
men and women, the algorithm terminates with a perfect pairing. -/
theorem gs_perfect (P : PreferenceProfile M W) (hcard : Fintype.card M = Fintype.card W) :
    (gs P).IsPerfect := by
  by_cases hM : Nonempty M
  · let σ : GSState P := gsLoop (init : GSState P)
    have hσ : Invariant σ := by
      unfold σ
      exact gsLoop_invariant (init : GSState P) init_invariant
    have hhalt : ¬ hasPending σ := by
      unfold σ
      exact gsLoop_no_pending (init : GSState P)
    have hbij : (Finset.univ.filter fun w : W => σ.wPartner w ≠ none).card =
        (Finset.univ.filter fun m : M => σ.mPartner m ≠ none).card :=
      matched_card_eq P hM
    have hmmatched : ∀ m : M, ∃ w : W, σ.mPartner m = some w := by
      intro m
      by_contra hnot
      have hmfree : σ.mPartner m = none := by
        by_contra hnotnone
        exact hnot (ne_none_iff_exists hnotnone)
      have hpropall : σ.proposed m = Finset.univ := by
        by_contra h
        exact hhalt ⟨m, hmfree, h⟩
      have hwmatched : ∀ w : W, σ.wPartner w ≠ none := by
        intro w
        have hwprop : w ∈ σ.proposed m := by
          rw [hpropall]
          exact Finset.mem_univ w
        exact hσ.w_proposed_matched hwprop
      have hcardW : (Finset.univ.filter fun w : W => σ.wPartner w ≠ none).card =
          Fintype.card W := by
        rw [show (Finset.univ.filter fun w : W => σ.wPartner w ≠ none) = Finset.univ by
          apply Finset.eq_univ_iff_forall.mpr
          intro w
          simp [hwmatched w]]
        simp
      have hcardM : (Finset.univ.filter fun m : M => σ.mPartner m ≠ none).card =
          Fintype.card M := by
        rw [← hbij, hcardW, hcard]
      have hall : ∀ m' : M, σ.mPartner m' ≠ none :=
        filter_eq_univ_of_card_eq (fun m : M => σ.mPartner m ≠ none) hcardM
      exact hnot (ne_none_iff_exists (hall m))
    have hwmatched : ∀ w : W, ∃ m : M, σ.wPartner w = some m := by
      intro w
      have hcardM : (Finset.univ.filter fun m : M => σ.mPartner m ≠ none).card =
          Fintype.card M := by
        rw [show (Finset.univ.filter fun m : M => σ.mPartner m ≠ none) = Finset.univ by
          apply Finset.eq_univ_iff_forall.mpr
          intro m
          rcases hmmatched m with ⟨w, hw⟩
          simp [hw]]
        simp
      have hcardW : (Finset.univ.filter fun w : W => σ.wPartner w ≠ none).card =
          Fintype.card W := by
        rw [hbij, hcardM, hcard]
      have hall : ∀ w' : W, σ.wPartner w' ≠ none :=
        filter_eq_univ_of_card_eq (fun w : W => σ.wPartner w ≠ none) hcardW
      exact ne_none_iff_exists (hall w)
    constructor
    · intro m
      exact hmmatched m
    · intro w
      exact hwmatched w
  · constructor
    · intro m
      exfalso
      exact hM ⟨m⟩
    · intro w
      exfalso
      have hW : ¬ Nonempty W := by
        intro hW
        have hcardW : Fintype.card W = 0 := by
          rw [← hcard]
          letI : IsEmpty M := not_nonempty_iff.mp hM
          exact Fintype.card_eq_zero (α := M)
        have hpos : 0 < Fintype.card W := (Fintype.card_pos_iff).mpr hW
        omega
      exact hW ⟨w⟩

/-- A woman `w` is a **valid partner** of man `m` when some stable pairing
matches `m` with `w` (CLRS §25.2). -/
def validPartner (P : PreferenceProfile M W) (m : M) (w : W) : Prop :=
  ∃ μ : Pairing M W, Pairing.Stable P μ ∧ μ.mPartner m = some w

/-- The state of the proposal loop after exactly `n` steps from the initial
state. -/
noncomputable def runAt (P : PreferenceProfile M W) (n : ℕ) : GSState P :=
  gsLoopN n (init : GSState P)

/-- Running the loop `n+1` times from `σ` is stepping the `n`-step run. -/
lemma gsLoopN_step_comm (σ : GSState P) (n : ℕ) :
    gsLoopN (n+1) σ = step (gsLoopN n σ) := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
      calc
        gsLoopN (n+2) σ = gsLoopN (n+1) (step σ) := rfl
        _ = step (gsLoopN n (step σ)) := ih (step σ)
        _ = step (gsLoopN (n+1) σ) := by rfl

/-- One more step of the indexed run steps the current state. -/
lemma runAt_succ (n : ℕ) : runAt P (n+1) = step (runAt P n) := by
  unfold runAt
  exact gsLoopN_step_comm P (init : GSState P) n

/-- From a state with pending proposals, the pending count is positive. -/
lemma pendingCount_pos_of_hasPending (σ : GSState P) (h : hasPending σ) :
    1 ≤ pendingCount σ := by
  classical
  rcases h with ⟨m, hmfree, hpropne⟩
  unfold pendingCount
  have hlt : (σ.proposed m).card < Fintype.card W := by
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hpropne⟩)
  have hterm : 1 ≤ Fintype.card W - (σ.proposed m).card := by omega
  have hsum : Fintype.card W - (σ.proposed m).card ≤
      ∑ m : M, (Fintype.card W - (σ.proposed m).card) := by
    exact Finset.single_le_sum
      (fun m' hm' => Nat.zero_le (Fintype.card W - (σ.proposed m').card))
      (Finset.mem_univ m)
  omega

/-- The proposal loop is the indexed run at its pending count: after
`pendingCount σ` steps the loop has halted. -/
lemma gsLoopN_eq_gsLoop_of_ge (σ : GSState P) (k : ℕ) (hk : pendingCount σ ≤ k) :
    gsLoopN k σ = gsLoop σ := by
  rw [gsLoop]
  by_cases h : hasPending σ
  · rw [dif_pos h]
    have hk1 : 1 ≤ k := le_trans (pendingCount_pos_of_hasPending P σ h) hk
    have hlt : pendingCount (step σ) < pendingCount σ := pendingCount_step_lt σ h
    have hk' : k = (k - 1) + 1 := by omega
    calc
      gsLoopN k σ = gsLoopN ((k - 1) + 1) σ := by rw [← hk']
      _ = gsLoopN (k - 1) (step σ) := rfl
      _ = gsLoop (step σ) := by
        exact gsLoopN_eq_gsLoop_of_ge (step σ) (k - 1) (by omega)
  · rw [dif_neg h]
    exact gsLoopN_eq_self_of_no_pending h k
termination_by pendingCount σ
decreasing_by
  exact pendingCount_step_lt σ h

/-- The Gale–Shapley loop from `σ` equals the indexed run of length
`pendingCount σ`. -/
lemma gsLoop_eq_gsLoopN (σ : GSState P) : gsLoop σ = gsLoopN (pendingCount σ) σ := by
  exact (gsLoopN_eq_gsLoop_of_ge P σ (pendingCount σ) le_rfl).symm

/-- Man `m` proposes to woman `w` at step `n+1`: `w` leaves the unproposed set
between the `n`-th and `(n+1)`-st states. -/
def proposesAt (n : ℕ) (m : M) (w : W) : Prop :=
  w ∉ (runAt P n).proposed m ∧ w ∈ (runAt P (n+1)).proposed m

/-- Man `m` is rejected by woman `w` at step `n+1`: `w` either drops `m`
between the two states, or rejects his proposal. -/
def rejectedAt (n : ℕ) (m : M) (w : W) : Prop :=
  ((runAt P n).mPartner m = some w ∧ (runAt P (n+1)).mPartner m ≠ some w) ∨
    (proposesAt P n m w ∧ ¬ accepts (runAt P n) m w)

/-- A proposal at step `n+1` is exactly the proposal step of `m` to his next
woman. -/
lemma proposesAt_extract (n : ℕ) (m : M) (w : W) (hp : proposesAt P n m w) :
    ∃ hfree : (runAt P n).mPartner m = none,
      ∃ hpend : (runAt P n).proposed m ≠ Finset.univ,
        w = nextWoman (runAt P n) m hpend ∧ runAt P (n+1) = proposalStep (runAt P n) m hfree hpend := by
  classical
  unfold proposesAt at hp
  rw [runAt_succ P n] at hp ⊢
  by_cases h : hasPending (runAt P n)
  · let c := Classical.choose h
    have hspec := Classical.choose_spec h
    have hstep : step (runAt P n) = proposalStep (runAt P n) c hspec.1 hspec.2 := by
      simp [step, h, c]
    have hmem : w ∈ (step (runAt P n)).proposed m := hp.2
    have hmc : m = c := by
      by_contra hmc
      have h' : (proposalStep (runAt P n) c hspec.1 hspec.2).proposed m =
          (runAt P n).proposed m := by
        exact proposalStep_proposed_other hspec.1 hspec.2 hmc
      exact hp.1 (by simpa [hstep, h'] using hmem)
    subst m
    have hmem' : w ∈ insert (nextWoman (runAt P n) c hspec.2) ((runAt P n).proposed c) := by
      rw [← proposalStep_proposed_self hspec.1 hspec.2]
      rw [← hstep]
      exact hmem
    have hw : w = nextWoman (runAt P n) c hspec.2 := by
      rcases Finset.mem_insert.mp hmem' with hw | hmem''
      · exact hw
      · exact False.elim (hp.1 (by simpa using hmem''))
    refine ⟨hspec.1, hspec.2, hw, ?_⟩
    exact hstep
  · have h' : step (runAt P n) = runAt P n := step_eq_self_of_no_pending h
    rw [h'] at hp
    exact False.elim (hp.1 hp.2)

/-- A man proposing at step `n+1` is free at time `n`. -/
lemma proposesAt_free (n : ℕ) (m : M) (w : W) (hp : proposesAt P n m w) :
    (runAt P n).mPartner m = none := by
  rcases proposesAt_extract P n m w hp with ⟨hfree, hpend, hw, hstep⟩
  exact hfree

/-- The proposer's partner after a proposal step: the target woman when she
accepts, and unmatched otherwise. -/
lemma proposesAt_self (n : ℕ) (m : M) (w : W) (hp : proposesAt P n m w) :
    (runAt P (n+1)).mPartner m = if accepts (runAt P n) m w then some w else none := by
  rcases proposesAt_extract P n m w hp with ⟨hfree, hpend, hw, hstep⟩
  rw [hstep]
  simpa [← hw] using proposalStep_mPartner_self hfree hpend

/-- The target woman's partner after a proposal step: the proposer when she
accepts, and unchanged otherwise. -/
lemma proposesAt_target (n : ℕ) (m : M) (w : W) (hp : proposesAt P n m w) :
    (runAt P (n+1)).wPartner w = if accepts (runAt P n) m w then some m else (runAt P n).wPartner w := by
  rcases proposesAt_extract P n m w hp with ⟨hfree, hpend, hw, hstep⟩
  rw [hstep]
  simpa [← hw] using proposalStep_wPartner_target hfree hpend

/-- If `w` is in a man's proposed set at time `b ≥ 1`, he proposed to her at
some earlier step. -/
lemma proposesAt_exists (b : ℕ) (m : M) (w : W) (hb : 1 ≤ b)
    (h : w ∈ (runAt P b).proposed m) : ∃ n < b, proposesAt P n m w := by
  classical
  have hnonempty : ∃ t : ℕ, w ∈ (runAt P t).proposed m := ⟨b, h⟩
  let t₀ : ℕ := Nat.find hnonempty
  have ht₀ : w ∈ (runAt P t₀).proposed m := Nat.find_spec hnonempty
  have htmin : ∀ t < t₀, w ∉ (runAt P t).proposed m := by
    intro t ht
    exact Nat.find_min hnonempty ht
  have ht₀ge : 1 ≤ t₀ := by
    by_contra ht0
    have ht₀' : t₀ = 0 := by omega
    rw [ht₀'] at ht₀
    have hfalse : False := by
      simp [runAt, gsLoopN, init] at ht₀
    exact hfalse
  have ht₀le : t₀ ≤ b := by
    by_contra htle
    exact htmin b (by omega) h
  refine ⟨t₀ - 1, by omega, ?_⟩
  constructor
  · exact htmin (t₀ - 1) (by omega)
  · have ht₀' : t₀ - 1 + 1 = t₀ := by omega
    rw [ht₀']
    exact ht₀

/-- At a rejection step, the rejecting woman is matched to a man she strictly
prefers to the rejected man. -/
lemma rejectedAt_new_partner (n : ℕ) (m : M) (w : W) (hrej : rejectedAt P n m w) :
    ∃ m₀, (runAt P (n+1)).wPartner w = some m₀ ∧ P.wPrefers w m₀ m := by
  rcases hrej with hB | hA
  · rcases hB with ⟨hwm, hnotm⟩
    by_cases h : hasPending (runAt P n)
    · let c := Classical.choose h
      have hspec := Classical.choose_spec h
      have hstep : step (runAt P n) = proposalStep (runAt P n) c hspec.1 hspec.2 := by
        simp [step, h, c]
      let w₀ : W := nextWoman (runAt P n) c hspec.2
      have hmc : m ≠ c := by
        intro hmc
        have hc : (runAt P n).mPartner m = none := by simpa [hmc] using hspec.1
        exact (by simpa [hc] using hwm)
      have hacc : accepts (runAt P n) c w₀ ∧ (runAt P n).wPartner w₀ = some m := by
        by_contra hnot'
        have hm' : (proposalStep (runAt P n) c hspec.1 hspec.2).mPartner m =
            (runAt P n).mPartner m := by
          exact proposalStep_mPartner_other hspec.1 hspec.2 hmc hnot'
        have hm'w : (runAt P (n+1)).mPartner m = some w := by
          rw [runAt_succ P n, hstep, hm', hwm]
        exact hnotm hm'w
      have hw₀ : w₀ = w := by
        have h1 : (runAt P n).mPartner m = some w₀ :=
          ((runAt P n).h_consistency m w₀).mpr hacc.2
        exact Option.some.inj (by rw [← h1, hwm])
      have hwnew : (runAt P (n+1)).wPartner w = some c := by
        rw [runAt_succ P n, hstep]
        have htarget : (proposalStep (runAt P n) c hspec.1 hspec.2).wPartner
            (nextWoman (runAt P n) c hspec.2) = some c := by
          simpa [w₀, hacc.1] using proposalStep_wPartner_target (σ := runAt P n) (m := c)
            hspec.1 hspec.2
        rw [← hw₀]
        exact htarget
      have hwmn : (runAt P n).wPartner w = some m := ((runAt P n).h_consistency m w).mp hwm
      have hpref : P.wPrefers w c m := by
        rcases hacc.1 with hfree' | hpref'
        · exact False.elim (by simp [← hw₀, hfree'] at hwmn)
        · rcases hpref' with ⟨m₁, hwm₁, hp'⟩
          have hm₁ : m₁ = m := Option.some.inj (by rw [← hwm₁, hw₀, hwmn])
          simpa [hw₀, hm₁] using hp'
      exact ⟨c, hwnew, hpref⟩
    · have hstep : step (runAt P n) = runAt P n := step_eq_self_of_no_pending h
      have hm' : (runAt P (n+1)).mPartner m = (runAt P n).mPartner m := by
        rw [runAt_succ P n, hstep]
      exact False.elim (hnotm (by simpa [hm'] using hwm))
  · rcases hA with ⟨hp, hnotacc⟩
    rcases proposesAt_extract P n m w hp with ⟨hfree, hpend, hw, hstep⟩
    have hwne : (runAt P n).wPartner w ≠ none := by
      intro hnone
      exact hnotacc (Or.inl hnone)
    rcases ne_none_iff_exists hwne with ⟨m₀, hwm₀⟩
    refine ⟨m₀, ?_, ?_⟩
    · rw [hstep, hw]
      have hnotacc' : ¬ accepts (runAt P n) m (nextWoman (runAt P n) m hpend) := by
        simpa [hw] using hnotacc
      have htarget : (proposalStep (runAt P n) m hfree hpend).wPartner
          (nextWoman (runAt P n) m hpend) =
          (runAt P n).wPartner (nextWoman (runAt P n) m hpend) := by
        rw [proposalStep_wPartner_target hfree hpend]
        rw [if_neg hnotacc']
      rw [htarget, hw.symm]
      exact hwm₀
    · have hnotpref : ¬ P.wPrefers w m m₀ := by
        intro hp'
        exact hnotacc (Or.inr ⟨m₀, hwm₀, hp'⟩)
      have hm₀ne : m₀ ≠ m := by
        intro hm₀
        have h : (runAt P n).mPartner m = some w := ((runAt P n).h_consistency m w).mpr
          (by simpa [hm₀] using hwm₀)
        exact False.elim (by simpa [hfree] using h)
      have hle : P.wRank w m₀ ≤ P.wRank w m := le_of_not_gt hnotpref
      have hne : P.wRank w m₀ ≠ P.wRank w m := Function.Injective.ne (P.h_wRank_injective w) hm₀ne
      exact lt_of_le_of_ne hle hne

/-- After a rejection step the new partner `m₀` of the rejecting woman has
already proposed to every woman `w₀` he strictly prefers to her by time `n`:
his proposed set does not gain `w₀` at the rejection step, and he is not
matched to `w₀` at time `n`. -/
lemma rejection_partner_facts (n : ℕ) (m : M) (w : W) (m₀ : M) (w₀ : W)
    (hrej : rejectedAt P n m w) (hwm₀new : (runAt P (n+1)).wPartner w = some m₀)
    (hm₀ne : m₀ ≠ m) (hw₀ne : w₀ ≠ w) (hw₀part : w₀ ∈ (runAt P (n+1)).proposed m₀) :
    w₀ ∈ (runAt P n).proposed m₀ ∧ (runAt P n).mPartner m₀ ≠ some w₀ := by
  rcases hrej with hB | hA
  · rcases hB with ⟨hwm, hnotm⟩
    by_cases h : hasPending (runAt P n)
    · let c := Classical.choose h
      have hspec := Classical.choose_spec h
      have hstep : step (runAt P n) = proposalStep (runAt P n) c hspec.1 hspec.2 := by
        simp [step, h, c]
      let w₀' : W := nextWoman (runAt P n) c hspec.2
      have hmc : m ≠ c := by
        intro hmc
        have hc : (runAt P n).mPartner m = none := by simpa [hmc] using hspec.1
        exact (by simpa [hc] using hwm)
      have hacc : accepts (runAt P n) c w₀' ∧ (runAt P n).wPartner w₀' = some m := by
        by_contra hnot'
        have hm' : (proposalStep (runAt P n) c hspec.1 hspec.2).mPartner m =
            (runAt P n).mPartner m := by
          exact proposalStep_mPartner_other hspec.1 hspec.2 hmc hnot'
        have hm'w : (runAt P (n+1)).mPartner m = some w := by
          rw [runAt_succ P n, hstep, hm', hwm]
        exact hnotm hm'w
      have hw₀' : w₀' = w := by
        have h1 : (runAt P n).mPartner m = some w₀' :=
          ((runAt P n).h_consistency m w₀').mpr hacc.2
        exact Option.some.inj (by rw [← h1, hwm])
      have hm₀c : m₀ = c := by
        have hwnew : (runAt P (n+1)).wPartner w = some c := by
          rw [runAt_succ P n, hstep]
          have htarget : (proposalStep (runAt P n) c hspec.1 hspec.2).wPartner
              (nextWoman (runAt P n) c hspec.2) = some c := by
            simpa [w₀', hacc.1] using proposalStep_wPartner_target (σ := runAt P n) (m := c)
              hspec.1 hspec.2
          rw [← hw₀']
          exact htarget
        exact Option.some.inj (by rw [← hwnew, hwm₀new])
      have hw₀partn : w₀ ∈ (runAt P n).proposed m₀ := by
        have hprop : (runAt P (n+1)).proposed m₀ = insert w ((runAt P n).proposed m₀) := by
          rw [runAt_succ P n, hstep]
          rw [hm₀c]
          rw [proposalStep_proposed_self hspec.1 hspec.2]
          change insert (w₀' : W) ((runAt P n).proposed c) = insert w ((runAt P n).proposed c)
          rw [hw₀']
        rw [hprop] at hw₀part
        rcases Finset.mem_insert.mp hw₀part with hw₀eq | hw₀in
        · exact False.elim (hw₀ne hw₀eq)
        · exact hw₀in
      have hmn₀ : (runAt P n).mPartner m₀ ≠ some w₀ := by
        have hm₀none : (runAt P n).mPartner m₀ = none := by simpa [hm₀c] using hspec.1
        intro h
        exact (by simpa [hm₀none] using h)
      exact ⟨hw₀partn, hmn₀⟩
    · have hstep : step (runAt P n) = runAt P n := step_eq_self_of_no_pending h
      have hm' : (runAt P (n+1)).mPartner m = (runAt P n).mPartner m := by
        rw [runAt_succ P n, hstep]
      exact False.elim (hnotm (by simpa [hm'] using hwm))
  · rcases hA with ⟨hp, hnotacc⟩
    rcases proposesAt_extract P n m w hp with ⟨hfree, hpend, hw, hstep⟩
    have hw₀partn : w₀ ∈ (runAt P n).proposed m₀ := by
      have hprop : (runAt P (n+1)).proposed m₀ = (runAt P n).proposed m₀ := by
        rw [hstep]
        exact proposalStep_proposed_other hfree hpend hm₀ne
      rwa [← hprop]
    have hmn₀ : (runAt P n).mPartner m₀ ≠ some w₀ := by
      have hnot' : ¬ (accepts (runAt P n) m (nextWoman (runAt P n) m hpend) ∧
          (runAt P n).wPartner (nextWoman (runAt P n) m hpend) = some m₀) := by
        intro hc
        have hwm' : (runAt P (n+1)).wPartner w = some m := by
          rw [hstep, hw]
          have htarget : (proposalStep (runAt P n) m hfree hpend).wPartner
              (nextWoman (runAt P n) m hpend) = some m := by
            simpa [hc.1] using proposalStep_wPartner_target (σ := runAt P n) (m := m) hfree hpend
          exact htarget
        exact hm₀ne (Option.some.inj (by rw [← hwm', hwm₀new]))
      have hm' : (runAt P n).mPartner m₀ = some w := by
        have hmm' : (proposalStep (runAt P n) m hfree hpend).mPartner m₀ =
            (runAt P n).mPartner m₀ :=
          proposalStep_mPartner_other hfree hpend hm₀ne hnot'
        have hcons : (proposalStep (runAt P n) m hfree hpend).mPartner m₀ = some w :=
          ((proposalStep (runAt P n) m hfree hpend).h_consistency m₀ w).mpr
            (by simpa [hstep] using hwm₀new)
        rw [← hmm', hcons]
      intro h
      have hw₀eq : w = w₀ := Option.some.inj (by rw [← h, hm'])
      exact hw₀ne hw₀eq.symm
    exact ⟨hw₀partn, hmn₀⟩

/-- A rejection of a valid partner implies an earlier rejection of a valid
partner: from a rejection at step `n+1` one can construct a rejection at an
earlier step. -/
lemma rejected_valid_earlier (n : ℕ) (m : M) (w : W) (hrej : rejectedAt P n m w)
    (hval : validPartner P m w) : ∃ n' < n, ∃ m' w', rejectedAt P n' m' w' ∧ validPartner P m' w' := by
  rcases hval with ⟨μ, hstable, hμm⟩
  rcases rejectedAt_new_partner P n m w hrej with ⟨m₀, hwm₀new, hpref₀⟩
  have hm₀ne : m₀ ≠ m := by
    intro hm₀
    have h : P.wRank w m < P.wRank w m := by
      rw [hm₀] at hpref₀
      exact hpref₀
    exact (lt_irrefl (P.wRank w m)) h
  have hμm₀ne : μ.mPartner m₀ ≠ none := by
    intro hm₀none
    have hblock : Pairing.BlockingPair P μ m₀ w := by
      constructor
      · exact Or.inr ⟨m, (μ.h_consistency m w).mp hμm, hpref₀⟩
      · exact Or.inl hm₀none
    exact hstable m₀ w hblock
  rcases ne_none_iff_exists hμm₀ne with ⟨w₀, hμm₀⟩
  have hw₀ne : w₀ ≠ w := by
    intro hw₀
    have h1 : μ.wPartner w = some m₀ := (μ.h_consistency m₀ w).mp (by simpa [hw₀] using hμm₀)
    have h2 : μ.wPartner w = some m := (μ.h_consistency m w).mp hμm
    exact hm₀ne (Option.some.inj (by rw [← h1, h2]))
  have hpref₀' : P.mPrefers m₀ w₀ w := by
    have hnotm : ¬ (μ.mPartner m₀ = none ∨ ∃ w₁, μ.mPartner m₀ = some w₁ ∧ P.mPrefers m₀ w w₁) := by
      intro hm
      exact hstable m₀ w ⟨Or.inr ⟨m, (μ.h_consistency m w).mp hμm, hpref₀⟩, hm⟩
    have hnotpref : ¬ P.mPrefers m₀ w w₀ := by
      intro hp
      exact hnotm (Or.inr ⟨w₀, hμm₀, hp⟩)
    have hle : P.mRank m₀ w₀ ≤ P.mRank m₀ w := le_of_not_gt hnotpref
    have hne : P.mRank m₀ w₀ ≠ P.mRank m₀ w := Function.Injective.ne (P.h_mRank_injective m₀) hw₀ne
    exact lt_of_le_of_ne hle hne
  have hσ₁ : Invariant (runAt P (n+1)) := by
    unfold runAt
    exact gsLoopN_invariant (init : GSState P) init_invariant (n+1)
  have hwm₀part : w ∈ (runAt P (n+1)).proposed m₀ := by
    have hm₀w : (runAt P (n+1)).mPartner m₀ = some w :=
      ((runAt P (n+1)).h_consistency m₀ w).mpr hwm₀new
    exact hσ₁.partner_proposed hm₀w
  have hw₀part : w₀ ∈ (runAt P (n+1)).proposed m₀ := hσ₁.downward_closed hwm₀part hpref₀'
  have hpair : w₀ ∈ (runAt P n).proposed m₀ ∧ (runAt P n).mPartner m₀ ≠ some w₀ :=
    rejection_partner_facts P n m w m₀ w₀ hrej hwm₀new hm₀ne hw₀ne hw₀part
  rcases hpair with ⟨hw₀partn, hmn₀⟩
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn' : n = 0 := by omega
    rw [hn'] at hw₀partn
    simp [runAt, gsLoopN, init] at hw₀partn
  rcases proposesAt_exists P n m₀ w₀ hn1 hw₀partn with ⟨n', hn'lt, hprop'⟩
  by_cases hacc : accepts (runAt P n') m₀ w₀
  · have hself : (runAt P (n'+1)).mPartner m₀ = some w₀ := by
      simpa [hacc] using proposesAt_self P n' m₀ w₀ hprop'
    let p : ℕ → Prop := fun t => n' + 1 < t ∧ (runAt P t).mPartner m₀ ≠ some w₀
    have hwitness : p (n+1) := by
      constructor
      · omega
      · have hcons : (runAt P (n+1)).mPartner m₀ = some w :=
          ((runAt P (n+1)).h_consistency m₀ w).mpr hwm₀new
        intro h
        exact hw₀ne (Option.some.inj (by rw [← h, hcons]))
    have hT : ∃ t, p t := ⟨n+1, hwitness⟩
    let T : ℕ := Nat.find hT
    have hTspec : p T := Nat.find_spec hT
    have hTmin : ∀ t < T, ¬ p t := by
      intro t ht
      exact Nat.find_min hT ht
    have hTle : T ≤ n + 1 := by
      by_contra hlt
      exact hTmin (n+1) (by omega) hwitness
    have hTne : T ≠ n + 1 := by
      intro hT'
      by_cases hn'lt : n' + 1 < n
      · exact hTmin n (by omega) ⟨hn'lt, hmn₀⟩
      · have hn'eq : n' + 1 = n := by omega
        exact hmn₀ (by simpa [hn'eq] using hself)
    have hT1 : T - 1 < n := by omega
    have hrej' : rejectedAt P (T-1) m₀ w₀ := by
      have hm₁ : (runAt P (T-1)).mPartner m₀ = some w₀ := by
        by_cases hT1eq : T - 1 = n' + 1
        · rwa [hT1eq]
        · have hT1gt : n' + 1 < T - 1 := by omega
          have hnotp : ¬ p (T-1) := hTmin (T-1) (by omega)
          by_cases hm' : (runAt P (T-1)).mPartner m₀ = some w₀
          · exact hm'
          · exact False.elim (hnotp ⟨hT1gt, hm'⟩)
      have hT' : (runAt P (T - 1 + 1)).mPartner m₀ ≠ some w₀ := by
        simpa [show T - 1 + 1 = T by omega] using hTspec.2
      exact Or.inl ⟨hm₁, hT'⟩
    exact ⟨T - 1, hT1, m₀, w₀, hrej', ⟨μ, hstable, hμm₀⟩⟩
  · have hrej' : rejectedAt P n' m₀ w₀ := Or.inr ⟨hprop', hacc⟩
    exact ⟨n', hn'lt, m₀, w₀, hrej', ⟨μ, hstable, hμm₀⟩⟩

/-- **No man is ever rejected by a valid partner** during the proposal run:
rejections of valid partners would descend to strictly earlier steps. -/
theorem no_rejection_of_valid : ¬ ∃ n m w, rejectedAt P n m w ∧ validPartner P m w := by
  classical
  intro h
  let p : ℕ → Prop := fun n => ∃ m w, rejectedAt P n m w ∧ validPartner P m w
  have hnonempty : ∃ n, p n := h
  let n₀ : ℕ := Nat.find hnonempty
  have h₀ : p n₀ := Nat.find_spec hnonempty
  have hmin : ∀ n < n₀, ¬ p n := by
    intro n hn
    exact Nat.find_min hnonempty hn
  rcases h₀ with ⟨m, w, hrej, hval⟩
  rcases rejected_valid_earlier P n₀ m w hrej hval with ⟨n', hn'lt, m', w', hrej', hval'⟩
  exact hmin n' hn'lt ⟨m', w', hrej', hval'⟩

/-- A man matched at the end of the run cannot strictly prefer a valid partner
to his final partner. -/
lemma better_valid_contradiction (k : ℕ) (m : M) (w : W) (hm : (runAt P k).mPartner m = some w)
    {w' : W} (hval : validPartner P m w') (hpref : P.mPrefers m w' w) : False := by
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk' : k = 0 := by omega
    rw [hk'] at hm
    simp [runAt, gsLoopN, init] at hm
  have hσ : Invariant (runAt P k) := by
    unfold runAt
    exact gsLoopN_invariant (init : GSState P) init_invariant k
  have hwprop : w ∈ (runAt P k).proposed m := hσ.partner_proposed hm
  have hw'prop : w' ∈ (runAt P k).proposed m := hσ.downward_closed hwprop hpref
  rcases proposesAt_exists P k m w' hk1 hw'prop with ⟨n, hnlt, hp⟩
  by_cases hacc : accepts (runAt P n) m w'
  · have hself : (runAt P (n+1)).mPartner m = some w' := by
      simpa [hacc] using proposesAt_self P n m w' hp
    have hww' : w' ≠ w := by
      intro h
      have h₁ : P.mRank m w < P.mRank m w := by
        rw [h] at hpref
        exact hpref
      exact (lt_irrefl (P.mRank m w)) h₁
    let p : ℕ → Prop := fun t => n + 1 < t ∧ (runAt P t).mPartner m ≠ some w'
    have hwitness : p k := by
      constructor
      · by_contra hnk
        have hkeq : k = n + 1 := by omega
        have hm' : (runAt P (n+1)).mPartner m = some w := by simpa [hkeq] using hm
        exact hww' (Option.some.inj (by rw [← hself, hm']))
      · intro h
        exact hww' (Option.some.inj (by rw [← h, hm]))
    have hT : ∃ t, p t := ⟨k, hwitness⟩
    let T : ℕ := Nat.find hT
    have hTspec : p T := Nat.find_spec hT
    have hTmin : ∀ t < T, ¬ p t := by
      intro t ht
      exact Nat.find_min hT ht
    have hT1 : T - 1 < k := by
      have hTle : T ≤ k := by
        by_contra hlt
        exact hTmin k (by omega) hwitness
      have hTpos : 1 ≤ T := by
        have h : n + 1 < T := hTspec.1
        omega
      omega
    have hrej : rejectedAt P (T-1) m w' := by
      have hm₁ : (runAt P (T-1)).mPartner m = some w' := by
        by_cases hT1eq : T - 1 = n + 1
        · rwa [hT1eq]
        · have hT1gt : n + 1 < T - 1 := by omega
          have hnotp : ¬ p (T-1) := hTmin (T-1) (by omega)
          by_cases hm' : (runAt P (T-1)).mPartner m = some w'
          · exact hm'
          · exact False.elim (hnotp ⟨hT1gt, hm'⟩)
      have hT' : (runAt P (T - 1 + 1)).mPartner m ≠ some w' := by
        simpa [show T - 1 + 1 = T by omega] using hTspec.2
      exact Or.inl ⟨hm₁, hT'⟩
    exact no_rejection_of_valid P ⟨T - 1, m, w', hrej, hval⟩
  · have hrej : rejectedAt P n m w' := Or.inr ⟨hp, hacc⟩
    exact no_rejection_of_valid P ⟨n, m, w', hrej, hval⟩

/-- **Man-optimality of the Gale–Shapley output** (CLRS Theorem 25.6): every
man is matched to his best valid partner — no stable matching pairs him with a
woman he strictly prefers to his Gale–Shapley partner. -/
theorem gs_man_optimal (P : PreferenceProfile M W) :
    ∀ m w, (gs P).mPartner m = some w →
      ∀ w', validPartner P m w' → ¬ P.mPrefers m w' w := by
  intro m w hm w' hval
  by_contra hpref
  have hσeq : gsLoop (init : GSState P) = runAt P (pendingCount (init : GSState P)) := by
    unfold runAt
    exact gsLoop_eq_gsLoopN P (init : GSState P)
  have hm' : (runAt P (pendingCount (init : GSState P))).mPartner m = some w := by
    simp [gs, GSState.toPairing, hσeq] at hm
    exact hm
  exact better_valid_contradiction P (pendingCount (init : GSState P)) m w hm' hval hpref

/-- **Man-optimality with equal cardinality** (CLRS Theorem 25.6): with equally
many men and women, every man is matched to his best valid partner. -/
theorem gs_man_optimal_perfect (P : PreferenceProfile M W)
    (hcard : Fintype.card M = Fintype.card W) :
    ∀ m, ∃ w, (gs P).mPartner m = some w ∧
      ∀ w', validPartner P m w' → ¬ P.mPrefers m w' w := by
  intro m
  rcases (gs_perfect P hcard).1 m with ⟨w, hw⟩
  exact ⟨w, hw, gs_man_optimal P m w hw⟩

/-- **Woman-pessimality of the Gale–Shapley output** (CLRS §25.2): each woman
is matched to her worst valid partner — no stable matching pairs her with a
man she prefers to her Gale–Shapley partner, and her Gale–Shapley partner is
preferred to every other stable partner of hers. -/
theorem gs_woman_pessimal (P : PreferenceProfile M W) :
    ∀ w m₀, (gs P).wPartner w = some m₀ →
      ∀ μ : Pairing M W, Pairing.Stable P μ →
        ∀ m', μ.wPartner w = some m' → ¬ P.wPrefers w m₀ m' := by
  intro w m₀ hwm₀ μ hstable m' hμm'
  by_contra hpref
  have hnot : ¬ Pairing.BlockingPair P μ m₀ w := hstable m₀ w
  have hwside : μ.wPartner w = none ∨ ∃ m₁, μ.wPartner w = some m₁ ∧ P.wPrefers w m₀ m₁ :=
    Or.inr ⟨m', hμm', hpref⟩
  have hnotm : ¬ (μ.mPartner m₀ = none ∨ ∃ w', μ.mPartner m₀ = some w' ∧ P.mPrefers m₀ w w') := by
    intro hm
    exact hnot ⟨hwside, hm⟩
  have hm₀ne : μ.mPartner m₀ ≠ none := by
    intro hn
    exact hnotm (Or.inl hn)
  rcases ne_none_iff_exists hm₀ne with ⟨w₀, hm₀w₀⟩
  have hnotpref : ¬ P.mPrefers m₀ w w₀ := by
    intro hp
    exact hnotm (Or.inr ⟨w₀, hm₀w₀, hp⟩)
  have hw₀ne : w₀ ≠ w := by
    intro h
    have h1 : μ.wPartner w = some m₀ := (μ.h_consistency m₀ w).mp (by simpa [h] using hm₀w₀)
    have hmm' : m₀ = m' := Option.some.inj (by rw [← h1, hμm'])
    have h : P.wRank w m₀ < P.wRank w m₀ := by
      rw [← hmm'] at hpref
      exact hpref
    exact (lt_irrefl (P.wRank w m₀)) h
  have hpref₀ : P.mPrefers m₀ w₀ w := by
    have hle : P.mRank m₀ w₀ ≤ P.mRank m₀ w := le_of_not_gt hnotpref
    have hne : P.mRank m₀ w₀ ≠ P.mRank m₀ w := Function.Injective.ne (P.h_mRank_injective m₀) hw₀ne
    exact lt_of_le_of_ne hle hne
  have hσm₀ : (gs P).mPartner m₀ = some w := ((gs P).h_consistency m₀ w).mpr hwm₀
  have hvalidw₀ : validPartner P m₀ w₀ := ⟨μ, hstable, hm₀w₀⟩
  exact gs_man_optimal P m₀ w hσm₀ w₀ hvalidw₀ hpref₀

end StableMarriage

end CLRS
