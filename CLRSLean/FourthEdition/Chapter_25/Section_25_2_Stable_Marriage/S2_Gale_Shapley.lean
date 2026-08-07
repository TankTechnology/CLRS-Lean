import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S1_Preference_Model

/-!
# S2. The Gale–Shapley proposal algorithm

A functional formulation of the Gale–Shapley algorithm of CLRS §25.2 as a
loop over proposal steps: at each step a free man proposes to the woman he
has not yet proposed to whom he ranks highest, and the woman accepts him
exactly when she is free or prefers him to her current partner (in which case
her current partner is freed).  Each man proposes to each woman at most once,
so the loop terminates within `|M| · |W|` proposals.

Main results:

- `GSState`: the algorithm state (a pairing plus per-man proposed sets)
- `nextWoman`: the most preferred woman a man has not yet proposed to
- `proposalStep` / `step`: the one-step proposal/accept transition
- `Invariant`: the loop invariants (matched women always prefer their current
  partner to any proposer; proposed sets are rank prefixes; a man's partner is
  always proposed to)
- `step_partner_improves`: a woman's partner only improves over time
- `pendingCount` / `gsLoopN` / `gs`: the well-founded loop and its final state
- `ProposedAt` and `proposedAt_before_of_prefers`: proposals proceed in
  decreasing preference order
-/
namespace CLRS

namespace StableMarriage

open Finset Classical Matchings

variable {M : Type*} [Fintype M] [DecidableEq M]
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {P : PreferenceProfile M W}

/--
The state of the Gale–Shapley proposal algorithm (CLRS §25.2): a pairing,
together with the set of women each man has already proposed to.
-/
structure GSState (P : PreferenceProfile M W) where
  /-- The woman each man is currently matched to, if any. -/
  mPartner : M → Option W
  /-- The man each woman is currently matched to, if any. -/
  wPartner : W → Option M
  /-- Mutual consistency of the two partner functions. -/
  h_consistency : ∀ m w, mPartner m = some w ↔ wPartner w = some m
  /-- The set of women each man has already proposed to. -/
  proposed : M → Finset W

/-- A proposal is *pending* when some free man has not yet proposed to every
woman. -/
def hasPending (σ : GSState P) : Prop :=
  ∃ m, σ.mPartner m = none ∧ σ.proposed m ≠ Finset.univ

/-- Woman `w` accepts man `m` when she is free or prefers him to her current
partner. -/
def accepts (σ : GSState P) (m : M) (w : W) : Prop :=
  σ.wPartner w = none ∨ ∃ m₁, σ.wPartner w = some m₁ ∧ P.wPrefers w m m₁

/-- A woman who has never been proposed to is free, and a man who has proposed
to every woman has no next proposal. -/
lemma nextWoman_witness (σ : GSState P) (m : M) (hpend : σ.proposed m ≠ Finset.univ) :
    ∃ w : W, w ∈ Finset.univ \ σ.proposed m ∧
      ∀ w' ∈ Finset.univ \ σ.proposed m, P.mRank m w ≤ P.mRank m w' := by
  classical
  let S : Finset ℕ := (Finset.univ \ σ.proposed m).image (P.mRank m)
  have hSne : S.Nonempty := by
    have hcm : (Finset.univ \ σ.proposed m).Nonempty := by
      by_contra hcm
      have hEq : Finset.univ \ σ.proposed m = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcm
      apply hpend
      ext x
      by_cases hx : x ∈ σ.proposed m
      · simp [hx]
      · exfalso
        have hx' : x ∈ Finset.univ \ σ.proposed m := by simp [hx]
        rw [hEq] at hx'
        simp at hx'
    rcases hcm with ⟨x, hx⟩
    exact ⟨P.mRank m x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let r : ℕ := S.min' hSne
  have hmin : r ∈ S ∧ ∀ b ∈ S, r ≤ b :=
    (Finset.min'_eq_iff (s := S) (H := hSne) r).mp rfl
  rcases Finset.mem_image.mp hmin.1 with ⟨w, hw, hrank⟩
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  have hw'_rank : P.mRank m w' ∈ S := Finset.mem_image.mpr ⟨w', hw', rfl⟩
  have hle : r ≤ P.mRank m w' := hmin.2 (P.mRank m w') hw'_rank
  rw [← hrank] at hle
  exact hle

/-- The woman a man proposes to next: the woman he has not yet proposed to
whom he ranks highest (CLRS §25.2). -/
noncomputable def nextWoman (σ : GSState P) (m : M) (hpend : σ.proposed m ≠ Finset.univ) : W :=
  Classical.choose (nextWoman_witness σ m hpend)

/-- The next woman a man proposes to has not been proposed to yet, so each man
proposes to each woman at most once. -/
lemma nextWoman_not_proposed (σ : GSState P) (m : M) (hpend : σ.proposed m ≠ Finset.univ) :
    nextWoman σ m hpend ∉ σ.proposed m :=
  (Finset.mem_sdiff.mp (Classical.choose_spec (nextWoman_witness σ m hpend)).1).2

/-- Every woman a man has not yet proposed to is ranked at least as high (that
is, at most as preferred) as his next proposal. -/
lemma nextWoman_min_rank (σ : GSState P) (m : M) (hpend : σ.proposed m ≠ Finset.univ)
    {w' : W} (hw' : w' ∈ Finset.univ \ σ.proposed m) :
    P.mRank m (nextWoman σ m hpend) ≤ P.mRank m w' :=
  (Classical.choose_spec (nextWoman_witness σ m hpend)).2 w' hw'

/-- The proposal step of a single free man `m`: he proposes to the woman he
has not yet proposed to whom he ranks highest; she accepts him exactly when
she is free or prefers him to her current partner, in which case her current
partner is freed. -/
noncomputable def proposalStep (σ : GSState P) (m : M) (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) : GSState P :=
  let w := nextWoman σ m hpend
  { mPartner := fun m' =>
      if accepts σ m w ∧ m' = m then some w
      else if accepts σ m w ∧ σ.wPartner w = some m' then none
      else σ.mPartner m'
    wPartner := fun w' =>
      if w' = w then (if accepts σ m w then some m else σ.wPartner w) else σ.wPartner w'
    h_consistency := by
      intro m' w'
      by_cases hacc : accepts σ m w
      · by_cases hmm : m' = m
        · by_cases hww : w' = w
          · simp [hacc, hmm, hww]
          · have hnot : σ.wPartner w' ≠ some m := by
              intro hw
              have hm := (σ.h_consistency m w').mpr hw
              simp [hfree] at hm
            have hwne : w ≠ w' := by
              intro h
              exact hww h.symm
            simp [hacc, hmm, hww, hnot, hwne]
        · by_cases hww : w' = w
          · subst w'
            by_cases hwm : σ.wPartner w = some m'
            · have hmne : m ≠ m' := by
                intro h
                exact hmm h.symm
              constructor
              · intro h
                simpa [hacc, hmm, hwm, hmne] using h
              · intro h
                simpa [hacc, hmm, hwm, hmne] using h
            · have hmw : σ.mPartner m' ≠ some w := by
                intro h
                exact hwm ((σ.h_consistency m' w).mp h)
              have hmne : m ≠ m' := by
                intro h
                exact hmm h.symm
              constructor
              · intro h
                simpa [hacc, hmm, hwm, hmw, hmne] using h
              · intro h
                simpa [hacc, hmm, hwm, hmw, hmne] using h
          · by_cases hwm : σ.wPartner w = some m'
            · have hnotw' : σ.wPartner w' ≠ some m' := by
                intro hw'
                have hm1 : σ.mPartner m' = some w := (σ.h_consistency m' w).mpr hwm
                have hm2 : σ.mPartner m' = some w' := (σ.h_consistency m' w').mpr hw'
                have hww' : w = w' := by
                  rw [hm1] at hm2
                  simpa using hm2
                exact hww hww'.symm
              constructor
              · intro h
                simpa [hacc, hmm, hwm] using h
              · intro h
                simpa [hacc, hmm, hww, hwm, hnotw'] using h
            · simp [hacc, hmm, hww, hwm]
              exact σ.h_consistency m' w'
      · by_cases hmm : m' = m
        · by_cases hww : w' = w
          · have hnot : σ.wPartner w ≠ some m := by
              intro hw
              have hm := (σ.h_consistency m w).mpr hw
              simp [hfree] at hm
            simp [hacc, hmm, hww, hnot, hfree]
          · have hnot : σ.wPartner w' ≠ some m := by
              intro hw
              have hm := (σ.h_consistency m w').mpr hw
              simp [hfree] at hm
            have hwne : w ≠ w' := by
              intro h
              exact hww h.symm
            simp [hacc, hmm, hww, hnot, hwne, hfree]
        · by_cases hww : w' = w
          · subst w'
            simp [hacc, hmm]
            exact σ.h_consistency m' w
          · simp [hacc, hmm, hww]
            exact σ.h_consistency m' w'
    proposed := fun m' => if m' = m then insert w (σ.proposed m') else σ.proposed m' }

/-- In a proposal step, the proposing man's proposed set gains exactly the
target woman. -/
lemma proposalStep_proposed_self {σ : GSState P} {m : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) :
    (proposalStep σ m hfree hpend).proposed m =
      insert (nextWoman σ m hpend) (σ.proposed m) := by
  simp [proposalStep]

/-- Other men's proposed sets are unchanged by a proposal step. -/
lemma proposalStep_proposed_other {σ : GSState P} {m m' : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) (hmm : m' ≠ m) :
    (proposalStep σ m hfree hpend).proposed m' = σ.proposed m' := by
  simp [proposalStep, hmm]

/-- The target woman's partner after a proposal step: she accepts exactly when
she is free or prefers the proposer. -/
lemma proposalStep_wPartner_target {σ : GSState P} {m : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) :
    (proposalStep σ m hfree hpend).wPartner (nextWoman σ m hpend) =
      if accepts σ m (nextWoman σ m hpend) then some m
      else σ.wPartner (nextWoman σ m hpend) := by
  simp [proposalStep]

/-- Other women's partners are unchanged by a proposal step. -/
lemma proposalStep_wPartner_other {σ : GSState P} {m : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) {w' : W} (hww : w' ≠ nextWoman σ m hpend) :
    (proposalStep σ m hfree hpend).wPartner w' = σ.wPartner w' := by
  simp [proposalStep, hww]

/-- The proposing man's partner after a proposal step: the target woman when
she accepts, and unmatched otherwise. -/
lemma proposalStep_mPartner_self {σ : GSState P} {m : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) :
    (proposalStep σ m hfree hpend).mPartner m =
      if accepts σ m (nextWoman σ m hpend) then some (nextWoman σ m hpend) else none := by
  by_cases hacc : accepts σ m (nextWoman σ m hpend)
  · simp [proposalStep, hacc, hfree]
  · simp [proposalStep, hacc, hfree]

/-- When a woman accepts a new man, her current partner is freed. -/
lemma proposalStep_mPartner_dump {σ : GSState P} {m m' : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) (hmm : m' ≠ m)
    (hacc : accepts σ m (nextWoman σ m hpend))
    (hwm : σ.wPartner (nextWoman σ m hpend) = some m') :
    (proposalStep σ m hfree hpend).mPartner m' = none := by
  simp [proposalStep, hmm, hacc, hwm]

/-- A man who is neither the proposer nor freed keeps his partner. -/
lemma proposalStep_mPartner_other {σ : GSState P} {m m' : M} (hfree : σ.mPartner m = none)
    (hpend : σ.proposed m ≠ Finset.univ) (hmm : m' ≠ m)
    (hnot : ¬ (accepts σ m (nextWoman σ m hpend) ∧
      σ.wPartner (nextWoman σ m hpend) = some m')) :
    (proposalStep σ m hfree hpend).mPartner m' = σ.mPartner m' := by
  simp [proposalStep, hmm, hnot]

/-- One proposal step of the algorithm: an arbitrary free man with a pending
proposal proposes to his most preferred unproposed woman.  If no proposal is
pending, the state is unchanged. -/
noncomputable def step (σ : GSState P) : GSState P :=
  if h : hasPending σ then
    proposalStep σ (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2
  else σ

/-- Without a pending proposal, a step changes nothing. -/
lemma step_eq_self_of_no_pending {σ : GSState P} (h : ¬ hasPending σ) : step σ = σ := by
  simp [step, h]

/--
The loop invariants of the proposal algorithm: every woman who has been
proposed to is matched, every matched woman prefers her current partner to
every man who has proposed to her, every man's proposed set is a rank prefix
(a woman of smaller rank implies all even more preferred women were proposed
to), and every man has proposed to his current partner.
-/
def Invariant (σ : GSState P) : Prop :=
  (∀ w m, w ∈ σ.proposed m → σ.wPartner w ≠ none) ∧
    (∀ w m₀, σ.wPartner w = some m₀ →
      ∀ m, w ∈ σ.proposed m → P.wRank w m₀ ≤ P.wRank w m) ∧
    (∀ m w₁ w₂, w₁ ∈ σ.proposed m → P.mRank m w₂ < P.mRank m w₁ → w₂ ∈ σ.proposed m) ∧
    (∀ m w, σ.mPartner m = some w → w ∈ σ.proposed m)

/-- Every woman who has been proposed to is matched. -/
lemma Invariant.w_proposed_matched {σ : GSState P} (hσ : Invariant σ) {w : W} {m : M}
    (h : w ∈ σ.proposed m) : σ.wPartner w ≠ none :=
  hσ.1 w m h

/-- A matched woman prefers her current partner to every man who has proposed
to her. -/
lemma Invariant.best_among_proposers {σ : GSState P} (hσ : Invariant σ) {w : W} {m₀ : M}
    (hw : σ.wPartner w = some m₀) {m : M} (hm : w ∈ σ.proposed m) :
    P.wRank w m₀ ≤ P.wRank w m :=
  hσ.2.1 w m₀ hw m hm

/-- Every man's proposed set is a rank prefix. -/
lemma Invariant.downward_closed {σ : GSState P} (hσ : Invariant σ) {m : M} {w₁ w₂ : W}
    (h₁ : w₁ ∈ σ.proposed m) (h₂ : P.mRank m w₂ < P.mRank m w₁) : w₂ ∈ σ.proposed m :=
  hσ.2.2.1 m w₁ w₂ h₁ h₂

/-- Every man has proposed to his current partner. -/
lemma Invariant.partner_proposed {σ : GSState P} (hσ : Invariant σ) {m : M} {w : W}
    (h : σ.mPartner m = some w) : w ∈ σ.proposed m :=
  hσ.2.2.2 m w h

/-- The initial state: nobody is matched and nobody has proposed. -/
def init : GSState P :=
  { mPartner := fun _ => none
    wPartner := fun _ => none
    h_consistency := by simp
    proposed := fun _ => ∅ }

/-- The initial state satisfies the invariants. -/
lemma init_invariant : Invariant (init : GSState P) := by
  unfold Invariant init
  simp

/-- A proposal step preserves the invariants. -/
lemma step_preserves_invariant {σ : GSState P} (hσ : Invariant σ) : Invariant (step σ) := by
  by_cases h : hasPending σ
  · have hstep : step σ = proposalStep σ (Classical.choose h) (Classical.choose_spec h).1
        (Classical.choose_spec h).2 := by
      simp [step, h]
    rw [hstep]
    let m := Classical.choose h
    have hspec := Classical.choose_spec h
    let w := nextWoman σ m hspec.2
    have hw_not : w ∉ σ.proposed m := nextWoman_not_proposed σ m hspec.2
    have hw_min : ∀ w' ∈ Finset.univ \ σ.proposed m, P.mRank m w ≤ P.mRank m w' := by
      intro w'' hw''
      exact nextWoman_min_rank σ m hspec.2 hw''
    unfold Invariant
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w' m' hmem
      by_cases hmm' : m' = m
      · subst m'
        have hmem' : w' ∈ insert w (σ.proposed m) := by
          rwa [proposalStep_proposed_self hspec.1 hspec.2] at hmem
        rcases Finset.mem_insert.mp hmem' with hw' | hw'
        · subst w'
          rw [proposalStep_wPartner_target hspec.1 hspec.2]
          change (if accepts σ m w then some m else σ.wPartner w) ≠ none
          by_cases hacc : accepts σ m w
          · simp [hacc]
          · simp [hacc]
            intro hnone
            exact hacc (Or.inl hnone)
        · have hwn : σ.wPartner w' ≠ none := hσ.w_proposed_matched hw'
          by_cases hww' : w' = w
          · subst w'
            exact False.elim (hw_not hw')
          · rw [proposalStep_wPartner_other hspec.1 hspec.2 hww']
            exact hwn
      · have hmem' : w' ∈ σ.proposed m' := by
          rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm'] at hmem
        have hwn : σ.wPartner w' ≠ none := hσ.w_proposed_matched hmem'
        by_cases hww' : w' = w
        · subst w'
          rw [proposalStep_wPartner_target hspec.1 hspec.2]
          change (if accepts σ m w then some m else σ.wPartner w) ≠ none
          by_cases hacc : accepts σ m w
          · simp [hacc]
          · simp [hacc]
            exact hwn
        · rw [proposalStep_wPartner_other hspec.1 hspec.2 hww']
          exact hwn
    · intro w' m₀ hwm₀
      by_cases hww' : w' = w
      · subst w'
        rw [proposalStep_wPartner_target hspec.1 hspec.2] at hwm₀
        change (if accepts σ m w then some m else σ.wPartner w) = some m₀ at hwm₀
        by_cases hacc : accepts σ m w
        · have hm₀ : m = m₀ := by
            simp [hacc] at hwm₀
            simpa using hwm₀
          subst m₀
          intro m'' hmem''
          by_cases hmm'' : m'' = m
          · subst m''
            rfl
          · have hmemσ : w ∈ σ.proposed m'' := by
              rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm''] at hmem''
            by_cases hwfree : σ.wPartner w = none
            · exact False.elim ((hσ.w_proposed_matched hmemσ) hwfree)
            · have hacc' : ∃ m₁, σ.wPartner w = some m₁ ∧ P.wPrefers w m m₁ := by
                rcases hacc with hnone | hpref
                · exact False.elim (hwfree hnone)
                · exact hpref
              rcases hacc' with ⟨m₁, hwm₁, hpref⟩
              have hle : P.wRank w m₁ ≤ P.wRank w m'' := hσ.best_among_proposers hwm₁ hmemσ
              exact le_trans (le_of_lt hpref) hle
        · have hwm₀' : σ.wPartner w = some m₀ := by
            simp [hacc] at hwm₀
            exact hwm₀
          have hnotpref : ¬ ∃ m₁, σ.wPartner w = some m₁ ∧ P.wPrefers w m m₁ := by
            intro hpref
            exact hacc (Or.inr hpref)
          have hnotw : ¬ P.wPrefers w m m₀ := by
            intro hpref
            exact hnotpref ⟨m₀, hwm₀', hpref⟩
          intro m'' hmem''
          by_cases hmm'' : m'' = m
          · subst m''
            exact le_of_not_gt hnotw
          · have hmemσ : w ∈ σ.proposed m'' := by
              rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm''] at hmem''
            exact hσ.best_among_proposers hwm₀' hmemσ
      · have hwmσ : σ.wPartner w' = some m₀ := by
          rwa [proposalStep_wPartner_other hspec.1 hspec.2 hww'] at hwm₀
        intro m'' hmem''
        by_cases hmm'' : m'' = m
        · subst m''
          have hmem' : w' ∈ insert w (σ.proposed m) := by
            rwa [proposalStep_proposed_self hspec.1 hspec.2] at hmem''
          rcases Finset.mem_insert.mp hmem' with hw' | hw'
          · subst w'
            exact False.elim (hww' rfl)
          · exact hσ.best_among_proposers hwmσ hw'
        · have hmemσ : w' ∈ σ.proposed m'' := by
            rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm''] at hmem''
          exact hσ.best_among_proposers hwmσ hmemσ
    · intro m' w₁ w₂ hmem₁ hlt
      by_cases hmm' : m' = m
      · subst m'
        have hmem₁' : w₁ ∈ insert w (σ.proposed m) := by
          rwa [proposalStep_proposed_self hspec.1 hspec.2] at hmem₁
        rcases Finset.mem_insert.mp hmem₁' with hw₁ | hw₁
        · subst w₁
          by_cases hw₂ : w₂ = w
          · subst w₂
            rw [proposalStep_proposed_self hspec.1 hspec.2]
            exact Finset.mem_insert_self w (σ.proposed m)
          · have hw₂' : w₂ ∈ σ.proposed m := by
              by_contra hnot
              have hw₂c : w₂ ∈ Finset.univ \ σ.proposed m :=
                Finset.mem_sdiff.mpr ⟨Finset.mem_univ w₂, hnot⟩
              exact (lt_irrefl (P.mRank m w)) (lt_of_le_of_lt (hw_min w₂ hw₂c) hlt)
            rw [proposalStep_proposed_self hspec.1 hspec.2]
            exact Finset.mem_insert_of_mem hw₂'
        · have hw₂' : w₂ ∈ σ.proposed m := hσ.downward_closed hw₁ hlt
          rw [proposalStep_proposed_self hspec.1 hspec.2]
          exact Finset.mem_insert_of_mem hw₂'
      · have hmem₁' : w₁ ∈ σ.proposed m' := by
          rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm'] at hmem₁
        have hw₂' : w₂ ∈ σ.proposed m' := hσ.downward_closed hmem₁' hlt
        rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm']
    · intro m' w' hm
      by_cases hmm' : m' = m
      · subst m'
        rw [proposalStep_mPartner_self hspec.1 hspec.2] at hm
        change (if accepts σ m w then some w else none) = some w' at hm
        by_cases hacc : accepts σ m w
        · simp [hacc] at hm
          have hEq : w = w' := by
            simpa using hm
          rw [← hEq]
          rw [proposalStep_proposed_self hspec.1 hspec.2]
          exact Finset.mem_insert_self w (σ.proposed m)
        · simp [hacc] at hm
      · by_cases hdump : accepts σ m w ∧ σ.wPartner w = some m'
        · rcases hdump with ⟨hacc, hwm⟩
          rw [proposalStep_mPartner_dump hspec.1 hspec.2 hmm' hacc hwm] at hm
          simp at hm
        · have hmσ : σ.mPartner m' = some w' := by
            rwa [proposalStep_mPartner_other hspec.1 hspec.2 hmm' hdump] at hm
          have hprop : w' ∈ σ.proposed m' := hσ.partner_proposed hmσ
          rwa [proposalStep_proposed_other hspec.1 hspec.2 hmm']
  · simp [step, h]
    exact hσ

/-- **Invariant (women only improve).** When a woman changes partner in a
proposal step, she strictly prefers the new partner to the old one. -/
lemma step_partner_improves {σ : GSState P} {w : W} {m₁ m₂ : M}
    (hold : σ.wPartner w = some m₁) (hnew : (step σ).wPartner w = some m₂)
    (hne : m₁ ≠ m₂) : P.wPrefers w m₂ m₁ := by
  by_cases h : hasPending σ
  · rw [step, dif_pos h] at hnew
    let m := Classical.choose h
    have hspec := Classical.choose_spec h
    by_cases hww : w = nextWoman σ m hspec.2
    · subst w
      rw [proposalStep_wPartner_target hspec.1 hspec.2] at hnew
      change (if accepts σ m (nextWoman σ m hspec.2) then some m
          else σ.wPartner (nextWoman σ m hspec.2)) = some m₂ at hnew
      by_cases hacc : accepts σ m (nextWoman σ m hspec.2)
      · simp [hacc] at hnew
        have hm₂ : m₂ = m := by
          exact hnew.symm
        subst m₂
        have hacc' : ∃ m₃, σ.wPartner (nextWoman σ m hspec.2) = some m₃ ∧
            P.wPrefers (nextWoman σ m hspec.2) m m₃ := by
          rcases hacc with hnone | hpref
          · exfalso
            rw [hold] at hnone
            simp at hnone
          · exact hpref
        rcases hacc' with ⟨m₃, hw₃, hpref⟩
        have hm₃ : m₃ = m₁ := by
          rw [hold] at hw₃
          exact Option.some.inj hw₃.symm
        simpa [hm₃] using hpref
      · simp [hacc] at hnew
        rw [hold] at hnew
        exact False.elim (hne (by simpa using hnew))
    · rw [proposalStep_wPartner_other hspec.1 hspec.2 hww] at hnew
      rw [hold] at hnew
      exact False.elim (hne (by simpa using hnew))
  · simp [step, h] at hnew
    rw [hold] at hnew
    exact False.elim (hne (by simpa using hnew))

end StableMarriage

end CLRS
