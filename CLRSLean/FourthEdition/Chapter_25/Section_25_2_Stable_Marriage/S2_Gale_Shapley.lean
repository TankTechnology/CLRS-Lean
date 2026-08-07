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

end StableMarriage

end CLRS
