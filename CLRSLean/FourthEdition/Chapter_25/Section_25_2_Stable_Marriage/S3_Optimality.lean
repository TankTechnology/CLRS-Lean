import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S1_Preference_Model
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S2_Gale_Shapley

/-!
# S3. Optimality of the Gale–Shapley output

The stable-marriage theorems of CLRS §25.2: the Gale–Shapley output is a
stable pairing, and every preference profile admits a stable pairing.

Main results:

- `gs_stable`: the Gale–Shapley output is stable (CLRS Theorem 25.5)
- `stable_matching_exists`: every preference profile has a stable pairing
- `unmatched_man_proposes_to_all`: at the final state an unmatched man has
  proposed to every woman

Current gaps:

- The perfectness theorem (all men matched when `|M| = |W|`, via the
  matched-pair cardinality argument) and man-optimality remain to be
  formalized.
-/

namespace CLRS

namespace StableMarriage

open Finset Classical Matchings

variable {M : Type*} [Fintype M] [DecidableEq M]
variable {W : Type*} [Fintype W] [DecidableEq W]

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
  -- `w` was proposed to by `m`: either `m` is unmatched (and proposed to
  -- everyone) or `m` prefers `w` to his partner (rank-prefix closure).
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
  -- `w` is matched, so the blocking condition must hold on the preference side.
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

end StableMarriage

end CLRS
