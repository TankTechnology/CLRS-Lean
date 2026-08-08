import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S1_Preference_Model
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S2_Gale_Shapley

/-!
# S3. Optimality of the Gale–Shapley output

The stable-marriage theorems of CLRS §25.2: the Gale–Shapley output is a
stable pairing, every preference profile admits a stable pairing, and the
output is a perfect pairing when the two sides have equal size.

Main results:

- `gs_stable`: the Gale–Shapley output is stable (CLRS Theorem 25.5)
- `stable_matching_exists`: every preference profile has a stable pairing
- `gs_perfect`: with equal numbers of men and women, the Gale–Shapley output
  is a perfect pairing
- `unmatched_man_proposes_to_all`: at the final state an unmatched man has
  proposed to every woman

Current gaps:

- Man-optimality remains to be formalized.
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
      matched_card_eq hM
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

end StableMarriage

end CLRS
