import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S2_Alternating_Paths
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S5_Residual_Translation

/-!
# S6. Berge's lemma and the flow-method headline

The section's closing theorems: Berge's maximum-matching characterisation
and the flow-method existence and certification theorem.

Main results:

- `berge_maximum_iff_no_augmentingPath` (Berge's lemma): a matching is
  maximum iff it admits no augmenting path
- `flowMethod_finds_maximum_matching`: a maximum matching exists, and the
  flow method certifies it
-/
namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
/-! ## Berge's lemma and the flow-method headline -/

/-- **Berge's lemma** (CLRS §25.1): a matching is maximum if and only if it
admits no augmenting path. -/
theorem berge_maximum_iff_no_augmentingPath (M : Matching V G) :
    M.IsMaximum ↔ ¬ ∃ p : List V, IsAugmentingPath G M p := by
  constructor
  · rintro hmax ⟨p, hp⟩
    exact not_isMaximum_of_isAugmentingPath hp hmax
  · intro hno
    have hφ : ¬ (matchingToFlow M).hasAugmentingPath := fun h =>
      hno (augmentingPath_of_hasAugmentingPath M h)
    have hmaxφ := Flow.maximal_of_noAugmentingPath _ hφ
    intro M'
    have hle := hmaxφ (matchingToFlow M')
    rw [matchingToFlow_value, matchingToFlow_value] at hle
    exact_mod_cast hle

/-- **Flow-method correctness** (CLRS §25.1, revisited): a maximum matching
exists, and the flow method certifies it — there is a maximal flow in the
unit-capacity network whose value is exactly the size of a maximum
matching. -/
theorem flowMethod_finds_maximum_matching (G : BipartiteGraph V) :
    ∃ M : Matching V G, M.IsMaximum ∧
      ∃ φ : Flow (V ⊕ Bool) (toFlowNetwork V G), φ.isMaximal ∧
        φ.value = (M.size : ℝ) := by
  obtain ⟨M, hM, φ, hφ, hval⟩ := maxMatching_eq_maxFlow_value (G := G)
  exact ⟨M, hM, φ, hφ, hval⟩

end Matchings

end CLRS
