import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes

/-!
# Textbook interfaces for Huffman Lemmas 15.2 and 15.3

The core exchange proof is intentionally packaged behind
{lit}`SplitLeafOptimalitySpec`.  These short corollaries expose the two textbook
ideas under stable, searchable names.
-/

namespace CLRS.HuffmanV2

theorem areSiblings_splitLeaf (t : HuffTree) (z b fa fb : Nat)
    (hz : z ∈ alphabet t) :
    areSiblings z b (splitLeaf t z z b fa fb) := by
  induction t with
  | htLeaf s f =>
      simp [alphabet] at hz
      subst s
      simp [splitLeaf]
      exact areSiblings.here fa fb
  | htInner l r ihl ihr =>
      rw [alphabet, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact areSiblings.inLeft _ _ (ihl hz)
      · exact areSiblings.inRight _ _ (ihr hz)

/--
CLRS Lemma 15.2 (greedy-choice property): the two minimum-frequency symbols
occur as sibling leaves in an optimal expanded tree.
-/
theorem lemma15_2_greedy_choice {t : HuffTree} {z b fa fb : Nat}
    (S : SplitLeafOptimalitySpec t z b fa fb) (hopt : optimum t) :
    ∃ u, optimum u ∧ areSiblings z b u := by
  refine ⟨splitLeaf t z z b fa fb,
    split_leaf_preserves_optimum S hopt, ?_⟩
  exact areSiblings_splitLeaf t z b fa fb S.z_mem

/--
CLRS Lemma 15.3 (optimal substructure): expanding an optimal code for the
merged alphabet at its merged leaf yields an optimal code for the original
alphabet.
-/
theorem lemma15_3_optimal_substructure {t : HuffTree} {z b fa fb : Nat}
    (S : SplitLeafOptimalitySpec t z b fa fb) (hopt : optimum t) :
    optimum (splitLeaf t z z b fa fb) :=
  split_leaf_preserves_optimum S hopt

end CLRS.HuffmanV2
