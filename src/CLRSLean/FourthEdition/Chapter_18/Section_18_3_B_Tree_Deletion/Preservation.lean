import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Repair

/-!
# Bundled preservation for B-tree deletion

The raw node operation may leave a one-child empty root, so its root
postcondition differs from the ordinary non-root invariant packet.  This
module proves both cases together and exposes root-normalized public results.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
The structural result expected from raw deletion at a node.  Recursive calls
return an ordinary non-root packet; the top-level call permits the single
empty-root transient recorded by {name}`RootDeleteResult`.
-/
def RawDeleteResult (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  if isRoot then RootDeleteResult t tr else NodeWF t false tr

/-- An ordinary invariant packet is always an admissible raw result. -/
theorem rawDeleteResult_of_nodeWF
    {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) :
    RawDeleteResult t isRoot tr := by
  cases isRoot with
  | false =>
      simpa [RawDeleteResult] using h
  | true =>
      simp only [RawDeleteResult, ↓reduceIte]
      exact
        ⟨h.sorted, h.childBounded, h.sameDepth,
          Or.inl h.occupancy⟩

/--
The leaf branch preserves all structural facts.  The readiness guard is used
only for a non-root leaf, where deleting one key must leave at least {lit}`t - 1`
keys.
-/
theorem deleteLeaf_packet
    {t x : Nat} {isRoot : Bool} {ks : List Nat}
    (hinv : NodeWF t isRoot (node ks []))
    (hready : DeleteReady t isRoot (node ks [])) :
    let out := node (sortedRemove x ks) []
    KeysSubset out (node ks []) ∧
      RawDeleteResult t isRoot out ∧
      heightOf out = heightOf (node ks []) := by
  have hsorted : Sorted (node (sortedRemove x ks) []) := by
    have hkeys := hinv.sorted
    unfold Sorted at hkeys ⊢
    exact
      ⟨sortedRemove_sorted x hkeys.1,
        by simp⟩
  have hbounded : ChildBounded (node (sortedRemove x ks) []) :=
    childBounded_node_nil _
  have hdepth : SameDepth (node (sortedRemove x ks) []) :=
    SameDepth.leaf _
  have hoccupancy :
      Occupancy t isRoot (node (sortedRemove x ks) []) := by
    have hold := hinv.occupancy
    have hlengthLe := sortedRemove_length_le x ks
    have hlengthGe := sortedRemove_length_ge x ks
    cases isRoot with
    | false =>
        have hreadyKeys : t ≤ ks.length := by
          simpa [DeleteReady, numKeys] using hready
        unfold Occupancy at hold ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at hold ⊢
        refine ⟨by omega, by omega, by simp, by simp⟩
    | true =>
        unfold Occupancy at hold ⊢
        simp only [↓reduceIte] at hold ⊢
        refine ⟨?_, by omega, by simp, by simp⟩
        by_cases hempty : sortedRemove x ks = []
        · simp [hempty]
        · have hzero : (sortedRemove x ks).length ≠ 0 := by
            intro hlength
            exact hempty (List.eq_nil_of_length_eq_zero hlength)
          simp [hzero]
          omega
  have hout :
      NodeWF t isRoot (node (sortedRemove x ks) []) :=
    ⟨hsorted, hbounded, hoccupancy, hdepth⟩
  have hsubset :
      KeysSubset (node (sortedRemove x ks) []) (node ks []) := by
    intro k hk
    simp only [keysOf, List.flatMap_nil, List.append_nil] at hk ⊢
    exact mem_of_sortedRemove hk
  exact
    ⟨hsubset, rawDeleteResult_of_nodeWF hout, by simp [heightOf]⟩

end BTree
end Chapter18
end CLRS
