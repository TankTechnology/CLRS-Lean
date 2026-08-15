import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation

/-!
# B-tree deletion: key-set subset and key-bound projections

This submodule exposes the key-set component of the bundled raw-deletion
preservation theorem.  The input carries a complete {lit}`NodeWF` packet:
without that premise, deletion on malformed trees may synthesize a default
separator key.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-! ## Result keys come from the input tree -/

/--
Every key represented by raw deletion was already represented by the input.
The root view is sufficient because {lit}`NodeWF.asRoot` weakens non-root
occupancy while preserving the other structural invariants.
-/
lemma keysOf_composedDelete_subset
    (t x : Nat) (ht : 2 ≤ t) (tr : BTree) {isRoot : Bool}
    (hinv : NodeWF t isRoot tr) (k : Nat)
    (hk : k ∈ keysOf (composedDelete t x tr)) :
    k ∈ keysOf tr := by
  exact
    (composedDelete_rootResult t x ht (hinv.asRoot ht)).1 k hk

/-! ## Key-bound transfer -/

/--
Transfer a lower key bound through raw deletion.  The complete invariant
packet supplies the premise needed by the subset theorem.
-/
lemma composedDelete_key_bound_lo
    (t x : Nat) (ht : 2 ≤ t) (tr : BTree) {isRoot : Bool}
    (hinv : NodeWF t isRoot tr) (lo : Nat)
    (hlo : ∀ k ∈ keysOf tr, lo ≤ k) :
    ∀ k ∈ keysOf (composedDelete t x tr), lo ≤ k :=
  fun k hk =>
    hlo k (keysOf_composedDelete_subset t x ht tr hinv k hk)

/-- Transfer an upper key bound through raw deletion. -/
lemma composedDelete_key_bound_hi
    (t x : Nat) (ht : 2 ≤ t) (tr : BTree) {isRoot : Bool}
    (hinv : NodeWF t isRoot tr) (hi : Nat)
    (hhi : ∀ k ∈ keysOf tr, k ≤ hi) :
    ∀ k ∈ keysOf (composedDelete t x tr), k ≤ hi :=
  fun k hk =>
    hhi k (keysOf_composedDelete_subset t x ht tr hinv k hk)

end BTree
end Chapter18
end CLRS
