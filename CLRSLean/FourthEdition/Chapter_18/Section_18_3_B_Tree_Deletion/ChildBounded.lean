import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation

/-!
# B-tree deletion: child-bound projection

This submodule retains the public {lit}`composedDelete_childBounded` name as
a small projection from the bundled raw-deletion preservation theorem.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
Raw deletion preserves recursive child key ranges for a structurally
well-formed input node.
-/
lemma composedDelete_childBounded
    (t x : Nat) (ht : 2 ≤ t) (tr : BTree) {isRoot : Bool}
    (hinv : NodeWF t isRoot tr) :
    ChildBounded (composedDelete t x tr) := by
  exact
    (composedDelete_rootResult t x ht (hinv.asRoot ht)).2.1.2.1

end BTree
end Chapter18
end CLRS
