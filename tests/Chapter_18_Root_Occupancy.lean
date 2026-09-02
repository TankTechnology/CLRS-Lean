import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# Regression tests for root-specific B-tree occupancy

An internal root has a root-specific lower bound of two children.  A non-root
internal node keeps the ordinary lower bound of `t` children.
-/

namespace CLRS
namespace Chapter18
namespace BTree

private def rootWithTwoChildren : BTree :=
  node [10] [node [1, 2] [], node [11, 12] []]

private def nonRootWithTwoChildren : BTree :=
  node [10, 20] [node [1, 2] [], node [21, 22] []]

/--
For minimum degree three, a one-key internal root with two occupied leaf
children is a valid root occupancy shape.
-/
example : Occupancy 3 true rootWithTwoChildren := by
  simp [rootWithTwoChildren, Occupancy]

/--
The corresponding non-root child-count lower bound remains `t`, so two
children are insufficient when `t = 3`.
-/
example : ¬ Occupancy 3 false nonRootWithTwoChildren := by
  simp [nonRootWithTwoChildren, Occupancy]

end BTree
end Chapter18
end CLRS
