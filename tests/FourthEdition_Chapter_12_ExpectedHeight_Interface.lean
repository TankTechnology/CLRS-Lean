import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees.ExpectedHeight

/-!
# Fourth-edition Chapter 12 expected-height interface checks

These checks pin the textbook expected-height theorem for a binary search tree
built from a uniform random insertion permutation.
-/

namespace CLRS
namespace Chapter12
namespace BSTree

#check height_buildFromPerm_eq_treapHeight
#check expectedHeight
#check expected_height_eq_treap
#check expected_height_le_thirty_harmonic
#check expected_height_le_O_log

end BSTree
end Chapter12
end CLRS
