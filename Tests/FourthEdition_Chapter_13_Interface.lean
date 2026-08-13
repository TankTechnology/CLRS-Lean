import CLRSLean.FourthEdition.Chapter_13

/-!
# Fourth-edition Chapter 13 interface checks

These checks pin the public theorem interface of the fourth-edition sections
§13.2 (rotations + pointer/sentinel store), §13.3 (insertion), and §13.4
(deletion).
-/

namespace CLRS
namespace Chapter13

-- §13.2 pointer/sentinel store + rotations
#check RBNode
#check RBStore
#check RBStore.nil
#check RBStore.get
#check RBStore.set
#check RBStore.get_set_eq
#check RBStore.get_set_ne
#check StoreRepr
#check Represents
#check RBTree.keys
#check RBTree.keys_rotateLeft
#check RBTree.keys_rotateRight
#check RBTree.keys_repaintRoot
#check RBTree.bst_rotateLeft
#check RBTree.bst_rotateRight
#check RBTree.bst_repaintRoot
#check rotateCost
#check rotateLeftP
#check rotateRightP
#check recolorP
#check rotateLeftP_cost
#check rotateRightP_cost
#check recolorP_spec
#check set_frame

-- §13.3 insertion
#check RBTree.keys_mem
#check RBTree.bst_iff_sorted
#check RBTree.keys_balanceLeft
#check RBTree.keys_balanceRight
#check RBTree.bst_balanceLeft
#check RBTree.bst_balanceRight
#check RBTree.bst_insert
#check RBTree.insertCost
#check RBTree.insertCost_le
#check RBTree.insertCost_log_bound

-- §13.4 deletion
#check RBTree.deleteCost
#check RBTree.deleteCost_le
#check RBTree.deleteCost_log_bound

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms RBTree.bst_insert
#print axioms RBTree.insertCost_log_bound
#print axioms RBTree.deleteCost_log_bound

end Chapter13
end CLRS
