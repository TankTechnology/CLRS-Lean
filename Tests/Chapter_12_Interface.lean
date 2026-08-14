import CLRSLean.Chapter_12

#check CLRS.Chapter12.BSTree.Frame
#check CLRS.Chapter12.BSTree.Zipper
#check CLRS.Chapter12.BSTree.searchZipper
#check CLRS.Chapter12.BSTree.searchZipper_toTree
#check CLRS.Chapter12.BSTree.searchIter_eq_search
#check CLRS.Chapter12.BSTree.transplant
#check CLRS.Chapter12.BSTree.transplant_preserves_ordered
#check CLRS.Chapter12.BSTree.deleteViaTransplant
#check CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete
#check CLRS.Chapter12.BSTree.successorZipper
#check CLRS.Chapter12.BSTree.successorZipper_eq_successor?
#check CLRS.Chapter12.BSTree.predecessorZipper
#check CLRS.Chapter12.BSTree.predecessorZipper_eq_predecessor?

-- Imperative pointer-heap model and TRANSPLANT/insert refinement (Issue #25)
#check CLRS.Chapter12.BSTree.Node
#check CLRS.Chapter12.BSTree.Store
#check CLRS.Chapter12.BSTree.RepresentsW
#check CLRS.Chapter12.BSTree.RepresentsW.tree_unique
#check CLRS.Chapter12.BSTree.RepresentsW.set_of_not_mem
#check CLRS.Chapter12.BSTree.RepresentsW.of_agreeChild
#check CLRS.Chapter12.BSTree.Store.transplantChild
#check CLRS.Chapter12.BSTree.transplantChild_left_representsW
#check CLRS.Chapter12.BSTree.transplantChild_right_representsW
#check CLRS.Chapter12.BSTree.transplantChild_left_refines_transplant
#check CLRS.Chapter12.BSTree.transplantChild_right_refines_transplant
#check CLRS.Chapter12.BSTree.insertPointer_right_representsW


-- Running-time / cost layer (O(h))
#check CLRS.Chapter12.BSTree.height
#check CLRS.Chapter12.BSTree.searchCost
#check CLRS.Chapter12.BSTree.minimumCost
#check CLRS.Chapter12.BSTree.maximumCost
#check CLRS.Chapter12.BSTree.successorCost
#check CLRS.Chapter12.BSTree.predecessorCost
#check CLRS.Chapter12.BSTree.insertCost
#check CLRS.Chapter12.BSTree.minKeyCost
#check CLRS.Chapter12.BSTree.deleteMinCost
#check CLRS.Chapter12.BSTree.deleteRootCost
#check CLRS.Chapter12.BSTree.deleteCost
#check CLRS.Chapter12.BSTree.searchCost_le_height
#check CLRS.Chapter12.BSTree.minimumCost_le_height
#check CLRS.Chapter12.BSTree.maximumCost_le_height
#check CLRS.Chapter12.BSTree.successorCost_le_height
#check CLRS.Chapter12.BSTree.predecessorCost_le_height
#check CLRS.Chapter12.BSTree.insertCost_le_height
#check CLRS.Chapter12.BSTree.minKeyCost_le_height
#check CLRS.Chapter12.BSTree.deleteMinCost_le_height
#check CLRS.Chapter12.BSTree.deleteRootCost_le
#check CLRS.Chapter12.BSTree.deleteCost_le

-- Randomly built BST (Section 12.4) ancestor characterization
#check CLRS.Chapter12.BSTree.depth
#check CLRS.Chapter12.BSTree.isAncestorOf
#check CLRS.Chapter12.BSTree.insertAll
#check CLRS.Chapter12.BSTree.buildFromList
#check CLRS.Chapter12.BSTree.buildFromPerm
#check CLRS.Chapter12.BSTree.IsFirstInInterval
#check CLRS.Chapter12.BSTree.firstInInterval
#check CLRS.Chapter12.BSTree.isAncestorOf_iff_firstInInterval
#check CLRS.Chapter12.BSTree.isAncestorOf_implies_inTree
#check CLRS.Chapter12.BSTree.InTree_buildFromList_iff
#check CLRS.Chapter12.BSTree.insertAll_split
#check CLRS.Chapter12.BSTree.buildFromList_cons
#check CLRS.Chapter12.BSTree.firstInInterval_iff_isFirstOf
