import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.Search
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.RunningTime
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion

/-!
# Chapter 18 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter18.BTree.search_true_iff
#check CLRS.Chapter18.BTree.searchExec_sound
#check CLRS.Chapter18.BTree.wellFormed_height_log_bound
#check CLRS.Chapter18.BTree.splitChild_valid
#check CLRS.Chapter18.BTree.delete_valid
#check CLRS.Chapter18.BTree.diskAccessBound
#check CLRS.Chapter18.BTree.searchCost_le_diskAccessBound
