import CLRSLean.Chapter_04.Section_04_2_Strassen_Algorithm
import CLRSLean.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# Chapter 4 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter04.strassen2x2_correct
#check CLRS.Chapter04.strassenRec_correct
#check CLRS.Chapter04.strassen_runtime_bigTheta
#check CLRS.Chapter04.substitution_upper_bound
#check CLRS.Chapter04.substitution_sandwich
#check CLRS.Chapter04.recursion_tree_additive_unroll
#check CLRS.Chapter04.recursion_tree_additive_upper_envelope
#check CLRS.Chapter04.master_case1_geometric
#check CLRS.Chapter04.master_case2_constant_forcing
#check CLRS.Chapter04.master_case2_polylog_forcing
#check CLRS.Chapter04.master_case3_tail_dominated
