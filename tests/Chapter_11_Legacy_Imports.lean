import CLRSLean.Chapter_11.Section_11_1_Direct_Address_Tables
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables
import CLRSLean.Chapter_11.Section_11_3_Hash_Functions
import CLRSLean.Chapter_11.Section_11_4_Open_Addressing
import CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing

/-!
# Chapter 11 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter11.search_insert_same
#check CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor
#check CLRS.Chapter11.affineHashMod_isUniversal
#check CLRS.Chapter11.expectedSuccessfulProbes_le_ln
#check CLRS.Chapter11.perfectSearch_iff_mem
#check CLRS.Chapter11.perfectHash_expected_total_space_lt_2n
