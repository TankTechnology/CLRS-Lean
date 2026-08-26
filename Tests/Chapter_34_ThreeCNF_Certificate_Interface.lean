import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.Verification

/-!
# Chapter 34 3-CNF-SAT certificate interface checks

These checks pin the total serialized assignment checker and its bounded
certificate characterization before the checker is lowered to a fixed TM2.
-/

namespace CLRS.Chapter34

#check cnfAssignmentInputs
#check encodeCNFAssignment
#check evalCNFBool_eq_true
#check threeCNFSatVerifier
#check threeCNFSatVerifier_accepts_iff
#check mem_threeCNFSat_iff_exists_bounded_certificate

#print axioms threeCNFSatVerifier_accepts_iff
#print axioms mem_threeCNFSat_iff_exists_bounded_certificate

end CLRS.Chapter34
