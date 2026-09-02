import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.Verification

/-!
# Chapter 34 SAT certificate interface checks

These checks pin the total serialized assignment checker and its bounded
certificate characterization before the checker is lowered to a fixed TM2.
-/

namespace CLRS.Chapter34

#check formulaAssignmentInputs
#check encodeFormulaAssignment
#check satVerifier
#check satVerifier_accepts_iff
#check mem_SAT_iff_exists_bounded_certificate

#print axioms satVerifier_accepts_iff
#print axioms mem_SAT_iff_exists_bounded_certificate

end CLRS.Chapter34
