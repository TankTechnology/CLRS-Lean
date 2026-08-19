import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedRowInvocationSource

open StateTransition

open CLRS.Chapter34.Turing.PolyBuilder

#check encodeAffineExactlyOneStructuredRowOutputInvocationFamily
#check affineExactlyOneMarkedRowInvocationProgram
#check affineExactlyOneMarkedRowInvocation_run
#check affineExactlyOneMarkedRowInvocationSteps_le
#check affineExactlyOneMarkedRowInvocation_computableInPolyTime
#check affineExactlyOneStructuredRowOutputInvocationFamily_computableInPolyTime

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneMarkedRowInvocationSteps
        labelWidth stateWidth cellCounts seeds ≤
      14 * (encodeAffineExactlyOneStructuredRowMarkedFamily
        labelWidth stateWidth cellCounts seeds).reverse.length + 2 :=
  affineExactlyOneMarkedRowInvocationSteps_le
    labelWidth stateWidth cellCounts seeds

#print axioms affineExactlyOneMarkedRowInvocation_run
#print axioms affineExactlyOneMarkedRowInvocationSteps_le
#print axioms affineExactlyOneMarkedRowInvocation_computableInPolyTime
#print axioms affineExactlyOneStructuredRowOutputInvocationFamily_computableInPolyTime
