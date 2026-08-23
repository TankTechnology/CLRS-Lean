import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Runtime

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass

private def triangle : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (0, 2), (1, 2)] }

example : syntaxPass (encodeCliqueCertificate [0, 1, 2])
    (encodeCliqueInstance triangle) = true := by native_decide

example : syntaxPass [.certificateMark, .vertexMark]
    (encodeCliqueInstance triangle) = false := by native_decide

#check syntaxPassStream_pairEncoding
#check syntaxPass_eq_true_iff
#check syntaxPassComputableInPolyTime

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass
