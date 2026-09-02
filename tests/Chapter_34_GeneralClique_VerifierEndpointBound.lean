import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Canonical

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

#check endpointsWithinBool_eq_true_iff
#check endpointBoundPass_encode_iff
#check program

example :
    endpointBoundPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(0, 2), (1, 3)] }) =
      true := by
  decide

example :
    endpointBoundPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(0, 4)] }) =
      false := by
  decide
