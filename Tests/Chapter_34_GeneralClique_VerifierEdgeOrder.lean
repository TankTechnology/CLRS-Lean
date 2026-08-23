import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Canonical

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

#check edgeOrder_run
#check edgeOrderSteps_le
#check edgeOrderPassComputableInPolyTime
#check edgeOrderPass_encode_iff

example :
    edgeOrderPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(0, 2), (1, 3)] }) =
      true := by
  decide

example :
    edgeOrderPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(2, 1)] }) = false := by
  decide
