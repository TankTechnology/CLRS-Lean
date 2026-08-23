import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeBounds

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier

#check EdgeOrder.edgeOrderPassComputableInPolyTime
#check EndpointBound.endpointBoundPassComputableInPolyTime
#check concreteEdgeBoundsPass_encode_eq
#check concreteEdgeBoundsPass_encode_iff

example :
    concreteEdgeBoundsPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(0, 2), (1, 3)] }) =
      true := by
  decide

example :
    concreteEdgeBoundsPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [(2, 1), (0, 4)] }) =
      false := by
  decide
