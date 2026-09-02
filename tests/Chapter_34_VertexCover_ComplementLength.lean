import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMapLength

/-!
# Regression test: polynomial size of the VERTEX-COVER complement maps
-/

open CLRS Chapter34

#check vertexCoverNormalizedPairRow_length_le
#check vertexCoverNormalizedPairs_length_le
#check vertexCoverComplementEdges_length_le
#check encode_complementForVertexCover_length_le
#check cliqueToVertexCoverMap_length_le
#check vertexCoverToCliqueMap_length_le

#print axioms encode_complementForVertexCover_length_le
#print axioms cliqueToVertexCoverMap_length_le
#print axioms vertexCoverToCliqueMap_length_le
