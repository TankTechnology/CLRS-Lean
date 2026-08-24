import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseRawReduction

/-!
# Regression test: total VERTEX-COVER-to-CLIQUE semantic reduction
-/

open CLRS Chapter34

#check CliqueInstance.complement_hasClique_of_hasVertexCover
#check CliqueInstance.hasVertexCover_of_complement_hasClique
#check CliqueInstance.hasVertexCover_iff_complement_hasClique
#check vertexCoverToCliqueMap
#check vertexCoverToCliqueMap_mem_CLIQUE_iff

#print axioms CliqueInstance.hasVertexCover_iff_complement_hasClique
#print axioms vertexCoverToCliqueMap_mem_CLIQUE_iff
