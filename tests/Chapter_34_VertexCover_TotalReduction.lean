import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Reduction

open CLRS Chapter34

noncomputable section

namespace CLRS.Chapter34.Tests.VertexCoverTotalReduction

example :
    _root_.Turing.TM2ComputableInPolyTime id id
      cliqueToVertexCoverMap :=
  Turing.VertexCover.ComplementMachine.Total.computableInPolyTime

example : PolyTimeReducible GeneralCLIQUE VERTEXCOVER :=
  generalCLIQUE_reducible_to_VERTEXCOVER

example : NPHard VERTEXCOVER := VERTEXCOVER_npHard

#print axioms CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector.run
#print axioms CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Total.computableInPolyTime
#print axioms CLRS.Chapter34.generalCLIQUE_reducible_to_VERTEXCOVER
#print axioms CLRS.Chapter34.VERTEXCOVER_npHard

end CLRS.Chapter34.Tests.VertexCoverTotalReduction
