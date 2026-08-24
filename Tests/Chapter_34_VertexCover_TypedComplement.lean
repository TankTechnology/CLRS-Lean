import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.TypedComplement

open CLRS Chapter34

noncomputable section

namespace CLRS.Chapter34.Tests.VertexCoverTypedComplement

example (I : CliqueInstance) :
    Turing.VertexCover.ComplementMachine.TypedComplement.serializedComplement I =
      encodeCliqueInstance I.complementForVertexCover :=
  Turing.VertexCover.ComplementMachine.TypedComplement.serializedComplement_eq I

example :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueInstance
      encodeCliqueInstance CliqueInstance.complementForVertexCover :=
  Turing.VertexCover.ComplementMachine.TypedComplement.computableInPolyTime

#print axioms CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header.run
#print axioms CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header.computableInPolyTime
#print axioms CLRS.Chapter34.Turing.VertexCover.ComplementMachine.TypedComplement.computableInPolyTime

end CLRS.Chapter34.Tests.VertexCoverTypedComplement
