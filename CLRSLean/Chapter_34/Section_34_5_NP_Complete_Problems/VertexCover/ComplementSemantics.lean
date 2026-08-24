import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Completeness

/-!
# Textbook CLIQUE-to-VERTEX-COVER semantic equivalence

This module exposes the typed semantic theorem for the standard complement
reduction.  The construction and the two proof directions live in smaller
modules so that difficult proofs can be compiled independently.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- For a well-formed graph-plus-target instance, a clique of size `k` exists
exactly when the complemented graph has a vertex cover of size at most
`|V| - k`. -/
theorem hasClique_iff_complement_hasVertexCover {I : CliqueInstance}
    (hI : I.WellFormed) :
    I.HasClique ↔ I.complementForVertexCover.HasVertexCover := by
  constructor
  · exact complement_hasVertexCover_of_hasClique
  · exact hasClique_of_complement_hasVertexCover hI

end CliqueInstance
end Chapter34
end CLRS
