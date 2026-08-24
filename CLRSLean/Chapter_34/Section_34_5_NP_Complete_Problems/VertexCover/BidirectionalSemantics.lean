import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseCompleteness

/-!
# Bidirectional complement semantics for CLIQUE and VERTEX-COVER

For a well-formed graph-plus-target instance, the deterministic complement
construction translates the decision predicates exactly in either direction.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- A well-formed instance has a cover of size at most `k` exactly when its
complement has a clique of size `|V| - k`. -/
theorem hasVertexCover_iff_complement_hasClique {I : CliqueInstance}
    (hI : I.WellFormed) :
    I.HasVertexCover ↔ I.complementForVertexCover.HasClique := by
  constructor
  · exact complement_hasClique_of_hasVertexCover
  · exact hasVertexCover_of_complement_hasClique hI

end CliqueInstance
end Chapter34
end CLRS
