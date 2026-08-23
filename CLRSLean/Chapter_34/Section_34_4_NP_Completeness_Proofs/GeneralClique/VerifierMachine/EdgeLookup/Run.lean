import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Header

/-!
# General CLIQUE verifier: complete canonical edge lookup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

/-- Exact execution cost of a complete canonical edge-membership query. -/
def edgeLookupSteps (query : Nat × Nat) (I : CliqueInstance) : Nat :=
  headerSteps query I + edgesSteps query I.edges

/-- Exact independent-semantics run from the raw query-instance pair to edge
membership. -/
def edgeLookup_run (query : Nat × Nat) (I : CliqueInstance) :
    EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)))
      (some (haltCfg program [decide (query ∈ I.edges)]))
      (edgeLookupSteps query I) := by
  have first := header_run query I
  have first' : EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)))
      (some (cfg .edges (some (some .fieldSep)) none false
        ((I.edges.flatMap encodeCliqueEdge).map some) []
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (headerSteps query I) := by
    simpa [initialCfg, cfg, program] using first
  have second := edges_run query I.edges (some (some .fieldSep)) none false
  let full := EvalsToInTime.trans (step program)
    (headerSteps query I) (edgesSteps query I.edges) _ _ _ first' second
  simpa [edgeLookupSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using full

/-- Below the diagonal, the concrete lookup machine computes the graph's
typed adjacency predicate. -/
def edgeLookup_adjacency_run (I : CliqueInstance) {u v : Nat} (huv : u < v) :
    EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding (encodeCliqueEdge (u, v)) (encodeCliqueInstance I)))
      (some (haltCfg program [adjacencyBool I u v]))
      (edgeLookupSteps (u, v) I) := by
  simpa [adjacencyBool, huv] using edgeLookup_run (u, v) I

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
