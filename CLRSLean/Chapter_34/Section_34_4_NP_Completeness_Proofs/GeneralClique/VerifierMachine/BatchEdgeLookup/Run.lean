import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Load

/-!
# Batch edge lookup: complete execution

This file closes the operational proof for the fixed batch controller.  The
query stream is loaded once, every query is checked against the same restored
graph, and the conjunction of the answers is emitted.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Stack layout used by the repeated-query loop.  Records and the order of
records are both reversed because the work tape is used as a stack. -/
def encodeQueryWork (queries : List (Nat × Nat)) : List (Option CliqueSym) :=
  queries.flatMap fun query => ((encodeCliqueEdge query).map some).reverse

theorem encodeQueryWork_append (left right : List (Nat × Nat)) :
    encodeQueryWork (left ++ right) =
      encodeQueryWork left ++ encodeQueryWork right := by
  simp [encodeQueryWork, List.flatMap_append]

theorem encodeQueryWork_reverse (queries : List (Nat × Nat)) :
    encodeQueryWork queries.reverse =
      ((queries.flatMap encodeCliqueEdge).map some).reverse := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rw [List.reverse_cons, encodeQueryWork_append, ih]
      simp [encodeQueryWork, List.map_append, List.reverse_append]

/-- Exact accumulated cost after all queries have already been loaded. -/
def iterationsSteps : List (Nat × Nat) → CliqueInstance → Nat
  | [], I => (encodeCliqueInstance I).length + 9
  | query :: queries, I =>
      iterationSteps query I + iterationsSteps queries I

/-- Execute every query currently present on the query stack. -/
def iterations_run (aggregate : Bool) (queries : List (Nat × Nat))
    (I : CliqueInstance) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextQuery aggregate) buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) []
        (encodeQueryWork queries) [] [] [] [])
      (some (haltCfg program
        [aggregate && queriesInEdgesBool I queries]))
      (iterationsSteps queries I) := by
  induction queries generalizing aggregate buffer₁ buffer₂ test with
  | nil =>
      simpa [encodeQueryWork, iterationsSteps, queriesInEdgesBool] using
        final_run aggregate ((encodeCliqueInstance I).map some)
          buffer₁ buffer₂ test
  | cons query queries ih =>
      have first := iteration_run aggregate query (encodeQueryWork queries) I
        buffer₁ buffer₂ test
      have rest := ih
        (aggregate := aggregate && decide (query ∈ I.edges))
        (buffer₁ := some (some CliqueSym.edgeMark))
        (buffer₂ := none) (test := false)
      let full := EvalsToInTime.trans (step program)
        (iterationSteps query I) (iterationsSteps queries I)
        _ _ _ first rest
      simpa [encodeQueryWork, iterationsSteps, queriesInEdgesBool,
        Bool.and_assoc, Nat.add_assoc, Nat.add_comm] using full

/-- Exact cost of the full fixed batch edge lookup. -/
def batchSteps (queries : List (Nat × Nat)) (I : CliqueInstance) : Nat :=
  loadSteps queries + iterationsSteps queries.reverse I

/-- The fixed machine decides whether every supplied canonical query occurs in
the serialized edge table. -/
def batch_run (queries : List (Nat × Nat)) (I : CliqueInstance) :
    EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding (queries.flatMap encodeCliqueEdge)
          (encodeCliqueInstance I)))
      (some (haltCfg program [queriesInEdgesBool I queries]))
      (batchSteps queries I) := by
  have loaded := load_run queries I
  have repeated := iterations_run true queries.reverse I
    (some none) none false
  rw [encodeQueryWork_reverse] at repeated
  let full := EvalsToInTime.trans (step program)
    (loadSteps queries) (iterationsSteps queries.reverse I)
    _ _ _ loaded repeated
  simpa [batchSteps, queriesInEdgesBool, Bool.and_assoc,
    Nat.add_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
