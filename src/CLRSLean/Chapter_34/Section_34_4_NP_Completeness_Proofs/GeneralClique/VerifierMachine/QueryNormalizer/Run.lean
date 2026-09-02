import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Simulation

/-!
# Query normalization: complete stream run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

open PolyBuilder

/-- Exact accumulated row cost. -/
def rowsSteps (edges : List (Nat × Nat)) : Nat :=
  (edges.map rowSteps).sum

/-- Every canonical query record is normalized while later output continues
to accumulate on the left of the output stack. -/
def rowsRun (edges : List (Nat × Nat)) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step revProgram)
        (cfg .scan buffer test
          (edges.flatMap encodeCliqueEdge ++ tail) output [] [] [])
        (some (cfg .scan finalBuffer finalTest tail
          ((encodeNormalizedQueries edges).reverse ++ output) [] [] []))
        (rowsSteps edges) := by
  induction edges generalizing output buffer test with
  | nil =>
      refine ⟨buffer, test, ?_⟩
      exact ⟨⟨0, by simp [encodeNormalizedQueries, cfg]⟩, le_rfl⟩
  | cons edge edges ih =>
      let remaining := edges.flatMap encodeCliqueEdge ++ tail
      have first := rowRun edge remaining output buffer test
      rcases ih
          ((encodeCliqueEdge (normalizeQuery edge)).reverse ++ output)
          (some .recordEnd) false with
        ⟨finalBuffer, finalTest, rest⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans (step revProgram)
        (rowSteps edge) (rowsSteps edges) _ _ _ first rest
      simpa [remaining, rowsSteps, encodeNormalizedQueries,
        Function.comp_def, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Total reverse-output cost, including empty-input detection and halt. -/
def revSteps (edges : List (Nat × Nat)) : Nat :=
  rowsSteps edges + 2

/-- The fixed controller normalizes a complete canonical query stream and
halts with all non-output stacks empty. -/
def revRun (edges : List (Nat × Nat)) :
    EvalsToInTime (step revProgram)
      (initialCfg revProgram (edges.flatMap encodeCliqueEdge))
      (some (haltCfg revProgram (encodeNormalizedQueries edges).reverse))
      (revSteps edges) := by
  change EvalsToInTime (step revProgram)
    (cfg .scan none false (edges.flatMap encodeCliqueEdge) [] [] [] [])
    (some (haltCfg revProgram (encodeNormalizedQueries edges).reverse))
    (rowsSteps edges + 2)
  rcases rowsRun edges [] [] none false with
    ⟨finalBuffer, finalTest, rows⟩
  have stop : EvalsToInTime (step revProgram)
      (cfg .scan finalBuffer finalTest []
        (encodeNormalizedQueries edges).reverse [] [] [])
      (some (cfg .halt none finalTest []
        (encodeNormalizedQueries edges).reverse [] [] [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have halt : EvalsToInTime (step revProgram)
      (cfg .halt none finalTest []
        (encodeNormalizedQueries edges).reverse [] [] [])
      (some (haltCfg revProgram (encodeNormalizedQueries edges).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let stopped := EvalsToInTime.trans (step revProgram)
    (rowsSteps edges) 1 _ _ _ (by
      simpa [initialCfg, cfg, revProgram] using rows) stop
  let full := EvalsToInTime.trans (step revProgram)
    _ 1 _ _ _ stopped halt
  convert full using 1
  · rfl
  · omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
