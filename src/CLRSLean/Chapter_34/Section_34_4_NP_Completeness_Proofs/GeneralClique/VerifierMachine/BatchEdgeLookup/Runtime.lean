import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Run
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.HeadProjection

/-!
# Batch edge lookup: polynomial runtime

The same graph is restored after each query, so the natural uniform bound is
cubic: at most linearly many encoded queries, each performing a quadratic
edge-table scan.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder
open _root_.Turing

private theorem edgesSteps_le_edgeLookup (query : Nat × Nat)
    (edges : List (Nat × Nat)) :
    edgesSteps query edges ≤ EdgeLookup.edgesSteps query edges := by
  induction edges with
  | nil => simp [edgesSteps, EdgeLookup.edgesSteps]
  | cons edge edges ih =>
      cases hmatch : EdgeLookup.edgeMatches query edge
      · simp [edgesSteps, EdgeLookup.edgesSteps, hmatch, ih]
      · simp [edgesSteps, EdgeLookup.edgesSteps, hmatch]
        omega

private theorem iterationSteps_le_of_bound (query : Nat × Nat)
    (I : CliqueInstance) (bound : Nat)
    (hbound :
      (encodeCliqueEdge query).length +
          (encodeCliqueInstance I).length + 1 ≤ bound) :
    iterationSteps query I ≤ 25 * bound.succ ^ 2 := by
  let pairLength :=
    (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)).length
  have hpair : pairLength ≤ bound := by
    simpa [pairLength, pairEncoding, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hbound
  have hedgeLookup := EdgeLookup.edgeLookupSteps_le query I
  have hedgeLookupBound : EdgeLookup.edgeLookupSteps query I ≤
      20 * bound.succ ^ 2 := by
    have hsquare : pairLength.succ ^ 2 ≤ bound.succ ^ 2 := by
      exact Nat.pow_le_pow_left (Nat.succ_le_succ hpair) 2
    exact hedgeLookup.trans (Nat.mul_le_mul_left 20 hsquare)
  have hedges : edgesSteps query I.edges ≤
      EdgeLookup.edgeLookupSteps query I := by
    exact (edgesSteps_le_edgeLookup query I.edges).trans
      (Nat.le_add_left _ _)
  have hrecord : query.1 + query.2 + 3 ≤ bound := by
    simp only [encodeCliqueEdge_length] at hbound
    omega
  have hgraph : (encodeCliqueInstance I).length ≤ bound := by
    omega
  have hheader : headerSteps I ≤ (encodeCliqueInstance I).length := by
    simp [headerSteps, encodeCliqueInstance]
    omega
  unfold iterationSteps querySteps
  nlinarith

private theorem iterationsSteps_le_of_bound (queries : List (Nat × Nat))
    (I : CliqueInstance) (bound : Nat)
    (hbound :
      (queries.flatMap encodeCliqueEdge).length +
          (encodeCliqueInstance I).length + 1 ≤ bound) :
    iterationsSteps queries I ≤
      25 * queries.length * bound.succ ^ 2 +
        (encodeCliqueInstance I).length + 9 := by
  induction queries with
  | nil => simp [iterationsSteps]
  | cons query queries ih =>
      have htail :
          (queries.flatMap encodeCliqueEdge).length +
              (encodeCliqueInstance I).length + 1 ≤ bound := by
        simp only [List.flatMap_cons, List.length_append] at hbound
        omega
      have hquery :
          (encodeCliqueEdge query).length +
              (encodeCliqueInstance I).length + 1 ≤ bound := by
        simp only [List.flatMap_cons, List.length_append] at hbound
        omega
      have hiteration := iterationSteps_le_of_bound query I bound hquery
      have hrest := ih htail
      simp only [iterationsSteps, List.length_cons]
      nlinarith

private theorem queryCount_le_stream (queries : List (Nat × Nat)) :
    queries.length ≤ (queries.flatMap encodeCliqueEdge).length := by
  induction queries with
  | nil => simp
  | cons query queries ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        encodeCliqueEdge_length]
      omega

/-- The exact full execution is bounded by one fixed cubic polynomial in the
paired input length. -/
theorem batchSteps_le (queries : List (Nat × Nat)) (I : CliqueInstance) :
    batchSteps queries I ≤
      40 * (pairEncoding (queries.flatMap encodeCliqueEdge)
        (encodeCliqueInstance I)).length.succ ^ 3 := by
  let queryLength := (queries.flatMap encodeCliqueEdge).length
  let graphLength := (encodeCliqueInstance I).length
  let inputLength :=
    (pairEncoding (queries.flatMap encodeCliqueEdge)
      (encodeCliqueInstance I)).length
  have hinput : queryLength + graphLength + 1 = inputLength := by
    simp [queryLength, graphLength, inputLength, pairEncoding,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hiterations := iterationsSteps_le_of_bound queries.reverse I
    inputLength
  have hreverse :
      (queries.reverse.flatMap encodeCliqueEdge).length = queryLength := by
    simp [queryLength]
  have hbound :
      (queries.reverse.flatMap encodeCliqueEdge).length +
          graphLength + 1 ≤ inputLength := by
    rw [hreverse, hinput]
  specialize hiterations hbound
  have hcount := queryCount_le_stream queries
  have hcountReverse : queries.reverse.length ≤ queryLength := by
    simpa [queryLength] using hcount
  have hquery : queryLength ≤ inputLength := by omega
  have hgraph : graphLength ≤ inputLength := by omega
  unfold batchSteps loadSteps
  change queryLength + 2 + iterationsSteps queries.reverse I ≤ _
  nlinarith

/-- The compiled fixed controller emits the aggregate followed by every
pointwise membership answer within the displayed cubic budget. -/
def batchResults_outputs_in_time (queries : List (Nat × Nat))
    (I : CliqueInstance) :
    TM2OutputsInTime (compile program)
      (pairEncoding (queries.flatMap encodeCliqueEdge)
        (encodeCliqueInstance I))
      (some (batchResultStream I queries))
      (40 * (pairEncoding (queries.flatMap encodeCliqueEdge)
        (encodeCliqueInstance I)).length.succ ^ 3) := by
  have builderRun := batch_run queries I
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program)
        (pairEncoding (queries.flatMap encodeCliqueEdge)
          (encodeCliqueInstance I)))
      (some (haltList (compile program) (batchResultStream I queries)))
      (40 * (pairEncoding (queries.flatMap encodeCliqueEdge)
        (encodeCliqueInstance I)).length.succ ^ 3)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (batchSteps_le queries I)⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- Polynomial-time computability of the enriched reusable batch lookup. -/
noncomputable def batchResultsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (pr.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance pr.2))
      id (fun pr => batchResultStream pr.2 pr.1) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 40 * (Polynomial.X + 1) ^ 3
  outputsFun := fun pr => by
    rcases pr with ⟨queries, I⟩
    have run := batchResults_outputs_in_time queries I
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.succ_eq_add_one]
    all_goals
      change List.map id _ = _
      exact List.map_id _

/-- Polynomial-time computability of the original aggregate-only interface. -/
noncomputable def batchComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (pr.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance pr.2))
      boolEncoding (fun pr => queriesInEdgesBool pr.2 pr.1) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchResultsComputableInPolyTime HeadProjection.computableInPolyTime
  have machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun pr => by
        have output := machine.outputsFun pr
        convert output using 1 <;>
          simp [Function.comp_def, batchResultStream, HeadProjection.stream,
            _root_.Turing.TM2Comp.boolEncoding] }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
