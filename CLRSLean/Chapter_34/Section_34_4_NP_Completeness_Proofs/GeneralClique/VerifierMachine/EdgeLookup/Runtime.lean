import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Run

/-!
# General CLIQUE verifier: polynomial runtime of edge lookup
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder
open _root_.Turing

private theorem leftFieldSteps_le (remaining saved candidate : Nat) :
    leftFieldSteps remaining saved candidate ≤
      4 * (remaining + saved + candidate) + 3 := by
  induction candidate generalizing remaining saved with
  | zero => simp [leftFieldSteps]; omega
  | succ candidate ih =>
      cases remaining with
      | zero =>
          have h := ih 0 saved
          simp [leftFieldSteps] at h ⊢
          omega
      | succ remaining =>
          have h := ih remaining (saved + 1)
          simp [leftFieldSteps] at h ⊢
          omega

private theorem rightFieldSteps_le (remaining saved candidate : Nat) :
    rightFieldSteps remaining saved candidate ≤
      4 * (remaining + saved + candidate) + 3 := by
  induction candidate generalizing remaining saved with
  | zero => simp [rightFieldSteps]; omega
  | succ candidate ih =>
      cases remaining with
      | zero =>
          have h := ih 0 saved
          simp [rightFieldSteps] at h ⊢
          omega
      | succ remaining =>
          have h := ih remaining (saved + 1)
          simp [rightFieldSteps] at h ⊢
          omega

private theorem edge_count_le_encoding_length (edges : List (Nat × Nat)) :
    edges.length ≤ (edges.flatMap encodeCliqueEdge).length := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        encodeCliqueEdge_length]
      omega

private theorem edgesSteps_le_of_bound (query : Nat × Nat)
    (edges : List (Nat × Nat)) (bound : Nat)
    (hquery : query.1 + query.2 ≤ bound)
    (hedges : (edges.flatMap encodeCliqueEdge).length ≤ bound) :
    edgesSteps query edges ≤
      (9 * bound + 10) * (edges.length + 1) + bound + 7 := by
  induction edges with
  | nil => simp [edgesSteps]; omega
  | cons edge edges ih =>
      have hleft := leftFieldSteps_le query.1 0 edge.1
      have hright := rightFieldSteps_le query.2 0 edge.2
      have htail : (edges.flatMap encodeCliqueEdge).length ≤ bound := by
        simp only [List.flatMap_cons, List.length_append,
          encodeCliqueEdge_length] at hedges
        omega
      have hedge : edge.1 + edge.2 ≤ bound := by
        simp only [List.flatMap_cons, List.length_append,
          encodeCliqueEdge_length] at hedges
        omega
      have hrec := ih htail
      cases hmatch : edgeMatches query edge with
      | false =>
          simp only [edgesSteps, hmatch, Bool.false_eq_true, ↓reduceIte,
            List.length_cons]
          simp only [Nat.mul_succ] at hrec ⊢
          omega
      | true =>
          have htailLength :
              (edges.flatMap encodeCliqueEdge).length ≤ bound := htail
          simp only [edgesSteps, hmatch, ↓reduceIte, List.length_cons]
          simp only [Nat.mul_succ]
          nlinarith

/-- The exact lookup execution is bounded by one fixed quadratic polynomial
in the complete paired input length. -/
theorem edgeLookupSteps_le (query : Nat × Nat) (I : CliqueInstance) :
    edgeLookupSteps query I ≤
      20 * (pairEncoding (encodeCliqueEdge query)
        (encodeCliqueInstance I)).length.succ ^ 2 := by
  let inputLength :=
    (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)).length
  have hquery : query.1 + query.2 ≤ inputLength := by
    simp [inputLength, pairEncoding, encodeCliqueEdge,
      encodeCliqueInstance]
    omega
  have hedges : (I.edges.flatMap encodeCliqueEdge).length ≤ inputLength := by
    simp [inputLength, pairEncoding, encodeCliqueEdge,
      encodeCliqueInstance]
    omega
  have hedgesRun := edgesSteps_le_of_bound query I.edges inputLength
    hquery hedges
  have hedgeCount : I.edges.length ≤ inputLength :=
    (edge_count_le_encoding_length I.edges).trans hedges
  have hmul :
      (9 * inputLength + 10) * (I.edges.length + 1) ≤
        (9 * inputLength + 10) * (inputLength + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hedgeCount 1)
  have hheader : headerSteps query I ≤ 2 * inputLength := by
    simp [headerSteps, inputLength, pairEncoding, encodeCliqueEdge,
      encodeCliqueInstance]
    omega
  have hcombined : edgeLookupSteps query I ≤
      2 * inputLength +
        ((9 * inputLength + 10) * (inputLength + 1) + inputLength + 7) := by
    exact Nat.add_le_add hheader (hedgesRun.trans
      (Nat.add_le_add_right hmul (inputLength + 7)))
  change edgeLookupSteps query I ≤ 20 * inputLength.succ ^ 2
  nlinarith

/-- The compiled fixed controller emits edge membership within the displayed
quadratic budget. -/
def edgeLookup_outputs_in_time (query : Nat × Nat) (I : CliqueInstance) :
    TM2OutputsInTime (compile program)
      (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I))
      (some (boolEncoding (decide (query ∈ I.edges))))
      (20 * (pairEncoding (encodeCliqueEdge query)
        (encodeCliqueInstance I)).length.succ ^ 2) := by
  have builderRun := edgeLookup_run query I
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program)
        (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)))
      (some (haltList (compile program) [decide (query ∈ I.edges)]))
      (20 * (pairEncoding (encodeCliqueEdge query)
        (encodeCliqueInstance I)).length.succ ^ 2)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (edgeLookupSteps_le query I)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the reusable concrete edge lookup. -/
noncomputable def edgeLookupComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : (Nat × Nat) × CliqueInstance =>
        pairEncoding (encodeCliqueEdge pr.1) (encodeCliqueInstance pr.2))
      boolEncoding (fun pr => decide (pr.1 ∈ pr.2.edges)) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun := fun pr => by
    rcases pr with ⟨query, I⟩
    have run := edgeLookup_outputs_in_time query I
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.succ_eq_add_one]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
