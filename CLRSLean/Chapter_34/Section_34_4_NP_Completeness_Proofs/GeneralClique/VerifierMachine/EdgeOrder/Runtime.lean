import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Run

/-!
# General CLIQUE verifier: polynomial runtime of normalized-edge checking
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

open PolyBuilder
open _root_.Turing

private theorem phaseSteps_le (phase : Phase) (input : List CliqueSym) :
    phaseSteps phase input ≤
      3 * input.length + phaseCount phase + 4 := by
  induction input generalizing phase with
  | nil =>
      cases phase <;> simp [phaseSteps, phaseCount]
  | cons symbol input ih =>
      cases phase with
      | edges =>
          have hedge := ih (Phase.left 0)
          have hrest := ih Phase.edges
          simp only [phaseCount] at hedge hrest
          cases symbol <;> simp [phaseSteps, phaseCount] <;> omega
      | left count =>
          have hsame := ih (Phase.left count)
          have htick := ih (Phase.left (count + 1))
          have hpair := ih (Phase.right count false)
          simp only [phaseCount] at hsame htick hpair
          cases symbol <;> simp [phaseSteps, phaseCount] <;> omega
      | right count exceeded =>
          have hsame := ih (Phase.right count exceeded)
          have hzero := ih (Phase.right 0 true)
          have hsucc (prior : Nat) := ih (Phase.right prior exceeded)
          have hedges := ih Phase.edges
          simp only [phaseCount] at hsame hzero hsucc hedges
          cases symbol <;> try simp [phaseSteps, phaseCount] <;> try omega
          case tick =>
            cases count with
            | zero => simp [phaseSteps, phaseCount] at hzero ⊢; omega
            | succ count =>
                have h := hsucc count
                simp [phaseSteps, phaseCount] at h ⊢
                omega
          case recordEnd =>
            cases count with
            | zero =>
                cases exceeded <;>
                  simp [phaseSteps, phaseCount] at hedges ⊢ <;> omega
            | succ count => simp [phaseSteps, phaseCount]; omega

private theorem targetFieldSteps_le (input : List CliqueSym) :
    targetFieldSteps input ≤ 3 * input.length + 4 := by
  induction input with
  | nil => simp [targetFieldSteps]
  | cons symbol input ih =>
      have hedges := phaseSteps_le Phase.edges input
      simp only [phaseCount] at hedges
      cases symbol <;> simp [targetFieldSteps] <;> omega

private theorem vertexFieldSteps_le (input : List CliqueSym) :
    vertexFieldSteps input ≤ 3 * input.length + 4 := by
  induction input with
  | nil => simp [vertexFieldSteps]
  | cons symbol input ih =>
      have htarget := targetFieldSteps_le input
      cases symbol <;> simp [vertexFieldSteps] <;> omega

private theorem instanceSteps_le (input : List CliqueSym) :
    instanceSteps input ≤ 3 * input.length + 4 := by
  cases input with
  | nil => simp [instanceSteps]
  | cons symbol input =>
      have h := vertexFieldSteps_le input
      simp [instanceSteps]
      omega

/-- Total step budget of the exact normalized-edge run. -/
def edgeOrderSteps (certificate input : List CliqueSym) : Nat :=
  certificate.length + 1 + instanceSteps input

/-- Uniform linear bound in the paired raw input length. -/
theorem edgeOrderSteps_le (certificate input : List CliqueSym) :
    edgeOrderSteps certificate input ≤
      3 * (pairEncoding certificate input).length + 4 := by
  have h := instanceSteps_le input
  simp only [edgeOrderSteps, pairEncoding, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-- The compiled controller emits its Boolean result inside the displayed
linear budget. -/
def edgeOrder_outputs_in_time (certificate input : List CliqueSym) :
    TM2OutputsInTime (compile program) (pairEncoding certificate input)
      (some (boolEncoding (edgeOrderPass certificate input)))
      (3 * (pairEncoding certificate input).length + 4) := by
  have builderRun := edgeOrder_run certificate input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (pairEncoding certificate input))
      (some (haltList (compile program) [edgeOrderPass certificate input]))
      (3 * (pairEncoding certificate input).length + 4)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (edgeOrderSteps_le certificate input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the concrete normalized-edge component. -/
noncomputable def edgeOrderPassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => edgeOrderPass pr.1 pr.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 4
  outputsFun := fun pr => by
    rcases pr with ⟨certificate, input⟩
    have run := edgeOrder_outputs_in_time certificate input
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder
