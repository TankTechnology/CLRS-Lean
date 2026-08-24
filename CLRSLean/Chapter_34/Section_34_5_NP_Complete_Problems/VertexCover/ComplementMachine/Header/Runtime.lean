import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.Header.Simulation
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# VERTEX-COVER complement header: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header

open PolyBuilder
open _root_.Turing

private theorem clearSteps_mono (edges : List CliqueSym)
    {left right original : Nat} (h : left ≤ right) :
    clearSteps edges left original ≤ clearSteps edges right original := by
  simp [clearSteps, emitSteps]
  omega

private theorem targetSteps_le (remaining original target : Nat)
    (edges : List CliqueSym) :
    targetSteps remaining original target edges ≤
      2 * target + 1 + clearSteps edges remaining original := by
  induction target generalizing remaining with
  | zero => simp [targetSteps]
  | succ target ih =>
      have hrest := ih (remaining - 1)
      have hmono : clearSteps edges (remaining - 1) original ≤
          clearSteps edges remaining original :=
        clearSteps_mono edges (Nat.sub_le remaining 1)
      simp only [targetSteps]
      omega

private theorem vertexSteps_le (remaining original vertices target : Nat)
    (edges : List CliqueSym) :
    vertexSteps remaining original vertices target edges ≤
      3 * vertices + 2 + 2 * target +
        clearSteps edges (remaining + vertices) (original + vertices) := by
  induction vertices generalizing remaining original with
  | zero =>
      have h := targetSteps_le remaining original target edges
      simp only [vertexSteps, Nat.mul_zero, Nat.add_zero]
      omega
  | succ vertices ih =>
      have h := ih (remaining + 1) (original + 1)
      simp only [vertexSteps]
      have hremaining : remaining + 1 + vertices =
          remaining + (vertices + 1) := by omega
      have horiginal : original + 1 + vertices =
          original + (vertices + 1) := by omega
      rw [hremaining, horiginal] at h
      omega

/-- The exact header run is bounded linearly by the original canonical graph
encoding. -/
theorem headerSteps_le (I : CliqueInstance) :
    headerSteps I ≤ 8 * (encodeCliqueInstance I).length + 10 := by
  let edges := I.edges.flatMap encodeCliqueEdge
  have h := vertexSteps_le 0 0 I.vertexCount I.targetSize edges
  have hlength : (encodeCliqueInstance I).length =
      I.vertexCount + I.targetSize + 3 + edges.length := by
    simp [encodeCliqueInstance, edges]
    omega
  rw [hlength]
  simp [headerSteps, clearSteps, emitSteps, edges] at h ⊢
  omega

def outputs_in_time (I : CliqueInstance) :
    TM2OutputsInTime (compile program) (encodeCliqueInstance I)
      (some (complementHeader I))
      (8 * (encodeCliqueInstance I).length + 10) := by
  have builderRun := run I
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (encodeCliqueInstance I))
      (some (haltList (compile program) (complementHeader I)))
      (8 * (encodeCliqueInstance I).length + 10)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (headerSteps_le I)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- One fixed polynomial-time TM2 computes the transformed complement header. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id complementHeader where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 8 * Polynomial.X + 10
  outputsFun := fun I => by
    have output := outputs_in_time I
    convert output using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header
