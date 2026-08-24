import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CyclePairs.Simulation
import Mathlib.Tactic

/-!
# HAM-CYCLE consecutive-pair generator complete run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

open PolyBuilder

/-- Exact complete cost of the reverse-output controller. -/
def revSteps : List Nat → Nat
  | [] => 3
  | first :: rest =>
      2 + (3 * first + 1) + rowsStepsFrom first rest + 1 +
        (2 * CliqueInstance.lastFrom first rest + 2 * first + 5) + 1

/-- The fixed controller emits the reverse of the exact path-plus-closing
query serialization. -/
def revRun (vertices : List Nat) :
    EvalsToInTime (step revProgram)
      (initialCfg revProgram (encodeCliqueCertificate vertices))
      (some (haltCfg revProgram (encodeCyclePairs vertices).reverse))
      (revSteps vertices) := by
  cases vertices with
  | nil =>
      exact ⟨⟨3, by simp [encodeCliqueCertificate, encodeCyclePairs,
        cyclePairs, Function.iterate_succ_apply, initialCfg,
        haltCfg, flip, step, revProgram, stepOp]⟩, le_rfl⟩
  | cons first rest =>
      let remainingInput := rest.flatMap encodeCliqueVertex
      let afterStart := cfg .firstRecord (some .certificateMark) false
        (first :: rest |>.flatMap encodeCliqueVertex) [] [] [] []
      let afterMarker := cfg .loadFirst (some .vertexMark) false
        (prependCliqueTicks first (.recordEnd :: remainingInput)) [] [] [] []
      have hstart : EvalsToInTime (step revProgram)
          (initialCfg revProgram (encodeCliqueCertificate (first :: rest)))
          (some afterStart) 1 :=
        ⟨⟨1, by simp [afterStart, encodeCliqueCertificate, initialCfg,
          flip, step, revProgram, cfg, stepOp]⟩, le_rfl⟩
      have hmarker : EvalsToInTime (step revProgram) afterStart
          (some afterMarker) 1 := by
        exact ⟨⟨1, by simp [afterStart, afterMarker, remainingInput,
          encodeCliqueVertex, prependCliqueTicks_append,
          flip, step, revProgram, cfg, stepOp]⟩, le_rfl⟩
      have hfirst := loadFirstRun first remainingInput []
        (some .vertexMark) false
      have hrows := rowsRun first first rest [] []
        (some .recordEnd) false
      let pathOutput :=
        ((pathPairsFrom first rest).flatMap encodeCliqueEdge).reverse
      let last := CliqueInstance.lastFrom first rest
      have hfinishInput : EvalsToInTime (step revProgram)
          (cfg .nextRecord (some .recordEnd) false [] pathOutput
            (List.replicate first ()) (List.replicate last ()) [])
          (some (cfg .closeEdgeMark none false [] pathOutput
            (List.replicate first ()) (List.replicate last ()) [])) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hclose := closeRun first last none false [] pathOutput
      have hhalt : EvalsToInTime (step revProgram)
          (cfg .halt none false []
            ((encodeCliqueEdge (last, first)).reverse ++ pathOutput)
            [] [] [])
          (some (haltCfg revProgram
            ((encodeCliqueEdge (last, first)).reverse ++ pathOutput))) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let firstRun := EvalsToInTime.trans (step revProgram)
        1 1 _ afterStart _ hstart hmarker
      let secondRun := EvalsToInTime.trans (step revProgram)
        2 (3 * first + 1) _ afterMarker _ firstRun (by simpa using hfirst)
      let thirdRun := EvalsToInTime.trans (step revProgram)
        _ (rowsStepsFrom first rest) _ _ _ secondRun (by
          simpa [pathOutput, last, loadTest] using hrows)
      let fourthRun := EvalsToInTime.trans (step revProgram)
        _ 1 _ _ _ thirdRun hfinishInput
      let fifthRun := EvalsToInTime.trans (step revProgram)
        _ (2 * last + 2 * first + 5) _ _ _ fourthRun hclose
      let full := EvalsToInTime.trans (step revProgram)
        _ 1 _ _ _ fifthRun hhalt
      convert full using 1
      · simp [encodeCyclePairs, cyclePairs, pathOutput, last,
          List.reverse_append]
      · simp [revSteps, last]
        omega

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs
