import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchQuotedLabelProgramSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveDispatch
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Semantic closure of the quoted program-label source

The periodic selector is connected here to the artifact at the same canonical
label position.  This identifies the concrete statement/tag/mux fold with the
quotation of the established recursive dispatch controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Generic suffix invariant: if dropping `position` from the complete
artifact family yields the current arithmetic suffix, then the explicit
quoted source fold is exactly the quotation of the recursive controller fold.
-/
theorem transitionDispatchQuotedControllerRowForLabels_eq_recursive
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hheight : seed.height = (verifierHeight W).eval input.length) :
    let source := arithmeticWidenedCfgWires W.machine.tm seed.height
      seed.start seed.rowBase
    ∀ (position : Nat) (labelOffset : TransitionAffineNat) (start : Nat)
      (fallback : CfgWires W.machine.tm
        (workHeight W.machine.tm seed.height))
      (labels : List W.machine.tm.Λ),
      start = seed.start + labelOffset.eval seed.height →
      (transitionDispatchArtifactsFromSeed W.machine.tm seed).drop position =
        transitionDispatchLabelArtifacts W.machine.tm seed.height seed.start
          (seed.start + 1) source start fallback labels →
      transitionDispatchQuotedControllerRowForLabels W.machine.tm seed
          position labelOffset labels =
        quoteUnaryFrameStream
          (transitionDispatchRecursiveControllerFramesForLabels W.machine.tm
            seed source labelOffset start fallback labels) := by
  dsimp only
  intro position labelOffset start fallback labels hstart hartifacts
  induction labels generalizing position labelOffset start fallback with
  | nil =>
      simp [transitionDispatchQuotedControllerRowForLabels,
        transitionDispatchRecursiveControllerFramesForLabels,
        quoteUnaryFrameStream]
  | cons label labels ih =>
      let source := arithmeticWidenedCfgWires W.machine.tm seed.height
        seed.start seed.rowBase
      let statement := transitionStmtScript W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        start source (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label)
      let statementWires := transitionStmtOutputWires W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        start source (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label)
      let selector := source.label
        (Fin.castSucc (labelEquivFin W.machine.tm label))
      let muxStart := start + compileStmtGateCost W.machine.tm
        (workHeight W.machine.tm seed.height) (W.machine.tm.m label)
      let artifact : TransitionDispatchLabelArtifact W.machine.tm :=
        { label := label
          start := start
          statement := statement
          selector := selector
          muxFrames := affineMuxFinCanonicalFrames muxStart selector _
            (fun coordinate => statementWires
              ((cfgSlotEquivFin W.machine.tm
                (workHeight W.machine.tm seed.height)).symm coordinate))
            (fun coordinate => fallback
              ((cfgSlotEquivFin W.machine.tm
                (workHeight W.machine.tm seed.height)).symm coordinate)) }
      let tailArtifacts := transitionDispatchLabelArtifacts W.machine.tm
        seed.height seed.start (seed.start + 1) source
        (muxStart +
          (3 * cfgBitCount W.machine.tm
            (workHeight W.machine.tm seed.height) + 1))
        (arithmeticMuxCfgWires W.machine.tm
          (workHeight W.machine.tm seed.height) muxStart) labels
      have hartifacts' :
          (transitionDispatchArtifactsFromSeed W.machine.tm seed).drop
              position = artifact :: tailArtifacts := by
        simpa only [transitionDispatchLabelArtifacts] using hartifacts
      have hartifactDrop : artifact ∈
          (transitionDispatchArtifactsFromSeed W.machine.tm seed).drop
            position := by
        rw [hartifacts']
        exact List.mem_cons_self
      have hartifact : artifact ∈
          transitionDispatchArtifactsFromSeed W.machine.tm seed :=
        List.mem_of_mem_drop hartifactDrop
      have hposition : position <
          (transitionDispatchArtifactsFromSeed W.machine.tm seed).length := by
        have hpositive := List.length_pos_of_mem hartifactDrop
        rw [List.length_drop] at hpositive
        omega
      have hget :
          (transitionDispatchArtifactsFromSeed W.machine.tm seed)[position] =
            artifact := by
        have hcanonical := List.drop_eq_getElem_cons
          (l := transitionDispatchArtifactsFromSeed W.machine.tm seed)
          hposition
        rw [hartifacts'] at hcanonical
        exact (List.cons.inj hcanonical).1.symm
      have hselected :
          (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm seed).getD
              position [] =
            quoteUnaryFrameStream artifact.muxInvocationView.encode := by
        unfold transitionDispatchQuotedMuxRowsFromSeed
        rw [List.getD_eq_getElem _ _ (by simpa using hposition)]
        simp only [List.getElem_map]
        rw [hget]
      have htailArtifacts :
          (transitionDispatchArtifactsFromSeed W.machine.tm seed).drop
              (position + 1) = tailArtifacts := by
        have hdrop := congrArg (List.drop 1) hartifacts'
        simpa [List.drop_drop, Nat.add_comm] using hdrop
      have hstatement :=
        transitionStmtRecursiveInitialControllerFrames_eq_script W input seed
          hheight labelOffset label
      rw [← hstart] at hstatement
      have hview :=
        transitionDispatchArtifactsFromSeed_muxInvocationView_encode
          W.machine.tm seed artifact hartifact
      have hmux : artifact.recursiveMuxControllerFrames =
          encodeAffineStmtControllerScript
            [.mux artifact.selector artifact.muxFrames] := by
        apply artifact.recursiveMuxControllerFrames_eq
        · exact affineMuxFinCanonicalFrames_selector _ _ _ _ _
        · exact affineMuxFinCanonicalFrames_falseArm _ _ _ _ _
      have hmuxQuoted :
          quoteUnaryFrameStream (transitionStmtPhaseKindTagCode .mux) ++
              quoteUnaryFrameStream artifact.muxInvocationView.encode =
            quoteUnaryFrameStream artifact.recursiveMuxControllerFrames := by
        rw [hview, hmux]
        simp [encodeAffineStmtControllerScript,
          encodeAffineStmtControllerPhase, affineStmtPhasePayload,
          transitionStmtPhaseKindTagCode, affineStmtPhaseTagCode,
          quoteUnaryFrameStream]
      have hheightPos : 0 < seed.height := by
        rw [hheight]
        exact verifierHeight_eval_pos W input.length
      have hnextStart :
          muxStart +
              (3 * cfgBitCount W.machine.tm
                (workHeight W.machine.tm seed.height) + 1) =
            seed.start +
              (((labelOffset.add
                (transitionDispatchStmtGateAffine W.machine.tm label)).add
                  (transitionDispatchMuxGateAffine W.machine.tm)).eval
                    seed.height) := by
        rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_add,
          transitionDispatchStmtGateAffine_eval W.machine.tm label
            seed.height
            (Nat.add_pos_left hheightPos
              (maxPushesPerStep W.machine.tm)),
          transitionDispatchMuxGateAffine_eval]
        simp only [muxStart]
        omega
      have htail := ih (position + 1)
        (((labelOffset.add
          (transitionDispatchStmtGateAffine W.machine.tm label)).add
            (transitionDispatchMuxGateAffine W.machine.tm)))
        (muxStart +
          (3 * cfgBitCount W.machine.tm
            (workHeight W.machine.tm seed.height) + 1))
        (arithmeticMuxCfgWires W.machine.tm
          (workHeight W.machine.tm seed.height) muxStart)
        hnextStart htailArtifacts
      simp only [transitionDispatchQuotedControllerRowForLabels,
        transitionDispatchRecursiveControllerFramesForLabels]
      change quoteUnaryFrameStream _ ++
          quoteUnaryFrameStream (transitionStmtPhaseKindTagCode .mux) ++
            (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm seed).getD
                position [] ++ _ =
        quoteUnaryFrameStream (_ ++ artifact.recursiveMuxControllerFrames ++ _)
      rw [hselected, htail, ← hstart]
      have hprefix :
          quoteUnaryFrameStream
                (encodeAffineStmtControllerScript statement) ++
              quoteUnaryFrameStream
                (transitionStmtPhaseKindTagCode .mux) ++
            quoteUnaryFrameStream artifact.muxInvocationView.encode =
          quoteUnaryFrameStream
            (transitionStmtRecursiveControllerFrames W.machine.tm seed
                labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
                (W.machine.tm.m label)
                (stmtPushSet_program_subset W.machine.tm label) ++
              artifact.recursiveMuxControllerFrames) := by
        rw [← hstatement, List.append_assoc, hmuxQuoted]
        simp [quoteUnaryFrameStream, List.flatMap_append]
      rw [hprefix]
      simp [quoteUnaryFrameStream, List.flatMap_append, List.append_assoc,
        muxStart]

/-- At the initial label position, the explicit quoted program fold is the
quotation of the complete recursive dispatch controller. -/
theorem transitionDispatchQuotedControllerRow_eq_recursive
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    transitionDispatchQuotedControllerRowForLabels W.machine.tm seed 0
        (TransitionAffineNat.const 2) (programLabels W.machine.tm) =
      quoteUnaryFrameStream
        (transitionDispatchRecursiveControllerFramesFromSeed W.machine.tm
          seed) := by
  unfold transitionDispatchRecursiveControllerFramesFromSeed
  apply transitionDispatchQuotedControllerRowForLabels_eq_recursive W input
    seed (verifierTransitionRowSeeds_height_eq W input seed hseed) 0
      (TransitionAffineNat.const 2) (seed.start + 2)
      (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
        seed.rowBase) (programLabels W.machine.tm)
  · simp [TransitionAffineNat.eval_const]
  · rfl

/-- The concrete complete dispatch source emits exactly the quotation of the
canonical recursive dispatch controller on every transition seed. -/
theorem verifierTransitionDispatchQuotedSeedRowSource_row_eq_recursive
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionDispatchQuotedSeedRowSource W).row seed =
      quoteUnaryFrameStream
        (transitionDispatchRecursiveControllerFramesFromSeed W.machine.tm
          seed) := by
  rw [verifierTransitionDispatchQuotedSeedRowSource_row_eq W input seed
    hseed]
  exact transitionDispatchQuotedControllerRow_eq_recursive W input seed hseed

/-- Textbook-facing form: each physical row is the quotation of the exact
canonical dispatch statement script. -/
theorem verifierTransitionDispatchQuotedSeedRowSource_row_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionDispatchQuotedSeedRowSource W).row seed =
      quoteUnaryFrameStream
        (encodeAffineStmtControllerScript
          (transitionDispatchScriptFromSeed W.machine.tm seed)) := by
  rw [verifierTransitionDispatchQuotedSeedRowSource_row_eq_recursive W input
    seed hseed]
  rw [verifierTransitionDispatchRecursiveControllerFramesFromSeed_eq_script
    W input seed (verifierTransitionRowSeeds_height_eq W input seed hseed)]

end CLRS.Chapter34.Turing.CookLevin
