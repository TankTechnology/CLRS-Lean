import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeed

/-!
# Recursive statements reconnected to complete label dispatch

Each program label contributes its recursively generated statement followed
immediately by the outer label-selector mux.  This module restores that exact
interleaving and proves equality with `transitionDispatchScriptFromSeed`, the
canonical complete dispatch field of one local transition.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Generic progression-controller output for one outer label mux. -/
def TransitionDispatchLabelArtifact.recursiveMuxControllerFrames
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) : List UnaryFrameSym :=
  affineStmtPhaseTagCode (.mux artifact.selector artifact.muxFrames) ++
    affineMuxInvocationProgressionFamilyFrames artifact.muxInvocationSegments

/-- When the artifact's frames are canonical, the generic mux controller
produces exactly the statement-controller encoding of its outer mux phase. -/
theorem TransitionDispatchLabelArtifact.recursiveMuxControllerFrames_eq
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm)
    (hselector : ∀ frame ∈ artifact.muxFrames,
      frame.selector = artifact.selector)
    (hfalseArm : ∀ frame ∈ artifact.muxFrames,
      frame.falseArm = frame.trueArm + 1) :
    artifact.recursiveMuxControllerFrames =
      encodeAffineStmtControllerScript
        [.mux artifact.selector artifact.muxFrames] := by
  unfold TransitionDispatchLabelArtifact.recursiveMuxControllerFrames
    TransitionDispatchLabelArtifact.muxInvocationSegments
  rw [affineMuxInvocationSingletonSegments_frames artifact.selector
    artifact.muxFrames hselector hfalseArm]
  simp [encodeAffineStmtControllerScript, encodeAffineStmtControllerPhase,
    affineStmtPhasePayload]

/-- Recursive statements and outer muxes, interleaved for a fixed label
suffix. -/
noncomputable def transitionDispatchRecursiveControllerFramesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (source : CfgWires tm (workHeight tm seed.height)) :
    TransitionAffineNat → Nat → CfgWires tm (workHeight tm seed.height) →
      List tm.Λ → List UnaryFrameSym
  | _, _, _, [] => []
  | labelOffset, start, fallback, label :: labels =>
      let statement := transitionStmtScript tm (workHeight tm seed.height)
        seed.start (seed.start + 1) start source (tm.m label)
        (stmtPushSet_program_subset tm label)
      let statementWires := transitionStmtOutputWires tm
        (workHeight tm seed.height) seed.start (seed.start + 1) start source
        (tm.m label) (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let muxStart := start + compileStmtGateCost tm
        (workHeight tm seed.height) (tm.m label)
      let artifact : TransitionDispatchLabelArtifact tm :=
        { label := label
          start := start
          statement := statement
          selector := selector
          muxFrames := affineMuxFinCanonicalFrames muxStart selector _
            (fun coordinate => statementWires
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate))
            (fun coordinate => fallback
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate)) }
      transitionStmtRecursiveControllerFrames tm seed labelOffset
          (TransitionStmtAffineContext.initial tm) (tm.m label)
          (stmtPushSet_program_subset tm label) ++
        artifact.recursiveMuxControllerFrames ++
        transitionDispatchRecursiveControllerFramesForLabels tm seed source
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm))
          (muxStart +
            (3 * cfgBitCount tm (workHeight tm seed.height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm seed.height) muxStart)
          labels

/-- Complete seed-local controller output for the entire label dispatch. -/
def transitionDispatchRecursiveControllerFramesFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  transitionDispatchRecursiveControllerFramesForLabels tm seed source
    (TransitionAffineNat.const 2) (seed.start + 2) source (programLabels tm)

/-- Label-suffix reassembly agrees with the builder-free artifact recursion. -/
theorem
    verifierTransitionDispatchRecursiveControllerFramesForLabels_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    let source := arithmeticWidenedCfgWires W.machine.tm seed.height
      seed.start seed.rowBase
    ∀ (labelOffset : TransitionAffineNat) (start : Nat)
      (fallback : CfgWires W.machine.tm
        (workHeight W.machine.tm seed.height))
      (labels : List W.machine.tm.Λ),
      start = seed.start + labelOffset.eval seed.height →
      transitionDispatchRecursiveControllerFramesForLabels W.machine.tm seed
          source labelOffset start fallback labels =
        encodeAffineStmtControllerScript
          ((transitionDispatchLabelArtifacts W.machine.tm seed.height
            seed.start (seed.start + 1) source start fallback labels).flatMap
              TransitionDispatchLabelArtifact.script) := by
  dsimp only
  intro labelOffset start fallback labels hstart
  induction labels generalizing labelOffset start fallback with
  | nil => rfl
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
      have hstatement :=
        transitionStmtRecursiveInitialControllerFrames_eq_script W input seed
          hseed labelOffset label
      rw [← hstart] at hstatement
      have hmux : artifact.recursiveMuxControllerFrames =
          encodeAffineStmtControllerScript
            [.mux artifact.selector artifact.muxFrames] := by
        apply artifact.recursiveMuxControllerFrames_eq
        · exact affineMuxFinCanonicalFrames_selector _ _ _ _ _
        · exact affineMuxFinCanonicalFrames_falseArm _ _ _ _ _
      have hheight : 0 < seed.height := by
        rw [hseed]
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
            (Nat.add_pos_left hheight
              (maxPushesPerStep W.machine.tm)),
          transitionDispatchMuxGateAffine_eval]
        simp only [muxStart]
        omega
      have htail := ih
        (((labelOffset.add
          (transitionDispatchStmtGateAffine W.machine.tm label)).add
            (transitionDispatchMuxGateAffine W.machine.tm)))
        (muxStart +
          (3 * cfgBitCount W.machine.tm
            (workHeight W.machine.tm seed.height) + 1))
        (arithmeticMuxCfgWires W.machine.tm
          (workHeight W.machine.tm seed.height) muxStart)
        hnextStart
      simp only [transitionDispatchRecursiveControllerFramesForLabels,
        transitionDispatchLabelArtifacts, List.flatMap_cons,
        TransitionDispatchLabelArtifact.script]
      change _ ++ artifact.recursiveMuxControllerFrames ++ _ = _
      rw [hstatement, hmux, htail]
      simp [encodeAffineStmtControllerScript,
        encodeAffineStmtControllerPhase, List.flatMap_append,
        List.append_assoc]
      rfl

/-- Complete seed-local dispatch closure. -/
theorem verifierTransitionDispatchRecursiveControllerFramesFromSeed_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    transitionDispatchRecursiveControllerFramesFromSeed W.machine.tm seed =
      encodeAffineStmtControllerScript
        (transitionDispatchScriptFromSeed W.machine.tm seed) := by
  unfold transitionDispatchRecursiveControllerFramesFromSeed
    transitionDispatchScriptFromSeed transitionDispatchArtifactsFromSeed
  exact
    verifierTransitionDispatchRecursiveControllerFramesForLabels_eq_script
      W input seed hseed (TransitionAffineNat.const 2) (seed.start + 2)
      (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
        seed.rowBase)
      (programLabels W.machine.tm) (by simp [TransitionAffineNat.eval_const])

/-- Row-major complete dispatch output of the recursive controllers. -/
def verifierTransitionRecursiveDispatchControllerTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchRecursiveControllerFramesFromSeed W.machine.tm)

/-- Row-major semantic encoding of every complete label dispatch. -/
def verifierTransitionRecursiveDispatchSemanticTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    encodeAffineStmtControllerScript
      (transitionDispatchScriptFromSeed W.machine.tm seed)

/-- Every statement and outer label mux of every transition row is generated
in the exact canonical order. -/
theorem verifierTransitionRecursiveDispatchControllerTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRecursiveDispatchControllerTarget W input =
      verifierTransitionRecursiveDispatchSemanticTarget W input := by
  unfold verifierTransitionRecursiveDispatchControllerTarget
    verifierTransitionRecursiveDispatchSemanticTarget
  apply List.flatMap_congr
  intro seed hseed
  apply verifierTransitionDispatchRecursiveControllerFramesFromSeed_eq_script
    W input seed
  exact verifierTransitionRowSeeds_height_eq W input seed hseed

end CLRS.Chapter34.Turing.CookLevin
