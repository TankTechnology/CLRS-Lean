import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerBounds

/-!
# Polynomial-time mux invocation expansion

This file compiles the verified fixed controller to TM2, applies the quadratic
source-length bound, and composes it with the existing list reverser to expose
the forward mux invocation stream.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Full builder execution through the actual halt configuration. -/
def affineMuxInvocationProgressionControllerRev_haltRun
    (segments : List AffineMuxInvocationProgression) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (initialCfg affineMuxInvocationProgressionControllerRevProgram
        (affineMuxInvocationProgressionFamilySourceFrames segments))
      (some (haltCfg affineMuxInvocationProgressionControllerRevProgram
        (affineMuxInvocationProgressionFamilyFrames segments).reverse))
      (affineMuxInvocationProgressionControllerFamilySteps segments + 2) := by
  have body := affineMuxInvocationProgressionControllerRev_run segments
  have haltStep : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerFinishCfg
        (affineMuxInvocationProgressionFamilyFrames segments).reverse)
      (some (haltCfg affineMuxInvocationProgressionControllerRevProgram
        (affineMuxInvocationProgressionFamilyFrames segments).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (affineMuxInvocationProgressionControllerFamilySteps segments + 1) 1
    _ _ _ body haltStep
  convert full using 1
  omega

/-- Compiled fixed TM2 for the reversed complete mux invocation stream. -/
noncomputable def
    affineMuxInvocationProgressionFamilyFramesRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      affineMuxInvocationProgressionFamilySourceFrames id
      (fun segments =>
        (affineMuxInvocationProgressionFamilyFrames segments).reverse) where
  tm := compile affineMuxInvocationProgressionControllerRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 100 * Polynomial.X ^ 2 + 2
  outputsFun := fun segments => by
    have builderRun :=
      affineMuxInvocationProgressionControllerRev_haltRun segments
    have compiledRun := compile_evalsToInTime
      affineMuxInvocationProgressionControllerRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineMuxInvocationProgressionControllerRevProgram).step
        (_root_.Turing.initList
          (compile affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionFamilySourceFrames segments))
        (some (_root_.Turing.haltList
          (compile affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionFamilyFrames segments).reverse))
        (affineMuxInvocationProgressionControllerFamilySteps segments + 2) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        affineMuxInvocationProgressionControllerFamilySteps segments + 2 ≤
          (100 * Polynomial.X ^ 2 + 2).eval
            (affineMuxInvocationProgressionFamilySourceFrames segments).length := by
      have hbound :=
        affineMuxInvocationProgressionControllerFamilySteps_le segments
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineMuxInvocationProgressionControllerRevProgram).step
        (_root_.Turing.initList
          (compile affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionFamilySourceFrames segments))
        (some (_root_.Turing.haltList
          (compile affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionFamilyFrames segments).reverse))
        ((100 * Polynomial.X ^ 2 + 2).eval
          (affineMuxInvocationProgressionFamilySourceFrames segments).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward complete mux invocation source, obtained by reversing the verified
stack-oriented controller output with the existing polynomial-time reverser.
-/
noncomputable def
    affineMuxInvocationProgressionFamilyFrames_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      affineMuxInvocationProgressionFamilySourceFrames id
      affineMuxInvocationProgressionFamilyFrames := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineMuxInvocationProgressionFamilyFramesRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
