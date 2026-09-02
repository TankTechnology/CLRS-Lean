import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementDescriptorSeedSources
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDelimiterMap

/-!
# Delimiter-exact controller source for fixed affine statement heads

The numeric head descriptor carries one marked row per transition seed.  For
a nonempty fixed phase table, a cyclic delimiter pass materializes the exact
tagged statement-controller frames and preserves the outer row marker.  The
empty table used by `halt` already consists solely of those outer markers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Delimiter-exact affine-head controller frames, retaining one additional
outer marker after each complete seed-local head. -/
noncomputable def verifierTransitionAffineHeadControllerMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) : List UnaryFrameSym :=
  if hphases : phases = [] then
    encodeUnaryFrameMarkedRowFamily
      (verifierTransitionAffineFormDescriptorFamily W [] input)
  else
    rewriteUnaryFrameDelimiters
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
      (encodeUnaryFrameMarkedRowFamily
        (verifierTransitionAffineFormDescriptorFamily W
          (transitionAffineStmtScriptFieldForms phases) input))

/-- Exact seed-major semantics of affine-head delimiter materialization. -/
theorem verifierTransitionAffineHeadControllerMarkedFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) :
    verifierTransitionAffineHeadControllerMarkedFrames W phases input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionStmtAffineFormsControllerFrames seed phases ++
          [.frameEnd] := by
  by_cases hphases : phases = []
  · subst phases
    unfold verifierTransitionAffineHeadControllerMarkedFrames
      verifierTransitionAffineFormDescriptorFamily
      encodeUnaryFrameMarkedRowFamily
      transitionStmtAffineFormsControllerFrames
    simp only [dite_true]
    rw [List.flatMap_map]
    generalize verifierTransitionRowSeeds W input = seeds
    induction seeds with
    | nil => rfl
    | cons seed seeds ih =>
        have htail :
            (seeds.flatMap fun seed =>
                encodeUnaryFrame
                    (affineUnaryTripleMap []
                      (transitionTailAffineSeed seed)) ++
                  [.frameEnd]) =
              (seeds.flatMap fun seed =>
                encodeAffineStmtControllerScript [] ++
                  [.frameEnd]) := by
          exact ih
        simpa [affineUnaryTripleMap, encodeUnaryFrame,
          encodeAffineStmtControllerScript] using
            congrArg (List.cons UnaryFrameSym.frameEnd) htail
  · rw [verifierTransitionAffineHeadControllerMarkedFrames]
    simp only [hphases, ↓reduceDIte]
    let rows := (verifierTransitionRowSeeds W input).map fun seed =>
      affineUnaryTripleMap
        (transitionAffineStmtScriptFieldForms phases)
        (transitionTailAffineSeed seed)
    have hlength : ∀ row ∈ rows,
        row.length =
          (transitionAffineStmtScriptDelimiters phases).length := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simpa [affineUnaryTripleMap] using
        transitionAffineStmtScript_lengths phases
    have hrewrite := rewriteUnaryFrameDelimiters_markedRows
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
      rows hlength
    have hinput :
        encodeUnaryFrameMarkedRowFamily
            (verifierTransitionAffineFormDescriptorFamily W
              (transitionAffineStmtScriptFieldForms phases) input) =
          rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd] := by
      unfold encodeUnaryFrameMarkedRowFamily
        verifierTransitionAffineFormDescriptorFamily
      simp [rows, List.flatMap_map]
    rw [hinput, hrewrite]
    unfold rows
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [transitionAffineStmtScriptForms_fixed_encoding]
    rfl

/-- Concrete polynomial-time TM2 for every fixed affine head, including the
empty `halt` head. -/
noncomputable def
    verifierTransitionAffineHeadControllerMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineHeadControllerMarkedFrames W phases) := by
  by_cases hphases : phases = []
  · subst phases
    let source :=
      verifierTransitionAffineFormDescriptorFamilyTotal_computableInPolyTime
        W []
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa only [id_eq,
            verifierTransitionAffineHeadControllerMarkedFrames, dite_true]
            using run }
  · let source :=
      verifierTransitionAffineFormDescriptorFamilyTotal_computableInPolyTime
        W (transitionAffineStmtScriptFieldForms phases)
    let sourceRaw : _root_.Turing.TM2ComputableInPolyTime id id
        (fun input => encodeUnaryFrameMarkedRowFamily
          (verifierTransitionAffineFormDescriptorFamily W
            (transitionAffineStmtScriptFieldForms phases) input)) :=
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          simpa only [id_eq] using source.outputsFun input }
    let delimited := unaryFrameDelimiterMap_computableInPolyTime
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
    let composed :=
      _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch sourceRaw
        delimited
    let result := Classical.choice composed
    exact
      { tm := result.tm
        inputAlphabet := result.inputAlphabet
        outputAlphabet := result.outputAlphabet
        time := result.time
        outputsFun := fun input => by
          have run := result.outputsFun input
          simpa only [Function.comp_def, id_eq,
            verifierTransitionAffineHeadControllerMarkedFrames, hphases,
            dite_false] using run }

end CLRS.Chapter34.Turing.CookLevin
