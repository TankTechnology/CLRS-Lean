import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerLabel
import Mathlib.Tactic

/-!
# Whole-family dispatch-mux packet assembly

The per-label exact theorem is lifted here to any list of aligned label views.
The same fixed controller consumes their concatenated stack-ready packets and
accumulates the reverse of the complete canonical mux-source family.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact transition count for loading and assembling a list of labels. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
    (views : List TransitionDispatchMuxInvocationView) : Nat :=
  (views.map fun view =>
    transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view +
      transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
        view.selector true view.frames).sum

/-- Exact execution of the fixed assembler over any aligned list of prepared
label packets. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_views
    (views : List TransitionDispatchMuxInvocationView)
    (tail output : List UnaryFrameSym)
    (haligned : ∀ view ∈ views, view.RowAligned) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames ++
          tail) output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        (((views.flatMap fun view =>
          transitionDispatchMuxInvocationLabelSourceRows
            view.selector view.frames).reverse) ++ output)))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        views) := by
  induction views generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons view views ih =>
      have hview : view.RowAligned := haligned view (by simp)
      have hviews : ∀ other ∈ views, other.RowAligned := by
        intro other hother
        exact haligned other (by simp [hother])
      let remainingInput :=
        views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames ++ tail
      let viewOutput :=
        (transitionDispatchMuxInvocationLabelSourceRows
          view.selector view.frames).reverse ++ output
      have hload : EvalsToInTime
          (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
            ((view :: views).flatMap
              TransitionDispatchMuxInvocationView.preparedLabelPacketFrames ++
              tail) output)
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
            view remainingInput output))
          (transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps
            view) := by
        simpa [remainingInput, List.append_assoc] using
          transitionDispatchMuxInvocationLabelPacketAssembler_load
            view remainingInput output
      have hlabel : EvalsToInTime
          (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
            view remainingInput output)
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
            remainingInput viewOutput))
          (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
            view.selector true view.frames) := by
        simpa [viewOutput] using
          transitionDispatchMuxInvocationLabelPacketAssembler_label
            view remainingInput output hview
      let hhead := EvalsToInTime.trans
        (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
        (transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view)
        (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
          view.selector true view.frames)
        _
        (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
          view remainingInput output)
        _ hload hlabel
      have htail := ih (output := viewOutput) hviews
      let full := EvalsToInTime.trans
        (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
        (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
            view.selector true view.frames +
          transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view)
        (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps views)
        _
        (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
          remainingInput viewOutput)
        _ hhead htail
      convert full using 1 <;>
        simp [transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps,
          remainingInput, viewOutput, List.reverse_append,
          List.append_assoc] <;>
        omega

/-- The family theorem stated directly with the abstract canonical
`sourceFrames` projection of each mux view. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_views_sourceFrames
    (views : List TransitionDispatchMuxInvocationView)
    (tail output : List UnaryFrameSym)
    (haligned : ∀ view ∈ views, view.RowAligned) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames ++
          tail) output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        ((views.flatMap TransitionDispatchMuxInvocationView.sourceFrames
          ).reverse ++ output)))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        views) := by
  have hsources :
      (views.flatMap fun view =>
        transitionDispatchMuxInvocationLabelSourceRows
          view.selector view.frames) =
        views.flatMap TransitionDispatchMuxInvocationView.sourceFrames := by
    apply List.flatMap_congr
    intro view hview
    exact view.sourceFrames_eq_rows.symm
  simpa [hsources] using
    transitionDispatchMuxInvocationLabelPacketAssembler_views
      views tail output haligned

end CLRS.Chapter34.Turing.CookLevin
