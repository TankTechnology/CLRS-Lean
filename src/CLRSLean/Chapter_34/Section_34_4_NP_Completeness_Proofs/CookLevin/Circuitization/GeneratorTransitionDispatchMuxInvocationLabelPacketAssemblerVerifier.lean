import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerFamily
import Mathlib.Tactic

/-!
# Verifier-level dispatch-mux packet assembly

This module instantiates the whole-family theorem with every label view derived
from every canonical verifier transition-row seed.  The result is an exact,
halting execution from the concrete prepared packet stream to the reverse of
the already verified dispatch-mux invocation source.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Seed-major list of every canonical dispatch-mux label view. -/
noncomputable def verifierTransitionDispatchMuxInvocationViews
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List TransitionDispatchMuxInvocationView :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed

/-- Every view in the complete verifier family satisfies the row-alignment
invariant required by the concrete assembler. -/
theorem verifierTransitionDispatchMuxInvocationViews_rowAligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ view ∈ verifierTransitionDispatchMuxInvocationViews W input,
      view.RowAligned := by
  intro view hview
  rw [verifierTransitionDispatchMuxInvocationViews,
    List.mem_flatMap] at hview
  rcases hview with ⟨seed, hseed, hview⟩
  exact transitionDispatchMuxDescriptorInvocationViews_rowAligned
    W input seed hseed view hview

/-- Once all prepared labels are consumed, two control transitions enter the
actual halting configuration without changing the accumulated output. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_halt
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg [] output)
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram output))
      2 := by
  exact ⟨⟨2, rfl⟩, le_rfl⟩

/-- Exact verifier-instance transition count, including the final halt. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
      (verifierTransitionDispatchMuxInvocationViews W input) + 2

/-- The concrete fixed assembler consumes the actual prepared verifier packet
stream, halts, and leaves exactly the reverse of the canonical dispatch-mux
invocation source on its output tape. -/
def verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
          W input).reverse))
      (verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
        W input) := by
  let views := verifierTransitionDispatchMuxInvocationViews W input
  have hprepared :
      verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input =
        views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames := by
    simpa [views, verifierTransitionDispatchMuxInvocationViews] using
      verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames_eq
        W input
  have hsource :
      verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
        views.flatMap TransitionDispatchMuxInvocationView.sourceFrames := by
    rw [
      verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_reassembledViews]
    simp [views, verifierTransitionDispatchMuxInvocationViews,
      List.flatMap_assoc]
  have haligned : ∀ view ∈ views, view.RowAligned := by
    simpa [views] using
      verifierTransitionDispatchMuxInvocationViews_rowAligned W input
  have hfamily : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg []
        (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
          W input).reverse))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        views) := by
    simpa [hprepared, hsource] using
      transitionDispatchMuxInvocationLabelPacketAssembler_views_sourceFrames
        views [] [] haligned
  have hhalt :=
    transitionDispatchMuxInvocationLabelPacketAssembler_halt
      (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
        W input).reverse
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps views)
    2 _
    (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg []
      (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
        W input).reverse)
    _ hfamily hhalt
  convert full using 1 <;>
    simp [verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps,
      views] <;>
    omega

/-- The same halting execution stated with the canonical invocation source
already consumed by the verified affine-mux controller. -/
def verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev_source
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        (verifierTransitionDispatchMuxInvocationSourceFrames W input).reverse))
      (verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
        W input) := by
  simpa [verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq]
    using
      verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev W input

end CLRS.Chapter34.Turing.CookLevin
