import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelReassembly

/-!
# Typed semantics of label-major dispatch descriptor packets

The physical label-major source carries one marked descriptor group per
program label.  This module gives that group a typed, label-local contract:
one selector, one fresh-coordinate progression family, one normalized
true-arm layout, and one false-arm progression family.  It proves both sides
of the contract.  Serializing the typed packets gives exactly the canonical
descriptor groups, while interpreting them gives exactly the four-row views
already accepted by the verified mux label-packet assembler.

No machine is introduced here.  The point is to make the remaining concrete
streaming interpreter prove one local specification instead of reasoning
again about whole transition artifacts.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Typed contents of one label-major descriptor packet. -/
structure TransitionDispatchMuxInvocationLabelMajorDescriptorPacket
    (tm : _root_.Turing.FinTM2) where
  selector : Nat
  coordinateProgressions : List AffineUnaryTripleProgression
  trueLayout : TransitionDispatchTrueArmNormalizedLayout tm
  falseProgressions : List AffineUnaryTripleProgression

/-- The exact runtime natural-number fields physically stored for a packet. -/
def TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.descriptorValues
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    List Nat :=
  packet.selector ::
    transitionDispatchProgressionDescriptorValues
        packet.coordinateProgressions ++
      packet.trueLayout.affineSpanDescriptorValues tm seed ++
      transitionDispatchProgressionDescriptorValues packet.falseProgressions

/-- Interpret one typed packet as the four semantic rows consumed by the
existing label-packet assembler. -/
noncomputable def
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.view
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    TransitionDispatchMuxInvocationView :=
  { selector := packet.selector
    coordinates := packet.coordinateProgressions.flatMap
      affineUnaryTripleProgressionRows
    whenTrue :=
      (packet.trueLayout.affineSpanProgressions tm seed).flatMap
        transitionProgressionFirstValues
    whenFalse := packet.falseProgressions.flatMap
      transitionProgressionFirstValues }

/-- Lock-step typed reassembly of the four verifier-fixed label tables. -/
def transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom
    (tm : _root_.Turing.FinTM2) :
    List Nat → List (List AffineUnaryTripleProgression) →
      List (TransitionDispatchTrueArmNormalizedLayout tm) →
      List (List AffineUnaryTripleProgression) →
      List (TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm)
  | selector :: selectors, coordinates :: coordinateGroups,
      trueLayout :: trueLayouts, whenFalse :: falseGroups =>
      { selector := selector
        coordinateProgressions := coordinates
        trueLayout := trueLayout
        falseProgressions := whenFalse } ::
        transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
          selectors coordinateGroups trueLayouts falseGroups
  | _, _, _, _ => []

/-- Canonical typed packet family for one transition seed. -/
noncomputable def transitionDispatchMuxInvocationLabelMajorDescriptorPackets
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :=
  transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
    (transitionDispatchSelectors tm seed)
    (transitionDispatchMuxCoordinateProgressionGroups tm seed)
    (transitionDispatchTrueArmNormalizedLayouts tm)
    (transitionDispatchFalseArmProgressionGroups tm seed)

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (selectors : List Nat)
    (coordinateGroups : List (List AffineUnaryTripleProgression))
    (trueLayouts : List (TransitionDispatchTrueArmNormalizedLayout tm))
    (falseGroups : List (List AffineUnaryTripleProgression)) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
        selectors coordinateGroups trueLayouts falseGroups).map
        (fun packet => packet.descriptorValues seed) =
      transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom
        selectors
        (coordinateGroups.map transitionDispatchProgressionDescriptorValues)
        (trueLayouts.map fun layout =>
          layout.affineSpanDescriptorValues tm seed)
        (falseGroups.map transitionDispatchProgressionDescriptorValues) := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil => rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => rfl
      | cons coordinates coordinateGroups =>
          cases trueLayouts with
          | nil => rfl
          | cons trueLayout trueLayouts =>
              cases falseGroups with
              | nil => rfl
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom,
                    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom,
                    List.map_cons]
                  congr 1
                  exact ih coordinateGroups trueLayouts falseGroups

/-- Serializing the typed packets recovers the canonical label-major value
groups exactly, with no permutation or inferred boundary. -/
theorem transitionDispatchMuxInvocationLabelMajorDescriptorPackets_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets tm seed).map
        (fun packet => packet.descriptorValues seed) =
      transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
  exact
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_values
      tm seed _ _ _ _

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_views
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (selectors : List Nat)
    (coordinateGroups : List (List AffineUnaryTripleProgression))
    (trueLayouts : List (TransitionDispatchTrueArmNormalizedLayout tm))
    (falseGroups : List (List AffineUnaryTripleProgression)) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
        selectors coordinateGroups trueLayouts falseGroups).map
        (fun packet => packet.view seed) =
      transitionDispatchMuxInvocationViewsFromRows selectors
        (coordinateGroups.map fun progressions =>
          progressions.flatMap affineUnaryTripleProgressionRows)
        (trueLayouts.map fun layout =>
          (layout.affineSpanProgressions tm seed).flatMap
            transitionProgressionFirstValues)
        (falseGroups.map fun progressions =>
          progressions.flatMap transitionProgressionFirstValues) := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil => rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => rfl
      | cons coordinates coordinateGroups =>
          cases trueLayouts with
          | nil => rfl
          | cons trueLayout trueLayouts =>
              cases falseGroups with
              | nil => rfl
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom,
                    transitionDispatchMuxInvocationViewsFromRows,
                    List.map_cons]
                  congr 1
                  exact ih coordinateGroups trueLayouts falseGroups

/-- Interpreting the typed label-major packets yields exactly the established
descriptor-derived mux views. -/
theorem transitionDispatchMuxInvocationLabelMajorDescriptorPackets_views
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets tm seed).map
        (fun packet => packet.view seed) =
      transitionDispatchMuxDescriptorInvocationViews tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
    transitionDispatchMuxDescriptorInvocationViews
    transitionDispatchTrueArmSpanProgressionGroups
  simpa [List.map_map, Function.comp_def] using
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_views
      tm seed (transitionDispatchSelectors tm seed)
      (transitionDispatchMuxCoordinateProgressionGroups tm seed)
      (transitionDispatchTrueArmNormalizedLayouts tm)
      (transitionDispatchFalseArmProgressionGroups tm seed))

/-- Label-packet frames obtained by interpreting the typed label-major source
from every verifier seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketsLabelPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
      W.machine.tm seed).flatMap fun packet =>
        (packet.view seed).labelPacketFrames

/-- The typed local interpreter contract lands byte-for-byte on the physical
four-row contract of the existing mux label-packet assembler. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPackets_labelPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketsLabelPacketFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
        W input := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketsLabelPacketFrames
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
  apply List.flatMap_congr
  intro seed hseed
  have hviews :=
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_views
      W.machine.tm seed
  have hframes := congrArg
    (List.flatMap TransitionDispatchMuxInvocationView.labelPacketFrames)
    hviews
  simpa [List.flatMap_map, Function.comp_def] using hframes

end CLRS.Chapter34.Turing.CookLevin
