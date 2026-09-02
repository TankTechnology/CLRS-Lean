import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketPipeline

/-!
# Fixed interpreter for length-prefixed transition descriptors

This module bridges the self-describing numeric row used by recursive syntax
to the existing four-row mux packet pipeline.  The bridge is generic over any
aligned mux-view family and reuses the verified dynamic splitter unchanged.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Flatten the coordinate triples into the numeric row consumed by the
four-way splitter. -/
def TransitionDispatchMuxInvocationView.coordinateValues
    (view : TransitionDispatchMuxInvocationView) : List Nat :=
  view.coordinates.flatMap fun coordinate =>
    [coordinate.1, coordinate.2.1, coordinate.2.2]

@[simp] theorem TransitionDispatchMuxInvocationView.coordinateValues_length
    (view : TransitionDispatchMuxInvocationView) :
    view.coordinateValues.length = 3 * view.coordinates.length := by
  unfold TransitionDispatchMuxInvocationView.coordinateValues
  induction view.coordinates with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem TransitionDispatchMuxInvocationView.coordinateValues_encoding
    (view : TransitionDispatchMuxInvocationView) :
    encodeUnaryFrame view.coordinateValues =
      transitionDispatchMuxCoordinateRowFrames view.coordinates := by
  unfold TransitionDispatchMuxInvocationView.coordinateValues
    transitionDispatchMuxCoordinateRowFrames encodeUnaryFrame
  rw [List.flatMap_assoc]

/-- Package one aligned semantic mux view as a well-sized dynamic-splitter
packet. -/
def TransitionDispatchMuxInvocationView.lengthPrefixedPacket
    (view : TransitionDispatchMuxInvocationView)
    (haligned : view.RowAligned) :
    UnaryFrameLengthPrefixedFourWayPacket where
  width := view.coordinates.length
  selector := view.selector
  coordinates := view.coordinateValues
  whenTrue := view.whenTrue
  whenFalse := view.whenFalse
  coordinates_length := view.coordinateValues_length
  whenTrue_length := haligned.1.symm
  whenFalse_length := haligned.2.symm

theorem TransitionDispatchMuxInvocationView.lengthPrefixedPacket_sourceFrames
    (view : TransitionDispatchMuxInvocationView)
    (haligned : view.RowAligned) :
    (view.lengthPrefixedPacket haligned).sourceFrames =
      encodeUnaryFrame [view.coordinates.length] ++ view.numericDescriptorRow ++
        [UnaryFrameSym.frameEnd] := by
  unfold TransitionDispatchMuxInvocationView.lengthPrefixedPacket
    UnaryFrameLengthPrefixedFourWayPacket.sourceFrames
    encodeUnaryFrameLengthPrefixedFourWaySplitInput
  rw [view.coordinateValues_encoding]
  simp [TransitionDispatchMuxInvocationView.numericDescriptorRow,
    encodeUnaryFrame, List.append_assoc]

theorem TransitionDispatchMuxInvocationView.lengthPrefixedPacket_outputFrames
    (view : TransitionDispatchMuxInvocationView)
    (haligned : view.RowAligned) :
    (view.lengthPrefixedPacket haligned).outputFrames =
      view.labelPacketFrames := by
  simp [TransitionDispatchMuxInvocationView.lengthPrefixedPacket,
    UnaryFrameLengthPrefixedFourWayPacket.outputFrames,
    encodeUnaryFrameLengthPrefixedFourWaySplitOutput,
    TransitionDispatchMuxInvocationView.labelPacketFrames,
    view.coordinateValues_encoding, List.append_assoc]

/-- Turn a proof-carrying aligned list into a dynamic-splitter packet list. -/
def transitionDispatchMuxInvocationLengthPrefixedPacketsFrom :
    (views : List TransitionDispatchMuxInvocationView) →
      (∀ view ∈ views, view.RowAligned) →
        List UnaryFrameLengthPrefixedFourWayPacket
  | [], _ => []
  | view :: rest, haligned =>
      view.lengthPrefixedPacket (haligned view (by simp)) ::
        transitionDispatchMuxInvocationLengthPrefixedPacketsFrom rest
          (fun item hitem => haligned item (by simp [hitem]))

def AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedPackets
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    List UnaryFrameLengthPrefixedFourWayPacket :=
  transitionDispatchMuxInvocationLengthPrefixedPacketsFrom family.views
    family.rowAligned

/-- Literal concatenation of all self-describing numeric packets. -/
def AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    List UnaryFrameSym :=
  encodeUnaryFrameLengthPrefixedFourWayPacketFamily
    family.lengthPrefixedPackets

private theorem lengthPrefixedPacketsFrom_sourceFrames
    (views : List TransitionDispatchMuxInvocationView)
    (haligned : ∀ view ∈ views, view.RowAligned) :
    encodeUnaryFrameLengthPrefixedFourWayPacketFamily
        (transitionDispatchMuxInvocationLengthPrefixedPacketsFrom views
          haligned) =
      views.flatMap fun view =>
        encodeUnaryFrame [view.coordinates.length] ++ view.numericDescriptorRow ++
          [UnaryFrameSym.frameEnd] := by
  induction views with
  | nil => rfl
  | cons view rest ih =>
      simp only [transitionDispatchMuxInvocationLengthPrefixedPacketsFrom,
        encodeUnaryFrameLengthPrefixedFourWayPacketFamily, List.flatMap_cons]
      rw [view.lengthPrefixedPacket_sourceFrames]
      have ih' := ih (fun item hitem => haligned item (by simp [hitem]))
      change List.flatMap UnaryFrameLengthPrefixedFourWayPacket.sourceFrames
          (transitionDispatchMuxInvocationLengthPrefixedPacketsFrom rest _) = _
        at ih'
      rw [ih']

private theorem lengthPrefixedPacketsFrom_outputFrames
    (views : List TransitionDispatchMuxInvocationView)
    (haligned : ∀ view ∈ views, view.RowAligned) :
    unaryFrameLengthPrefixedFourWayPacketFamilyOutput
        (transitionDispatchMuxInvocationLengthPrefixedPacketsFrom views
          haligned) =
      views.flatMap TransitionDispatchMuxInvocationView.labelPacketFrames := by
  induction views with
  | nil => rfl
  | cons view rest ih =>
      simp only [transitionDispatchMuxInvocationLengthPrefixedPacketsFrom,
        unaryFrameLengthPrefixedFourWayPacketFamilyOutput, List.flatMap_cons]
      rw [view.lengthPrefixedPacket_outputFrames]
      have ih' := ih (fun item hitem => haligned item (by simp [hitem]))
      change List.flatMap UnaryFrameLengthPrefixedFourWayPacket.outputFrames
          (transitionDispatchMuxInvocationLengthPrefixedPacketsFrom rest _) = _
        at ih'
      rw [ih']

theorem AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames_eq
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    family.lengthPrefixedDescriptorFrames =
      family.views.flatMap fun view =>
        encodeUnaryFrame [view.coordinates.length] ++ view.numericDescriptorRow ++
          [UnaryFrameSym.frameEnd] := by
  exact lengthPrefixedPacketsFrom_sourceFrames family.views family.rowAligned

theorem AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedPackets_output
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    unaryFrameLengthPrefixedFourWayPacketFamilyOutput
        family.lengthPrefixedPackets = family.labelPacketFrames := by
  unfold AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
  rw [encode_transitionDispatchMuxInvocationLabelPacketFamily]
  exact lengthPrefixedPacketsFrom_outputFrames family.views family.rowAligned

/-- The dynamic splitter is a fixed polynomial-time interpreter from aligned
length-prefixed numeric descriptors to the existing four-row packet format. -/
noncomputable def
    transitionDispatchMuxInvocationLengthPrefixedDescriptorInterpreter_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames id := by
  let generic :=
    unaryFrameLengthPrefixedFourWayPacketFamilyOutput_computableInPolyTime
  exact
    { tm := generic.tm
      inputAlphabet := generic.inputAlphabet
      outputAlphabet := generic.outputAlphabet
      time := generic.time
      outputsFun := fun family => by
        have run := generic.outputsFun family.lengthPrefixedPackets
        simpa only [id_eq,
          AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames,
          family.lengthPrefixedPackets_output] using run }

end CLRS.Chapter34.Turing.CookLevin
