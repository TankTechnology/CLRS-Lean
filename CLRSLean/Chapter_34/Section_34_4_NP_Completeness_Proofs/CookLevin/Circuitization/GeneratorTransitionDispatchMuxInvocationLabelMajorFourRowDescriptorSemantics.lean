import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorSource

/-!
# Exact packet semantics of the label-major four-row descriptor source

The concrete delimiter source now has a typed, byte-exact contract.  For
every transition seed and program label it emits, in order, one selector row,
one fresh-coordinate descriptor row, one normalized true-arm descriptor row,
and one false-arm descriptor row.  This is the physical input shape needed by
the remaining periodic descriptor interpreter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The four descriptor-value rows carried by one typed label packet. -/
def
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorValueGroups
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    List (List Nat) :=
  [ [packet.selector],
    transitionDispatchProgressionDescriptorValues
      packet.coordinateProgressions,
    packet.trueLayout.affineSpanDescriptorValues tm seed,
    transitionDispatchProgressionDescriptorValues packet.falseProgressions ]

/-- Physical marked encoding of the four descriptor rows of one label. -/
def
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorFrames
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    List UnaryFrameSym :=
  (packet.fourRowDescriptorValueGroups seed).flatMap
    encodeUnaryFrameFixedWidthPacket

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_fourRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (selectors : List Nat)
    (coordinateGroups : List (List AffineUnaryTripleProgression))
    (trueLayouts : List (TransitionDispatchTrueArmNormalizedLayout tm))
    (falseGroups : List (List AffineUnaryTripleProgression)) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
        selectors coordinateGroups trueLayouts falseGroups).flatMap
        (fun packet => packet.fourRowDescriptorValueGroups seed) =
      transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
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
                  change
                    [[selector],
                      transitionDispatchProgressionDescriptorValues coordinates,
                      trueLayout.affineSpanDescriptorValues tm seed,
                      transitionDispatchProgressionDescriptorValues whenFalse] ++
                        (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom
                          tm selectors coordinateGroups trueLayouts
                          falseGroups).flatMap
                            (fun packet =>
                              packet.fourRowDescriptorValueGroups seed) =
                      [[selector],
                        transitionDispatchProgressionDescriptorValues coordinates,
                        trueLayout.affineSpanDescriptorValues tm seed,
                        transitionDispatchProgressionDescriptorValues whenFalse] ++
                          transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
                            selectors
                            (coordinateGroups.map
                              transitionDispatchProgressionDescriptorValues)
                            (trueLayouts.map fun layout =>
                              layout.affineSpanDescriptorValues tm seed)
                            (falseGroups.map
                              transitionDispatchProgressionDescriptorValues)
                  rw [ih coordinateGroups trueLayouts falseGroups]

/-- Flattening the four rows of every typed packet gives the canonical
seed-local four-row value family. -/
theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_fourRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets tm seed).flatMap
        (fun packet => packet.fourRowDescriptorValueGroups seed) =
      transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
        tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
  exact
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_fourRows
      tm seed _ _ _ _

private theorem
    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_encoding
    (seed : TransitionRowSeed) (forms : List AffineUnaryTripleForm) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap forms (transitionTailAffineSeed seed))
        (transitionDispatchMuxInvocationLabelMajorSectionDelimiters forms) =
      encodeUnaryFrameFixedWidthPacket
        (affineUnaryTripleMap forms (transitionTailAffineSeed seed)) := by
  cases forms with
  | nil =>
      simp [affineUnaryTripleMap,
        transitionDispatchMuxInvocationLabelMajorSectionDelimiters,
        encodeUnaryFrameWithFixedDelimiters,
        encodeUnaryFrameFixedWidthPacket]
  | cons form forms =>
      let values := affineUnaryTripleMap (form :: forms)
        (transitionTailAffineSeed seed)
      have hvalues : values ≠ [] := by
        simp [values, affineUnaryTripleMap]
      have hdelimiters :
          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
              (form :: forms) =
            List.replicate forms.length .separator ++ [.frameEnd] := by
        apply List.ext_getElem
        · simp [transitionDispatchMuxInvocationLabelMajorSectionDelimiters]
        · intro index hleft hright
          simp only [
            transitionDispatchMuxInvocationLabelMajorSectionDelimiters,
            List.getElem_ofFn]
          have hbound : index < forms.length + 1 := by
            simpa [
              transitionDispatchMuxInvocationLabelMajorSectionDelimiters]
              using hleft
          by_cases hindex : index < forms.length
          · have hnotIndex : ¬index = forms.length := by omega
            simp [hindex, hnotIndex]
          · have hlast : index = forms.length := by omega
            subst index
            simp
      change encodeUnaryFrameWithFixedDelimiters values _ =
        encodeUnaryFrameFixedWidthPacket values
      rw [hdelimiters]
      have hlength : values.length - 1 = forms.length := by
        simp [values, affineUnaryTripleMap]
      rw [← hlength]
      rw [encodeUnaryFrameWithOwnFinalDelimiter values .frameEnd hvalues]
      cases hvaluesEq : values with
      | nil => exact False.elim (hvalues hvaluesEq)
      | cons value rest =>
          simpa [hvaluesEq] using
            (encodeUnaryFrameFixedWidthPacket_eq_body value rest).symm

private theorem
    transitionDispatchMuxInvocationLabelMajorFourRowForms_fixed_encoding
    (seed : TransitionRowSeed) :
    ∀ (selectors : List AffineUnaryTripleForm)
      (coordinateGroups trueGroups falseGroups :
        List (List AffineUnaryTripleForm)),
      encodeUnaryFrameWithFixedDelimiters
          ((transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
            selectors coordinateGroups trueGroups falseGroups).map
              (fun group => affineUnaryTripleMap group
                (transitionTailAffineSeed seed))).flatten
          (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom
            selectors coordinateGroups trueGroups falseGroups).flatten =
        (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
          (affineUnaryTripleMap selectors (transitionTailAffineSeed seed))
          (coordinateGroups.map fun group => affineUnaryTripleMap group
            (transitionTailAffineSeed seed))
          (trueGroups.map fun group => affineUnaryTripleMap group
            (transitionTailAffineSeed seed))
          (falseGroups.map fun group => affineUnaryTripleMap group
            (transitionTailAffineSeed seed))).flatMap
              encodeUnaryFrameFixedWidthPacket := by
  intro selectors coordinateGroups trueGroups falseGroups
  induction selectors generalizing coordinateGroups trueGroups falseGroups with
  | nil => rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => rfl
      | cons coordinates coordinateGroups =>
          cases trueGroups with
          | nil => rfl
          | cons whenTrue trueGroups =>
              cases falseGroups with
              | nil => rfl
              | cons whenFalse falseGroups =>
                  have hhead :
                      (affineUnaryTripleMap
                        (selector :: coordinates ++ whenTrue ++ whenFalse)
                        (transitionTailAffineSeed seed)).length =
                        ([UnaryFrameSym.frameEnd] ++
                          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            coordinates ++
                          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            whenTrue ++
                          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            whenFalse).length := by
                    simp [affineUnaryTripleMap,
                      transitionDispatchMuxInvocationLabelMajorSectionDelimiters]
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom,
                    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom,
                    List.map_cons, List.flatten_cons]
                  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ hhead]
                  rw [ih coordinateGroups trueGroups falseGroups]
                  simp only [affineUnaryTripleMap, List.map_cons,
                    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom,
                    List.flatMap_append, List.flatMap_cons,
                    List.flatMap_nil, List.append_nil]
                  apply congrArg (fun head => head ++ _)
                  simp only [List.map_cons, List.map_append]
                  change encodeUnaryFrameWithFixedDelimiters
                      ([affineUnaryTripleFormValue selector
                          (transitionTailAffineSeed seed)] ++
                        (affineUnaryTripleMap coordinates
                            (transitionTailAffineSeed seed) ++
                          affineUnaryTripleMap whenTrue
                            (transitionTailAffineSeed seed) ++
                          affineUnaryTripleMap whenFalse
                            (transitionTailAffineSeed seed)))
                      ([UnaryFrameSym.frameEnd] ++
                        (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            coordinates ++
                          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            whenTrue ++
                          transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                            whenFalse)) =
                    encodeUnaryFrameFixedWidthPacket
                        [affineUnaryTripleFormValue selector
                          (transitionTailAffineSeed seed)] ++
                      (encodeUnaryFrameFixedWidthPacket
                          (affineUnaryTripleMap coordinates
                            (transitionTailAffineSeed seed)) ++
                        (encodeUnaryFrameFixedWidthPacket
                            (affineUnaryTripleMap whenTrue
                              (transitionTailAffineSeed seed)) ++
                          encodeUnaryFrameFixedWidthPacket
                            (affineUnaryTripleMap whenFalse
                              (transitionTailAffineSeed seed))))
                  rw [encodeUnaryFrameWithFixedDelimiters_append
                    [_]
                    (affineUnaryTripleMap coordinates
                        (transitionTailAffineSeed seed) ++
                      affineUnaryTripleMap whenTrue
                        (transitionTailAffineSeed seed) ++
                      affineUnaryTripleMap whenFalse
                        (transitionTailAffineSeed seed))
                    [UnaryFrameSym.frameEnd]
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                        coordinates ++
                      transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                        whenTrue ++
                      transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                        whenFalse)
                    (by simp)]
                  rw [List.append_assoc
                    (affineUnaryTripleMap coordinates
                      (transitionTailAffineSeed seed))
                    (affineUnaryTripleMap whenTrue
                      (transitionTailAffineSeed seed))
                    (affineUnaryTripleMap whenFalse
                      (transitionTailAffineSeed seed))]
                  rw [List.append_assoc
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      coordinates)
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      whenTrue)
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      whenFalse)]
                  rw [encodeUnaryFrameWithFixedDelimiters_append
                    (affineUnaryTripleMap coordinates
                      (transitionTailAffineSeed seed))
                    (affineUnaryTripleMap whenTrue
                        (transitionTailAffineSeed seed) ++
                      affineUnaryTripleMap whenFalse
                        (transitionTailAffineSeed seed))
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      coordinates)
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                        whenTrue ++
                      transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                        whenFalse)
                    (by simp [affineUnaryTripleMap])]
                  rw [encodeUnaryFrameWithFixedDelimiters_append
                    (affineUnaryTripleMap whenTrue
                      (transitionTailAffineSeed seed))
                    (affineUnaryTripleMap whenFalse
                      (transitionTailAffineSeed seed))
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      whenTrue)
                    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
                      whenFalse)
                    (by simp [affineUnaryTripleMap])]
                  simp only [encodeUnaryFrameWithFixedDelimiters,
                    encodeUnaryFrameFixedWidthPacket]
                  rw [
                    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_encoding
                      seed coordinates]
                  rw [
                    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_encoding
                      seed whenTrue]
                  rw [
                    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_encoding
                      seed whenFalse]

/-- The actual raw-input source is exactly the seed-major, label-major
concatenation of four physical descriptor rows from every typed packet. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq_packets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet =>
            packet.fourRowDescriptorFrames seed := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq]
  apply List.flatMap_congr
  intro seed hseed
  rw [←
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical]
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroups
  rw [
    transitionDispatchMuxInvocationLabelMajorFourRowForms_fixed_encoding seed]
  rw [←
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups_eq_forms]
  rw [←
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_fourRows]
  simp [
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorFrames,
    List.flatMap_assoc]

end CLRS.Chapter34.Turing.CookLevin
