import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.MinimumVertexCount
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.TargetIncrement
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# HAM-CYCLE verifier: composed scalar checks

This module turns the two target-field transducers into the Boolean checks
needed by the final verifier.  Increment followed by the reused CLIQUE
target-bound pass tests `targetSize < vertexCount`; negating that result,
together with the ordinary base bound, enforces equality.  Replacing the
target by three followed by the same pass enforces the textbook minimum
cycle size.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine

open _root_.Turing

/-- Paired raw verifier input. -/
abbrev RawInput := TargetIncrement.RawInput

/-- Physical separator encoding shared by every final verifier branch. -/
abbrev rawEncoding : RawInput → List (Option CliqueSym) :=
  TargetIncrement.rawEncoding

/-- Strict target test obtained by incrementing the target field and reusing
the CLIQUE target-bound pass. -/
def targetStrictCheck (input : RawInput) : Bool :=
  GeneralCliqueVerifier.TargetBound.targetBoundPass input.1
    (TargetIncrement.incrementTargetField input.2)

/-- A fixed polynomial-time TM2 computes the strict target test. -/
noncomputable def targetStrictCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      targetStrictCheck := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TargetIncrement.computableInPolyTime
    GeneralCliqueVerifier.TargetBound.targetBoundPassComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => GeneralCliqueVerifier.TargetBound.targetBoundPass input.1
      (TargetIncrement.incrementTargetField input.2))
  simpa [TargetIncrement.incrementedInput, Function.comp_def] using
      Classical.choice composed

/-- Negating strict target inequality.  The final conjunction also contains
the base condition `targetSize ≤ vertexCount`, so the two checks force
`targetSize = vertexCount`. -/
def targetEqualityCheck (input : RawInput) : Bool :=
  !(targetStrictCheck input)

/-- A fixed polynomial-time TM2 computes the negated strict target test. -/
noncomputable def targetEqualityCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      targetEqualityCheck := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    targetStrictCheckComputableInPolyTime TM2Comp.notComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => !(targetStrictCheck input))
  simpa [targetEqualityCheck, Function.comp_def] using Classical.choice composed

/-- Canonical semantics of the target equality branch. -/
theorem targetEqualityCheck_encode_iff
    (certificate : List CliqueSym) (I : CliqueInstance) :
    targetEqualityCheck (certificate, encodeCliqueInstance I) = true ↔
      ¬I.targetSize < I.vertexCount := by
  have hstrict :=
    TargetIncrement.targetBound_incremented_encode_iff certificate I
  simpa [targetEqualityCheck, targetStrictCheck] using not_congr hstrict

/-- Minimum-size test obtained by replacing the graph target with three and
reusing the CLIQUE target-bound pass. -/
def minimumVertexCountCheck (input : RawInput) : Bool :=
  GeneralCliqueVerifier.TargetBound.targetBoundPass input.1
    (MinimumVertexCount.replaceTargetWithThree input.2)

/-- A fixed polynomial-time TM2 computes the three-vertex minimum test. -/
noncomputable def minimumVertexCountCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      minimumVertexCountCheck := by
  let source := MinimumVertexCount.computableInPolyTime
  let transformed : TM2ComputableInPolyTime rawEncoding rawEncoding
      MinimumVertexCount.replacedInput :=
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa [MinimumVertexCount.rawEncoding,
          TargetIncrement.rawEncoding] using source.outputsFun input }
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    transformed
    GeneralCliqueVerifier.TargetBound.targetBoundPassComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => GeneralCliqueVerifier.TargetBound.targetBoundPass input.1
      (MinimumVertexCount.replaceTargetWithThree input.2))
  simpa [MinimumVertexCount.replacedInput, Function.comp_def] using
      Classical.choice composed

/-- Canonical semantics of the minimum-size branch. -/
theorem minimumVertexCountCheck_encode_iff
    (certificate : List CliqueSym) (I : CliqueInstance) :
    minimumVertexCountCheck (certificate, encodeCliqueInstance I) = true ↔
      3 ≤ I.vertexCount := by
  exact MinimumVertexCount.targetBound_replaced_encode_iff certificate I

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine
