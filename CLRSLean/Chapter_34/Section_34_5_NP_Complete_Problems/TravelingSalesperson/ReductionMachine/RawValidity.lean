import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.ComponentChecks
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.RawWellFormed
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-!
# Raw HAM-CYCLE validity guard for the TSP reduction

The serialized reduction is defined on every raw word.  Its ordinary branch
requires both the general graph invariants and the HAM-CYCLE header convention
`targetSize = vertexCount`.  The second condition is obtained by reusing the
fixed strict-target checker from the HAM-CYCLE verifier.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.RawValidity

open _root_.Turing
open VertexCover.ComplementMachine
open HamiltonianCycle.VerifierMachine

local instance : Inhabited CliqueSym := ⟨.tick⟩

/-- The reused target-equality check specialized to an empty certificate. -/
def graphTargetEqualityPass (graph : List CliqueSym) : Bool :=
  targetEqualityCheck ([], graph)

/-- Repackage the existing paired checker as a graph-only checker. -/
noncomputable def graphTargetEqualityComputableInPolyTime :
    TM2ComputableInPolyTime
      WellFormedGuard.graphPairEncoding TM2Comp.boolEncoding
      graphTargetEqualityPass := by
  let machine := targetEqualityCheckComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun graph => by
        have output := machine.outputsFun ([], graph)
        simpa [graphTargetEqualityPass, rawEncoding,
          TargetIncrement.rawEncoding,
          WellFormedGuard.graphPairEncoding] using output }

/-- Target-equality result for the syntax-normalized graph. -/
def rawTargetEqualityPass (input : List CliqueSym) : Bool :=
  graphTargetEqualityPass
    (encodeCliqueInstance (SyntaxNormalizer.normalizedInstanceValue input))

/-- A fixed polynomial-time machine computes target equality from a raw word. -/
noncomputable def rawTargetEqualityComputableInPolyTime :
    TM2ComputableInPolyTime id TM2Comp.boolEncoding
      rawTargetEqualityPass := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    RawWellFormed.normalizedGraphPairComputableInPolyTime
    graphTargetEqualityComputableInPolyTime
  change TM2ComputableInPolyTime id TM2Comp.boolEncoding
    (fun input => graphTargetEqualityPass
      (encodeCliqueInstance (SyntaxNormalizer.normalizedInstanceValue input)))
  simpa [Function.comp_def] using Classical.choice composed

/-- Exact raw guard used by the total HAM-CYCLE-to-TSP machine. -/
def validPass (input : List CliqueSym) : Bool :=
  RawWellFormed.rawWellFormedPass input && rawTargetEqualityPass input

/-- The raw guard accepts exactly normalized well-formed HAM-CYCLE headers. -/
theorem validPass_eq_true_iff (input : List CliqueSym) :
    validPass input = true ↔
      (SyntaxNormalizer.normalizedInstanceValue input).WellFormed ∧
      (SyntaxNormalizer.normalizedInstanceValue input).targetSize =
        (SyntaxNormalizer.normalizedInstanceValue input).vertexCount := by
  let I := SyntaxNormalizer.normalizedInstanceValue input
  have hwell := RawWellFormed.rawWellFormedPass_eq_true_iff input
  have heq := targetEqualityCheck_encode_iff ([] : List CliqueSym) I
  have htarget : rawTargetEqualityPass input = true ↔
      ¬I.targetSize < I.vertexCount := by
    simpa [rawTargetEqualityPass, graphTargetEqualityPass, I] using heq
  rw [validPass, Bool.and_eq_true, hwell, htarget]
  change (I.WellFormed ∧ ¬I.targetSize < I.vertexCount) ↔
    (I.WellFormed ∧ I.targetSize = I.vertexCount)
  constructor
  · rintro ⟨hI, hnotlt⟩
    exact ⟨hI, Nat.le_antisymm hI.1 (Nat.le_of_not_gt hnotlt)⟩
  · rintro ⟨hI, htargetEq⟩
    exact ⟨hI, by omega⟩

/-- One fixed polynomial-time TM2 computes the complete raw validity guard. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id TM2Comp.boolEncoding validPass := by
  exact TM2AndOr.andOrComputableInPolyTime
    RawWellFormed.computableInPolyTime
    rawTargetEqualityComputableInPolyTime Bool.and

end CLRS.Chapter34.Turing.TSPReduction.RawValidity
