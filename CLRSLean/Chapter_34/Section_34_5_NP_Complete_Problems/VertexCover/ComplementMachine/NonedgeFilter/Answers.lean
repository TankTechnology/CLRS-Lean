import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Input
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DropHead

/-!
# VERTEX-COVER complement machine: pointwise source-edge answers

The reusable batch lookup emits one aggregate bit followed by one membership
bit for every candidate pair.  Dropping the aggregate yields an answer stream
aligned exactly with `candidatePairs`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

def lookupResults (I : CliqueInstance) : List Bool :=
  BatchEdgeLookup.batchResultStream I (candidatePairs I)

def membershipBits (I : CliqueInstance) : List Bool :=
  BatchEdgeLookup.queryMembershipBits I (candidatePairs I)

@[simp] theorem membershipBits_length (I : CliqueInstance) :
    (membershipBits I).length = (candidatePairs I).length := by
  simp [membershipBits, BatchEdgeLookup.queryMembershipBits]

theorem lookupResults_eq (I : CliqueInstance) :
    lookupResults I =
      BatchEdgeLookup.queriesInEdgesBool I (candidatePairs I) ::
        membershipBits I := by
  rfl

theorem dropHead_lookupResults (I : CliqueInstance) :
    DropHead.stream (lookupResults I) = membershipBits I := by
  rfl

noncomputable def lookupResultsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id lookupResults := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInputComputableInPolyTime
    BatchEdgeLookup.batchResultsComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, lookupResults] using output }

/-- Fixed polynomial-time computation of the candidate-aligned membership
bit stream from the original graph input. -/
noncomputable def membershipBitsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id membershipBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    lookupResultsComputableInPolyTime
    (DropHead.computableInPolyTime Bool)
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, dropHead_lookupResults] using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
