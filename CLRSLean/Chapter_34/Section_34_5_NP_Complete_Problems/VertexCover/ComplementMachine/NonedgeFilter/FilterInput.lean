import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Answers
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# VERTEX-COVER complement machine: aligned filter input

Candidate edge records are reversed before being stored on the filter work
stack.  A fixed-pair separator then precedes the pointwise answer bits, which
use two reserved `CliqueSym` tags.  Consequently the first answer is aligned
with the first candidate record when the work stack is popped.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

/-- Reserved tags outside the four-symbol edge-record grammar. -/
def bitSymbol : Bool → CliqueSym
  | false => .certificateMark
  | true => .instanceMark

@[simp] theorem bitSymbol_injective : Function.Injective bitSymbol := by
  intro left right h
  cases left <;> cases right <;> simp [bitSymbol] at h ⊢

def candidateReverseStream (I : CliqueInstance) : List CliqueSym :=
  (candidateStream I).reverse

def taggedMembershipStream (I : CliqueInstance) : List CliqueSym :=
  (membershipBits I).map bitSymbol

/-- Left paired branch, including its unique `none` separator. -/
def candidateReversePairLeft (I : CliqueInstance) :
    List (Option CliqueSym) :=
  OptionPairLeft.format (candidateReverseStream I)

/-- Tagged answer branch of the paired stream. -/
def taggedMembershipPairRight (I : CliqueInstance) :
    List (Option CliqueSym) :=
  (taggedMembershipStream I).map some

/-- Concrete input to the final fixed nonedge-selection controller. -/
def filterInput (I : CliqueInstance) : List (Option CliqueSym) :=
  pairEncoding (candidateReverseStream I) (taggedMembershipStream I)

noncomputable def candidateReverseStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      candidateReverseStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    candidateStreamComputableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym))
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [candidateReverseStream, Function.comp_def] using output }

noncomputable def taggedMembershipStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      taggedMembershipStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    membershipBitsComputableInPolyTime
    (listMap_computableInPolyTime bitSymbol)
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [taggedMembershipStream, Function.comp_def] using output }

noncomputable def candidateReversePairLeftComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      candidateReversePairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    candidateReverseStreamComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  exact Classical.choice composed

noncomputable def taggedMembershipPairRightComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      taggedMembershipPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    taggedMembershipStreamComputableInPolyTime
    (AdjacencyPipeline.someMapComputableInPolyTime CliqueSym)
  exact Classical.choice composed

/-- A fixed polynomial-time TM2 assembles the exact aligned filter input from
the original canonical graph string. -/
noncomputable def filterInputComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id filterInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    AdjacencyPipeline.encodeOptionCliqueSymPair
    AdjacencyPipeline.decodeOptionCliqueSymPair
    AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    candidateReversePairLeftComputableInPolyTime
    taggedMembershipPairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        have heq : candidateReversePairLeft I ++
              taggedMembershipPairRight I = filterInput I := by
          simp [candidateReversePairLeft, taggedMembershipPairRight,
            filterInput, OptionPairLeft.format, pairEncoding,
            List.append_assoc]
        rw [heq] at output
        simpa using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
