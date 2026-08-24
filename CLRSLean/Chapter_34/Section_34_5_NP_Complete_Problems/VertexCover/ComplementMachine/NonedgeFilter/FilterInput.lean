import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Answers
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# VERTEX-COVER complement machine: aligned filter input

Candidate edge records are reversed before being stored on the filter work
stack.  The pointwise answer bits follow as two reserved `CliqueSym` tags.
Consequently the first answer is aligned with the first candidate record when
the work stack is popped.
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

/-- Concrete input to the final fixed nonedge-selection controller. -/
def filterInput (I : CliqueInstance) : List CliqueSym :=
  candidateReverseStream I ++ taggedMembershipStream I

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

/-- A fixed polynomial-time TM2 assembles the exact aligned filter input from
the original canonical graph string. -/
noncomputable def filterInputComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id filterInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    candidateReverseStreamComputableInPolyTime
    taggedMembershipStreamComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        simpa [filterInput] using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
