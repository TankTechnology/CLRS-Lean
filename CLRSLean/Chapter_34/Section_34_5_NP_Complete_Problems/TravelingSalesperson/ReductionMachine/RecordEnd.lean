import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Codec
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-! # Fixed final TSP record terminator -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.RecordEnd

open PolyBuilder
open _root_.Turing

def spec : StatefulFlatMapSpec Unit CliqueSym TSPSym where
  initial := ()
  action := fun _ _ => ([], ())
  finish := fun _ => [.recordEnd]

def physical (input : List CliqueSym) : List TSPSym :=
  rewriteStatefulFlatMap spec input

theorem physical_eq (input : List CliqueSym) :
    physical input = [.recordEnd] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      unfold physical rewriteStatefulFlatMap
      rw [rewriteStatefulFlatMapFrom]
      change rewriteStatefulFlatMapFrom spec () input = _
      simpa [physical, rewriteStatefulFlatMap] using ih

def stream (_ : CliqueInstance) : List TSPSym := [.recordEnd]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id stream := by
  let raw : TM2ComputableInPolyTime
      (id : List CliqueSym → List CliqueSym)
      (id : List TSPSym → List TSPSym) physical :=
    statefulFlatMap_computableInPolyTime spec
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun I => by
        have output := raw.outputsFun (encodeCliqueInstance I)
        rw [physical_eq] at output
        simpa [stream] using output }

end CLRS.Chapter34.Turing.TSPReduction.RecordEnd
