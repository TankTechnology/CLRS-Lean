import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Ordinary.Core

/-!
# VERTEX-COVER to HAM-CYCLE: polynomial-time ordinary target
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary

open _root_.Turing
open PolyBuilder

private noncomputable def prefixComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      (fun I : VertexCoverInstance =>
        NondegeneratePrefix.stream (encodeVertexCoverInstance I)) := by
  let machine := NondegeneratePrefix.computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        simpa using machine.outputsFun (encodeVertexCoverInstance I) }

private noncomputable def selectorCliqueComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      (fun I : VertexCoverInstance =>
        SelectorClique.stream (encodeVertexCoverInstance I)) := by
  let machine := SelectorClique.computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        simpa using machine.outputsFun (encodeVertexCoverInstance I) }

/-- One fixed polynomial-time TM2 emits the complete nondegenerate target. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id stream := by
  let prefixChain := fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    prefixComputableInPolyTime Incidence.Chain.computableInPolyTime
  let withEndpoints := fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    prefixChain SelectorEndpoints.computableInPolyTime
  let complete := fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    withEndpoints selectorCliqueComputableInPolyTime
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun I => by
        simpa [stream, List.append_assoc] using complete.outputsFun I }

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary
