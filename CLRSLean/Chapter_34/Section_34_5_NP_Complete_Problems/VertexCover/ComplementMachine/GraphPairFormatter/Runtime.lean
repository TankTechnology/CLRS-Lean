import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.GraphPairFormatter.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Empty-certificate graph-pair formatter: fixed polynomial-time TM2
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GraphPairFormatter

open _root_.Turing
open PolyBuilder
open WellFormedGuard

/-- A fixed machine computes the empty-certificate graph-pair format by
reverse, existing left-pair formatting, and reverse. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id format := by
  let first := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (reverse_computableInPolyTime (Γ := CliqueSym))
    (OptionPairLeft.computableInPolyTime CliqueSym)
  let second := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice first)
    (reverse_computableInPolyTime (Γ := Option CliqueSym))
  change TM2ComputableInPolyTime id id
    (fun input => (OptionPairLeft.format input.reverse).reverse)
  simpa [Function.comp_def] using Classical.choice second

/-- Repackage the same controller over typed canonical graph encodings.  Its
semantic output is the canonical graph string, encoded for the next guard as
an empty-certificate pair. -/
noncomputable def typedComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance graphPairEncoding
      encodeCliqueInstance where
  tm := computableInPolyTime.tm
  inputAlphabet := computableInPolyTime.inputAlphabet
  outputAlphabet := computableInPolyTime.outputAlphabet
  time := computableInPolyTime.time
  outputsFun := fun I => by
    have output := computableInPolyTime.outputsFun (encodeCliqueInstance I)
    rw [format_eq_graphPairEncoding] at output
    exact output

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GraphPairFormatter
