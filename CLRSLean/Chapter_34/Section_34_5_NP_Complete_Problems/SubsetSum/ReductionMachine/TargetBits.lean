import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.BinaryCanonicalizer
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.TargetBlockStream
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# Canonical binary target generated from raw CNF input

The block controller emits little-endian columns.  A verified reversal and
the fixed leading-zero canonicalizer turn that stream into the repository's
canonical big-endian natural-number representation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

def targetBits (input : List CNFSym) : List Bool :=
  binaryCanonicalizer (targetPackedBitsLE input).reverse

theorem targetBits_eq (input : List CNFSym) :
    targetBits input = reductionTargetBits (decodeCNF input) := by
  rw [targetBits, binaryCanonicalizer_eq, targetPackedBitsLE_eq]
  rfl

/-- A fixed polynomial-time TM2 computes the canonical binary target directly
from arbitrary raw CNF syntax. -/
noncomputable def targetBits_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetBits := by
  let reversedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      targetPackedBitsLE_computableInPolyTime
      (reverse_computableInPolyTime (Γ := Bool))
  let reversed := Classical.choice reversedExists
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reversed computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => binaryCanonicalizer (targetPackedBitsLE input).reverse)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction
