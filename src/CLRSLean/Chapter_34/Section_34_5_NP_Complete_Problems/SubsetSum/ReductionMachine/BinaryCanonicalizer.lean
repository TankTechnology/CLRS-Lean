import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.BinaryBlocks
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Fixed binary canonicalizer for the SUBSET-SUM reduction

This two-state transducer drops leading zeroes from a big-endian fixed-width
word and emits the unique one-bit zero representation when the whole input is
zero.  It is the final pass from block output to the repository's canonical
natural-number codec.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Finite-state streaming specification.  `started` records whether the
first one bit has already been seen. -/
def binaryCanonicalizerSpec : StatefulFlatMapSpec Bool Bool Bool where
  initial := false
  action started bit :=
    if started then ([bit], true)
    else if bit then ([true], true)
    else ([], false)
  finish started := if started then [] else [false]

def binaryCanonicalizer (bits : List Bool) : List Bool :=
  rewriteStatefulFlatMap binaryCanonicalizerSpec bits

private theorem binaryCanonicalizerFrom_started (bits : List Bool) :
    rewriteStatefulFlatMapFrom binaryCanonicalizerSpec true bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [bit] ++
        rewriteStatefulFlatMapFrom binaryCanonicalizerSpec true bits =
          bit :: bits
      simp [ih]

theorem binaryCanonicalizer_eq (bits : List Bool) :
    binaryCanonicalizer bits = canonicalizeBinaryBits bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit
      · simpa [binaryCanonicalizer, rewriteStatefulFlatMap,
          rewriteStatefulFlatMapFrom, binaryCanonicalizerSpec,
          canonicalizeBinaryBits] using ih
      · change [true] ++
          rewriteStatefulFlatMapFrom binaryCanonicalizerSpec true bits =
            true :: bits
        simp [binaryCanonicalizerFrom_started]

/-- A genuine fixed TM2 performs binary canonicalization in polynomial time. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id binaryCanonicalizer :=
  statefulFlatMap_computableInPolyTime binaryCanonicalizerSpec

end CLRS.Chapter34.Turing.SubsetSumReduction
