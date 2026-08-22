import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.GuardedHeader

/-!
# Concrete polynomial-time 3-CNF to general CLIQUE machine

The guarded instance header and canonical occurrence-edge suffix are generated
from the same raw CNF input and concatenated by the verified fixed-pair
same-input combinator.  Their concatenation is exactly the previously proved
semantic reduction map.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- The guarded header followed by the generated compatibility edges is
definitionally the canonical encoding of the guarded occurrence instance. -/
theorem threeCNFToGeneralCliqueMap_eq_header_edges (input : List CNFSym) :
    canonicalGuardedCliqueHeader input ++
        encodeOccurrenceCliqueEdges (decodeCNF input) =
      threeCNFToGeneralCliqueMap input := by
  rw [canonicalGuardedCliqueHeader_eq]
  unfold threeCNFToGeneralCliqueMap guardedOccurrenceCliqueInstance
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · simp only [hthree, ↓reduceIte]
    simp [encodeCliqueInstance, occurrenceCliqueInstance,
      encodeOccurrenceCliqueEdges, prependCliqueTicks_append,
      indexedOccurrences_length]
  · simp only [hthree, ↓reduceIte]
    simp [encodeCliqueInstance, occurrenceCliqueInstance,
      encodeOccurrenceCliqueEdges, prependCliqueTicks_append,
      indexedOccurrences_length]

/-- A fixed polynomial-time TM2 computes the exact raw 3-CNF-to-general-
CLIQUE reduction map. -/
noncomputable def threeCNFToGeneralCliqueComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      threeCNFToGeneralCliqueMap := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    canonicalGuardedCliqueHeader_computableInPolyTime
    canonicalOccurrenceCliqueEdges_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        rw [threeCNFToGeneralCliqueMap_eq_header_edges] at run
        simpa only [id_eq] using run }

/-- Named polynomial runtime of the concrete reduction machine, obtained by
the verified composition of normalization, guarded-header, row generation,
compatibility filtering, and fixed-pair concatenation phases. -/
noncomputable def threeCNFToGeneralCliqueRuntimePolynomial : Polynomial Nat :=
  threeCNFToGeneralCliqueComputableInPolyTime.time

/-- The fixed compiled-and-composed reduction machine. -/
noncomputable def threeCNFToGeneralCliqueMachine : _root_.Turing.FinTM2 :=
  threeCNFToGeneralCliqueComputableInPolyTime.tm

/-- Direct exact-output and named-runtime contract for the fixed reduction
machine on every raw source string. -/
theorem threeCNFToGeneralCliqueMachine_outputs (input : List CNFSym) :
    Nonempty (_root_.Turing.TM2OutputsInTime
      threeCNFToGeneralCliqueMachine
      (List.map
        threeCNFToGeneralCliqueComputableInPolyTime.inputAlphabet.invFun input)
      (some (List.map
        threeCNFToGeneralCliqueComputableInPolyTime.outputAlphabet.invFun
        (threeCNFToGeneralCliqueMap input)))
      (threeCNFToGeneralCliqueRuntimePolynomial.eval input.length)) := by
  exact ⟨threeCNFToGeneralCliqueComputableInPolyTime.outputsFun input⟩

/-- The concrete occurrence construction is a polynomial-time many-one
reduction from raw 3-CNF satisfiability to honest general CLIQUE. -/
theorem threeCNFSat_reducible_to_generalCLIQUE :
    PolyTimeReducible ThreeCNFSat GeneralCLIQUE := by
  refine ⟨threeCNFToGeneralCliqueMap,
    ⟨threeCNFToGeneralCliqueComputableInPolyTime⟩, ?_⟩
  intro input
  exact (threeCNFToGeneralCliqueMap_mem_iff input).symm

end TMClique
end Turing
end Chapter34
end CLRS
