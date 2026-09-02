import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Runtime

/-!
# Certificate pair-row generator: semantic output

The reusable occurrence controller emits a serialized edge stream.  This
module exposes the corresponding list of vertex pairs, so later verifier
stages can consume it through the canonical edge encoder rather than through
an opaque list of tape symbols.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

/-- Pair contributed by one compatible prior row. -/
def compatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) : List (Nat × Nat) :=
  if TMClique.indexedOccurrencesCompatibleCode current prior then
    [(prior.2, current.2)]
  else []

/-- Explicit pair family contributed by one outer iteration. -/
def compatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List (Nat × Nat) :=
  priors.flatMap (compatibleOccurrencePair current)

/-- Explicit pair family accumulated over every outer iteration. -/
def compatibleOccurrencePairIterations :
    List (IndexedOccurrence × Nat) → List (Nat × Nat)
  | [] => []
  | current :: priors =>
      compatibleOccurrencePairIterations priors ++
        compatibleOccurrencePairs current priors.reverse

theorem encodeCompatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) :
    TMClique.encodeCompatibleOccurrenceEdge current prior =
      (compatibleOccurrencePair current prior).flatMap encodeCliqueEdge := by
  cases hcompatible :
      TMClique.indexedOccurrencesCompatibleCode current prior <;>
    simp [TMClique.encodeCompatibleOccurrenceEdge,
      compatibleOccurrencePair, hcompatible]

theorem encodeCompatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceEdges current priors =
      (compatibleOccurrencePairs current priors).flatMap encodeCliqueEdge := by
  unfold TMClique.encodeCompatibleOccurrenceEdges compatibleOccurrencePairs
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro prior _
  exact encodeCompatibleOccurrencePair current prior

theorem encodeCompatibleOccurrencePairIterations
    (entries : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceIterations entries =
      (compatibleOccurrencePairIterations entries).flatMap
        encodeCliqueEdge := by
  induction entries with
  | nil => rfl
  | cons current priors ih =>
      simp only [TMClique.encodeCompatibleOccurrenceIterations,
        compatibleOccurrencePairIterations, List.flatMap_append]
      rw [ih, encodeCompatibleOccurrencePairs]

/-- Semantic list of all raw vertex pairs generated from a certificate. -/
def certificateRawPairs (vertices : List Nat) : List (Nat × Nat) :=
  compatibleOccurrencePairIterations (certificatePairEntries vertices).reverse

/-- The existing physical pair stream is the canonical encoding of the
semantic raw pair family. -/
theorem encodeCertificatePairIterations_eq (vertices : List Nat) :
    encodeCertificatePairIterations vertices =
      (certificateRawPairs vertices).flatMap encodeCliqueEdge := by
  exact encodeCompatibleOccurrencePairIterations _

/-- The fixed pair generator exposed at the semantic list boundary. -/
noncomputable def rawPairs_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      certificateRawPairs := by
  let pairs := pairIterations_computableInPolyTime
  exact
    { tm := pairs.tm
      inputAlphabet := pairs.inputAlphabet
      outputAlphabet := pairs.outputAlphabet
      time := pairs.time
      outputsFun := fun vertices => by
        simpa [encodeCertificatePairIterations_eq] using
          pairs.outputsFun vertices }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
