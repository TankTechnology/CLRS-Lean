import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.CyclePairStream
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DropHead
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection

/-!
# Decision-TSP verifier: normalized cycle membership

The complete normalized pair family is queried against the normalized cyclic
tour edges.  The reused CLIQUE batch-lookup controller returns one membership
bit per matrix pair.  This avoids a new random-access weight-table machine.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.CycleMembership

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def candidatePairs (input : RawInput) : List (Nat × Nat) :=
  vertexCoverNormalizedPairs
    (UnaryBaseInput.dummyInstance input).vertexCount

def normalizedCyclePairs (input : RawInput) : List (Nat × Nat) :=
  (CyclePairStream.cyclePairs input).map QueryNormalizer.normalizeQuery

def cycleGraph (edges : List (Nat × Nat)) : CliqueInstance :=
  { vertexCount := 0, targetSize := 0, edges := edges }

def batchInput (input : RawInput) :
    List (Nat × Nat) × CliqueInstance :=
  (candidatePairs input, cycleGraph (normalizedCyclePairs input))

def membershipBits (input : RawInput) : List Bool :=
  GeneralCliqueVerifier.BatchEdgeLookup.queryMembershipBits
    (batchInput input).2 (batchInput input).1

noncomputable def candidatePairsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      candidatePairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    UnaryBaseInput.dummyInstanceComputableInPolyTime
    VertexCover.ComplementMachine.PairStream.computableInPolyTime
  change TM2ComputableInPolyTime UnaryBaseInput.rawEncoding
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun input => vertexCoverNormalizedPairs
      (UnaryBaseInput.dummyInstance input).vertexCount)
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def normalizedCyclePairsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      normalizedCyclePairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    CyclePairStream.cyclePairsComputableInPolyTime
    QueryNormalizer.normalizer_computableInPolyTime
  change TM2ComputableInPolyTime CyclePairStream.rawEncoding
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun input =>
      (CyclePairStream.cyclePairs input).map
        QueryNormalizer.normalizeQuery)
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def cycleGraphComputableFromEdgesInPolyTime :
    TM2ComputableInPolyTime
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      encodeCliqueInstance cycleGraph := by
  let packed :=
    HamiltonianCycle.VerifierMachine.CertificateNodup.packComputableInPolyTime
  let projectedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    packed (PairSecondProjection.computableInPolyTime CliqueSym)
  let machine := Classical.choice projectedExists
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun edges => by
        have output := machine.outputsFun edges
        simpa [Function.comp_def, cycleGraph,
          HamiltonianCycle.VerifierMachine.CertificateNodup.packedInput,
          HamiltonianCycle.VerifierMachine.CertificateNodup.queryGraph] using
          output }

private noncomputable def cycleGraphComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding encodeCliqueInstance
      (fun input => cycleGraph (normalizedCyclePairs input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedCyclePairsComputableInPolyTime
    cycleGraphComputableFromEdgesInPolyTime
  simpa only [Function.comp_def] using Classical.choice composed

private def candidateLeft (input : RawInput) : List (Option CliqueSym) :=
  OptionPairLeft.format
    ((candidatePairs input).flatMap encodeCliqueEdge)

private def graphRight (input : RawInput) : List (Option CliqueSym) :=
  (encodeCliqueInstance (cycleGraph (normalizedCyclePairs input))).map some

private noncomputable def candidateLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id candidateLeft := by
  let stream : TM2ComputableInPolyTime rawEncoding id
      (fun input => (candidatePairs input).flatMap encodeCliqueEdge) :=
    { tm := candidatePairsComputableInPolyTime.tm
      inputAlphabet := candidatePairsComputableInPolyTime.inputAlphabet
      outputAlphabet := candidatePairsComputableInPolyTime.outputAlphabet
      time := candidatePairsComputableInPolyTime.time
      outputsFun := fun input => by
        simpa using candidatePairsComputableInPolyTime.outputsFun input }
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch stream
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => OptionPairLeft.format
      ((candidatePairs input).flatMap encodeCliqueEdge))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def graphRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id graphRight := by
  let graph : TM2ComputableInPolyTime rawEncoding id
      (fun input =>
        encodeCliqueInstance (cycleGraph (normalizedCyclePairs input))) :=
    { tm := cycleGraphComputableInPolyTime.tm
      inputAlphabet := cycleGraphComputableInPolyTime.inputAlphabet
      outputAlphabet := cycleGraphComputableInPolyTime.outputAlphabet
      time := cycleGraphComputableInPolyTime.time
      outputsFun := fun input => by
        simpa using cycleGraphComputableInPolyTime.outputsFun input }
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch graph
    (AdjacencyPipeline.someMapComputableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input =>
      (encodeCliqueInstance
        (cycleGraph (normalizedCyclePairs input))).map some)
  simpa only [Function.comp_def] using Classical.choice composed

/-- Build the literal query/graph pair consumed by the reusable batch lookup. -/
noncomputable def batchInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pr : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (pr.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance pr.2))
      batchInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    AdjacencyPipeline.encodeOptionCliqueSymPair
    AdjacencyPipeline.decodeOptionCliqueSymPair
    AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    candidateLeftComputableInPolyTime graphRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [batchInput, candidateLeft, graphRight,
          OptionPairLeft.format, pairEncoding, List.append_assoc] using output }

private def lookupResults (input : RawInput) : List Bool :=
  GeneralCliqueVerifier.BatchEdgeLookup.batchResultStream
    (batchInput input).2 (batchInput input).1

private noncomputable def lookupResultsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id lookupResults := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInputComputableInPolyTime
    GeneralCliqueVerifier.BatchEdgeLookup.batchResultsComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding id
    (fun input =>
      GeneralCliqueVerifier.BatchEdgeLookup.batchResultStream
        (batchInput input).2 (batchInput input).1)
  simpa only [Function.comp_def] using Classical.choice composed

/-- Fixed polynomial-time pointwise cycle-membership stream, aligned with the
canonical normalized matrix-pair order. -/
noncomputable def membershipBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id membershipBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    lookupResultsComputableInPolyTime (DropHead.computableInPolyTime Bool)
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [Function.comp_def, lookupResults, membershipBits,
          GeneralCliqueVerifier.BatchEdgeLookup.batchResultStream,
          DropHead.stream] using output }

@[simp] theorem candidatePairs_encode (vertices : List Nat) (data : TSPData) :
    candidatePairs
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      vertexCoverNormalizedPairs vertices.length := by
  simp [candidatePairs, UnaryBaseInput.dummyInstance,
    UnaryBaseInput.certificateCount, UnaryBaseInput.emptyInstance]

@[simp] theorem normalizedCyclePairs_encode
    (vertices : List Nat) (data : TSPData) :
    normalizedCyclePairs
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
        QueryNormalizer.normalizeQuery := by
  simp [normalizedCyclePairs]

@[simp] theorem membershipBits_encode (vertices : List Nat) (data : TSPData) :
    membershipBits
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      (vertexCoverNormalizedPairs vertices.length).map fun edge =>
        decide (edge ∈
          (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
            QueryNormalizer.normalizeQuery) := by
  simp [membershipBits, batchInput, cycleGraph,
    GeneralCliqueVerifier.BatchEdgeLookup.queryMembershipBits]

end CLRS.Chapter34.Turing.TSPVerifier.CycleMembership
