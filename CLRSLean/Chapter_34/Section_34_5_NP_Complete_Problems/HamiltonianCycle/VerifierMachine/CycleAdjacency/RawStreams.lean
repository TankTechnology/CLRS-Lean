import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CyclePairs
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams

/-!
# HAM-CYCLE verifier: raw cycle-query and graph streams

The existing total certificate/graph canonicalizers are reused unchanged.
Only the CLIQUE all-pairs branch is replaced by the verified HAM consecutive-
and-closing pair generator.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency

open PolyBuilder
open _root_.Turing

abbrev RawInput := GeneralCliqueVerifier.AdjacencyPipeline.RawInput

def rawEncoding (input : RawInput) : List (Option CliqueSym) :=
  GeneralCliqueVerifier.AdjacencyPipeline.rawEncoding input

def rawVertices (input : RawInput) : List Nat :=
  GeneralCliqueVerifier.AdjacencyPipeline.rawVertices input

def rawInstance (input : RawInput) : CliqueInstance :=
  GeneralCliqueVerifier.AdjacencyPipeline.rawInstance input

/-- Consecutive path pairs and the closing pair from the total decoded
certificate. -/
def rawCyclePairs (input : RawInput) : List (Nat × Nat) :=
  CyclePairs.cyclePairs (rawVertices input)

/-- Canonically oriented cycle-edge queries. -/
def rawQueries (input : RawInput) : List (Nat × Nat) :=
  (rawCyclePairs input).map GeneralCliqueVerifier.QueryNormalizer.normalizeQuery

def rawQueryStream (input : RawInput) : List CliqueSym :=
  (rawQueries input).flatMap encodeCliqueEdge

def rawGraphStream (input : RawInput) : List CliqueSym :=
  encodeCliqueInstance (rawInstance input)

noncomputable def rawCyclePairsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
      rawCyclePairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    GeneralCliqueVerifier.AdjacencyPipeline.rawVerticesComputableInPolyTime
    CyclePairs.pairsComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding
    (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
    (fun input => CyclePairs.cyclePairs (rawVertices input))
  exact Classical.choice composed

noncomputable def rawQueriesComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
      rawQueries := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawCyclePairsComputableInPolyTime
    GeneralCliqueVerifier.QueryNormalizer.normalizer_computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding
    (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
    (fun input => (rawCyclePairs input).map
      GeneralCliqueVerifier.QueryNormalizer.normalizeQuery)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def rawQueryStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rawQueryStream := by
  let queries := rawQueriesComputableInPolyTime
  exact
    { tm := queries.tm
      inputAlphabet := queries.inputAlphabet
      outputAlphabet := queries.outputAlphabet
      time := queries.time
      outputsFun := fun input => by
        simpa [rawQueryStream] using queries.outputsFun input }

noncomputable def rawGraphStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rawGraphStream := by
  let graph :=
    GeneralCliqueVerifier.AdjacencyPipeline.rawGraphStreamComputableInPolyTime
  exact
    { tm := graph.tm
      inputAlphabet := graph.inputAlphabet
      outputAlphabet := graph.outputAlphabet
      time := graph.time
      outputsFun := fun input => by
        simpa [rawEncoding, rawGraphStream, rawInstance,
          GeneralCliqueVerifier.AdjacencyPipeline.rawGraphStream] using
          graph.outputsFun input }

def queryPairLeft (input : RawInput) : List (Option CliqueSym) :=
  OptionPairLeft.format (rawQueryStream input)

def graphPairRight (input : RawInput) : List (Option CliqueSym) :=
  (rawGraphStream input).map some

noncomputable def queryPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id queryPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawQueryStreamComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => OptionPairLeft.format (rawQueryStream input))
  exact Classical.choice composed

noncomputable def graphPairRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id graphPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawGraphStreamComputableInPolyTime
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => (rawGraphStream input).map some)
  exact Classical.choice composed

def batchInputStream (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding (rawQueryStream input) (rawGraphStream input)

/-- A fixed polynomial-time TM2 assembles the normalized cycle queries and
canonical graph into the shared batch-lookup input format. -/
noncomputable def batchInputStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id batchInputStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    queryPairLeftComputableInPolyTime graphPairRightComputableInPolyTime
  have machine : TM2ComputableInPolyTime rawEncoding id
      (fun input => queryPairLeft input ++ graphPairRight input) := joined
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        have heq : queryPairLeft input ++ graphPairRight input =
            batchInputStream input := by
          simp [queryPairLeft, graphPairRight, batchInputStream,
            OptionPairLeft.format, pairEncoding, List.append_assoc]
        rw [heq] at output
        simpa using output }

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency
