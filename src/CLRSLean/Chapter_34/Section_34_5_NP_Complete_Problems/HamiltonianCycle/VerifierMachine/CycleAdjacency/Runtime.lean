import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CycleAdjacency.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Runtime

/-!
# HAM-CYCLE verifier: total raw cycle adjacency machine
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency

open _root_.Turing

def batchInput (input : RawInput) : List (Nat × Nat) × CliqueInstance :=
  (rawQueries input, rawInstance input)

def batchEncoding (input : List (Nat × Nat) × CliqueInstance) :
    List (Option CliqueSym) :=
  pairEncoding (input.1.flatMap encodeCliqueEdge)
    (encodeCliqueInstance input.2)

theorem batchInputStream_eq_encoding (input : RawInput) :
    batchInputStream input = batchEncoding (batchInput input) := by
  rfl

noncomputable def batchInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding batchEncoding batchInput := by
  let stream := batchInputStreamComputableInPolyTime
  exact
    { tm := stream.tm
      inputAlphabet := stream.inputAlphabet
      outputAlphabet := stream.outputAlphabet
      time := stream.time
      outputsFun := fun input => by
        have output := stream.outputsFun input
        rw [batchInputStream_eq_encoding] at output
        simpa only [id_eq] using output }

/-- Total Boolean result.  Empty decoded certificates yield `true` here; the
independent minimum-size and cardinality checks reject them in the final
verifier conjunction. -/
def rawCycleAdjacencyCheck (input : RawInput) : Bool :=
  GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool
    (rawInstance input) (rawQueries input)

/-- A fixed polynomial-time TM2 checks every generated cycle edge against
the normalized graph edge table. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      rawCycleAdjacencyCheck := by
  let batch : TM2ComputableInPolyTime batchEncoding TM2Comp.boolEncoding
      (fun input : List (Nat × Nat) × CliqueInstance =>
        GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool
          input.2 input.1) := by
    change TM2ComputableInPolyTime
      (fun input : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (input.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance input.2))
      TM2Comp.boolEncoding
      (fun input => GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool
        input.2 input.1)
    exact GeneralCliqueVerifier.BatchEdgeLookup.batchComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInputComputableInPolyTime batch
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool
      (rawInstance input) (rawQueries input))
  simpa [batchInput, Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency
