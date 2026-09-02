import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Runtime

/-!
# General CLIQUE verifier: total raw adjacency machine

The stream producer is re-exposed at the typed batch-input boundary and then
composed with the fixed cubic lookup controller.  The resulting machine is
total on every raw certificate/instance pair.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline

open _root_.Turing

/-- Typed batch input computed from one arbitrary raw verifier input. -/
def batchInput (input : RawInput) : List (Nat × Nat) × CliqueInstance :=
  (rawQueries input, rawInstance input)

/-- Encoder used by the reusable batch lookup controller. -/
def batchEncoding (input : List (Nat × Nat) × CliqueInstance) :
    List (Option CliqueSym) :=
  pairEncoding (input.1.flatMap encodeCliqueEdge)
    (encodeCliqueInstance input.2)

theorem batchInputStream_eq_encoding (input : RawInput) :
    batchInputStream input = batchEncoding (batchInput input) := by
  rfl

/-- The literal stream producer, exposed at the typed boundary needed for
ordinary TM composition. -/
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

/-- Total Boolean adjacency result produced from raw verifier input. -/
def rawAdjacencyCheck (input : RawInput) : Bool :=
  BatchEdgeLookup.queriesInEdgesBool (rawInstance input) (rawQueries input)

/-- A fixed polynomial-time TM2 computes all certificate-pair edge lookups on
arbitrary raw verifier inputs. -/
noncomputable def rawAdjacencyCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      rawAdjacencyCheck := by
  let batch : TM2ComputableInPolyTime batchEncoding TM2Comp.boolEncoding
      (fun input : List (Nat × Nat) × CliqueInstance =>
        BatchEdgeLookup.queriesInEdgesBool input.2 input.1) := by
    change TM2ComputableInPolyTime
      (fun input : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (input.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance input.2))
      TM2Comp.boolEncoding
      (fun input => BatchEdgeLookup.queriesInEdgesBool input.2 input.1)
    exact BatchEdgeLookup.batchComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInputComputableInPolyTime batch
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => BatchEdgeLookup.queriesInEdgesBool
      (rawInstance input) (rawQueries input))
  simpa [batchInput, Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline
