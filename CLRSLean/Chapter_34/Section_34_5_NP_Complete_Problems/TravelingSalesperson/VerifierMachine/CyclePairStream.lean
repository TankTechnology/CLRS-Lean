import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.UnaryBaseInput
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CycleAdjacency.RawStreams

/-!
# Decision-TSP verifier: cyclic tour-pair stream

The unary certificate adapter exposes an ordinary CLIQUE certificate.  This
module composes it with the verified HAM-CYCLE consecutive-pair controller,
obtaining every directed path edge plus the closing last-to-first edge.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.CyclePairStream

open _root_.Turing

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def cyclePairs (input : RawInput) : List (Nat × Nat) :=
  HamiltonianCycle.VerifierMachine.CycleAdjacency.rawCyclePairs
    (UnaryBaseInput.baseInput input)

def stream (input : RawInput) : List CliqueSym :=
  (cyclePairs input).flatMap encodeCliqueEdge

/-- A fixed polynomial-time machine emits the literal unary endpoint records
for all cyclic tour edges. -/
noncomputable def cyclePairsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
      cyclePairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    UnaryBaseInput.baseInputComputableInPolyTime
    HamiltonianCycle.VerifierMachine.CycleAdjacency.rawCyclePairsComputableInPolyTime
  change TM2ComputableInPolyTime UnaryBaseInput.rawEncoding
    (fun pairs : List (Nat × Nat) => pairs.flatMap encodeCliqueEdge)
    (fun input =>
      HamiltonianCycle.VerifierMachine.CycleAdjacency.rawCyclePairs
        (UnaryBaseInput.baseInput input))
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id stream := by
  let machine := cyclePairsComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa [stream] using machine.outputsFun input }

@[simp] theorem cyclePairs_encode (vertices : List Nat) (data : TSPData) :
    cyclePairs (UnaryCertificate.encode vertices, encodeTSPData data) =
      HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices := by
  simp [cyclePairs,
    HamiltonianCycle.VerifierMachine.CycleAdjacency.rawCyclePairs,
    HamiltonianCycle.VerifierMachine.CycleAdjacency.rawVertices,
    GeneralCliqueVerifier.AdjacencyPipeline.rawVertices,
    GeneralCliqueVerifier.Canonicalizer.certificateValue,
    decode_encodeCliqueCertificate]

@[simp] theorem stream_encode (vertices : List Nat) (data : TSPData) :
    stream (UnaryCertificate.encode vertices, encodeTSPData data) =
      HamiltonianCycle.VerifierMachine.CyclePairs.encodeCyclePairs vertices := by
  simp [stream,
    HamiltonianCycle.VerifierMachine.CyclePairs.encodeCyclePairs]

end CLRS.Chapter34.Turing.TSPVerifier.CyclePairStream
