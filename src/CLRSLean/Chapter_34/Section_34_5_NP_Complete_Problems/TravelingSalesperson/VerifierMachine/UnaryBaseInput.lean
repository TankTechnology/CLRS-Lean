import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.UnaryCertificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.StructuralChecks
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Header
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CertificateNodup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# Decision-TSP verifier: reusable unary-certificate checks

This adapter turns a unary TSP tour certificate into the exact raw format
expected by the already verified general-CLIQUE base passes.  Its dummy graph
has no edges and repeats the certificate-field count in both unary header
fields.  Consequently the reused checks decide certificate syntax and vertex
range; the HAM-CYCLE duplicate pass then decides `List.Nodup`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.UnaryBaseInput

open _root_.Turing
open PolyBuilder

abbrev RawInput := StructuralChecks.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  StructuralChecks.rawEncoding

def ticksToClique (ticks : List Bool) : List CliqueSym :=
  ticks.map fun _ => .tick

def emptyInstance (count : Nat) : CliqueInstance :=
  { vertexCount := count, targetSize := count, edges := [] }

def certificateCount (input : RawInput) : Nat :=
  (FieldCount.certificateTicks input.1).length

def dummyInstance (input : RawInput) : CliqueInstance :=
  emptyInstance (certificateCount input)

def cliqueCertificate (certificate : List TSPSym) : List CliqueSym :=
  UnaryCertificate.toCliqueCertificate certificate

def dummyGraph (certificate : List TSPSym) : List CliqueSym :=
  HamiltonianCycle.ReductionMachine.Header.headerFromCount
    (ticksToClique (FieldCount.certificateTicks certificate))

def baseInput (input : RawInput) : List CliqueSym × List CliqueSym :=
  (cliqueCertificate input.1, dummyGraph input.1)

private theorem certificateTicks_encodeVertex (vertex : Nat) :
    FieldCount.certificateTicks (UnaryCertificate.encodeVertex vertex) =
      [true] := by
  simp [FieldCount.certificateTicks, UnaryCertificate.encodeVertex]

private theorem certificateTicks_append (left right : List TSPSym) :
    FieldCount.certificateTicks (left ++ right) =
      FieldCount.certificateTicks left ++
        FieldCount.certificateTicks right := by
  simp [FieldCount.certificateTicks, List.flatMap_append]

@[simp] theorem certificateTicks_encode (vertices : List Nat) :
    FieldCount.certificateTicks (UnaryCertificate.encode vertices) =
      List.replicate vertices.length true := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      rw [UnaryCertificate.encode]
      change FieldCount.certificateTicks
          (UnaryCertificate.encodeVertex vertex ++
            vertices.flatMap UnaryCertificate.encodeVertex) = _
      rw [certificateTicks_append, certificateTicks_encodeVertex]
      have htail :
          FieldCount.certificateTicks
              (vertices.flatMap UnaryCertificate.encodeVertex) =
            List.replicate vertices.length true := by
        simpa [UnaryCertificate.encode, FieldCount.certificateTicks] using ih
      rw [htail]
      simp [List.replicate_succ]

private theorem ticksToClique_replicate (count : Nat) :
    ticksToClique (List.replicate count true) =
      List.replicate count CliqueSym.tick := by
  simp [ticksToClique]

private theorem ticksToClique_eq_replicate (ticks : List Bool) :
    ticksToClique ticks = List.replicate ticks.length CliqueSym.tick := by
  simp [ticksToClique]

private theorem replicate_ticks_append (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ suffix =
      prependCliqueTicks count suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, prependCliqueTicks]
      exact congrArg (List.cons .tick) ih

@[simp] theorem dummyGraph_encode (vertices : List Nat) :
    dummyGraph (UnaryCertificate.encode vertices) =
      encodeCliqueInstance (emptyInstance vertices.length) := by
  rw [dummyGraph, certificateTicks_encode, ticksToClique_replicate,
    _root_.CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Header.headerFromCount_eq]
  simp only [emptyInstance, encodeCliqueInstance, List.flatMap_nil]
  refine congrArg (List.cons CliqueSym.instanceMark) ?_
  rw [← replicate_ticks_append vertices.length
      (.fieldSep :: prependCliqueTicks vertices.length [.fieldSep])]
  rw [← replicate_ticks_append vertices.length [.fieldSep]]
  simp [List.append_assoc]

theorem dummyGraph_eq_encode (input : RawInput) :
    dummyGraph input.1 = encodeCliqueInstance (dummyInstance input) := by
  rw [dummyGraph, ticksToClique_eq_replicate,
    _root_.CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Header.headerFromCount_eq]
  simp only [dummyInstance, certificateCount, emptyInstance,
    encodeCliqueInstance, List.flatMap_nil]
  refine congrArg (List.cons CliqueSym.instanceMark) ?_
  rw [← replicate_ticks_append
      (FieldCount.certificateTicks input.1).length
      (.fieldSep :: prependCliqueTicks
        (FieldCount.certificateTicks input.1).length [.fieldSep])]
  rw [← replicate_ticks_append
      (FieldCount.certificateTicks input.1).length [.fieldSep]]
  simp [List.append_assoc]

@[simp] theorem baseInput_encode (vertices : List Nat) (data : TSPData) :
    baseInput (UnaryCertificate.encode vertices, encodeTSPData data) =
      (encodeCliqueCertificate vertices,
        encodeCliqueInstance (emptyInstance vertices.length)) := by
  simp [baseInput, cliqueCertificate,
    UnaryCertificate.toCliqueCertificate_encode]

private noncomputable def certificateProjection :
    TM2ComputableInPolyTime rawEncoding id Prod.fst := by
  let machine := PairFirstProjection.computableInPolyTime TSPSym
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa [rawEncoding, StructuralChecks.rawEncoding] using
          machine.outputsFun input }

private noncomputable def cliqueCertificateComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => cliqueCertificate input.1) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateProjection UnaryCertificate.toCliqueCertificateComputableInPolyTime
  simpa [cliqueCertificate, Function.comp_def] using Classical.choice composed

private noncomputable def certificateLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => OptionPairLeft.format (cliqueCertificate input.1)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    cliqueCertificateComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def ticksToCliqueComputableInPolyTime :
    TM2ComputableInPolyTime id id ticksToClique :=
  listMap_computableInPolyTime (fun _ : Bool => CliqueSym.tick)

private noncomputable def dummyGraphComputableFromCertificateInPolyTime :
    TM2ComputableInPolyTime id id dummyGraph := by
  let countExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    FieldCount.certificateTicksComputableInPolyTime
    ticksToCliqueComputableInPolyTime
  let headerExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice countExists)
    HamiltonianCycle.ReductionMachine.Header.headerFromCountComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun certificate =>
      HamiltonianCycle.ReductionMachine.Header.headerFromCount
        (ticksToClique (FieldCount.certificateTicks certificate)))
  simpa only [Function.comp_def] using Classical.choice headerExists

noncomputable def dummyGraphComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => dummyGraph input.1) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateProjection dummyGraphComputableFromCertificateInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

/-- Typed view of the same physical dummy-graph generator. -/
noncomputable def dummyInstanceComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding encodeCliqueInstance
      dummyInstance := by
  let machine := dummyGraphComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [dummyGraph_eq_encode input] at output
        exact output }

private noncomputable def graphRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => (dummyGraph input.1).map some) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    dummyGraphComputableInPolyTime
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  simpa [Function.comp_def] using Classical.choice composed

/-- A fixed polynomial-time machine builds the paired input consumed by both
reused CLIQUE/HAM-CYCLE certificate passes. -/
noncomputable def baseInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pair : List CliqueSym × List CliqueSym =>
        pairEncoding pair.1 pair.2)
      baseInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    certificateLeftComputableInPolyTime graphRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [baseInput, OptionPairLeft.format, pairEncoding,
          List.append_assoc] using output }

def baseCheck (input : RawInput) : Bool :=
  GeneralCliqueVerifier.BaseChecks.baseChecks
    (baseInput input).1 (baseInput input).2

noncomputable def baseCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding baseCheck := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    baseInputComputableInPolyTime
    GeneralCliqueVerifier.BaseChecks.baseChecksComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => GeneralCliqueVerifier.BaseChecks.baseChecks
      (baseInput input).1 (baseInput input).2)
  simpa only [Function.comp_def] using Classical.choice composed

@[simp] theorem baseCheck_encode_iff (vertices : List Nat) (data : TSPData) :
    baseCheck (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      ∀ vertex ∈ vertices, vertex < vertices.length := by
  rw [baseCheck, baseInput_encode,
    GeneralCliqueVerifier.BaseChecks.baseChecks_encode_iff]
  simp [GeneralCliqueVerifier.BaseChecks.BaseConditions, emptyInstance]

def nodupCheck (input : RawInput) : Bool :=
  HamiltonianCycle.VerifierMachine.CertificateNodup.nodupCheck
    (baseInput input)

noncomputable def nodupCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding nodupCheck := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    baseInputComputableInPolyTime
    HamiltonianCycle.VerifierMachine.CertificateNodup.nodupCheckComputableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input =>
      HamiltonianCycle.VerifierMachine.CertificateNodup.nodupCheck
        (baseInput input))
  simpa only [Function.comp_def] using Classical.choice composed

@[simp] theorem nodupCheck_encode_iff (vertices : List Nat) (data : TSPData) :
    nodupCheck (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      vertices.Nodup := by
  rw [nodupCheck, baseInput_encode]
  exact HamiltonianCycle.VerifierMachine.CertificateNodup.nodupCheck_eq_true_iff
    (encodeCliqueCertificate vertices)
    (encodeCliqueInstance (emptyInstance vertices.length)) vertices
    (decode_encodeCliqueCertificate vertices)

end CLRS.Chapter34.Turing.TSPVerifier.UnaryBaseInput
