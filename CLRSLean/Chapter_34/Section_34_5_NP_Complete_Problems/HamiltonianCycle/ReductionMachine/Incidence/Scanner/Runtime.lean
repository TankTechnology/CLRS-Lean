import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Run
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Length

/-!
# HAM-CYCLE incidence scanner: polynomial runtime and public composition
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder
open _root_.Turing

private theorem leftFieldSteps_le (remaining saved candidate : Nat) :
    leftFieldSteps remaining saved candidate ≤
      6 * (remaining + saved + candidate + 1) := by
  induction candidate generalizing remaining saved with
  | zero =>
      simp [leftFieldSteps]
      omega
  | succ candidate ih =>
      cases remaining with
      | zero =>
          have h := ih 0 saved
          simp [leftFieldSteps] at h ⊢
          omega
      | succ remaining =>
          have h := ih remaining (saved + 1)
          simp [leftFieldSteps] at h ⊢
          omega

private theorem rightFieldSteps_le (remaining saved candidate : Nat) :
    rightFieldSteps remaining saved candidate ≤
      6 * (remaining + saved + candidate + 1) := by
  induction candidate generalizing remaining saved with
  | zero =>
      simp [rightFieldSteps]
      omega
  | succ candidate ih =>
      cases remaining with
      | zero =>
          have h := ih 0 saved
          simp [rightFieldSteps] at h ⊢
          omega
      | succ remaining =>
          have h := ih remaining (saved + 1)
          simp [rightFieldSteps] at h ⊢
          omega

private theorem emitOccurrenceSteps_le (occurrence : Nat) (side : Bool) :
    emitOccurrenceSteps occurrence side ≤ 5 * (occurrence + 1) := by
  cases side <;> simp [emitOccurrenceSteps] <;> omega

private theorem edges_length_le_encoding (edges : List (Nat × Nat)) :
    edges.length ≤ cliqueEdgesEncodingLength edges := by
  induction edges with
  | nil => simp [cliqueEdgesEncodingLength]
  | cons edge edges ih =>
      simp [cliqueEdgesEncodingLength] at ih ⊢
      omega

private theorem edgesSteps_le_of_bound (query occurrence bound : Nat)
    (edges : List (Nat × Nat))
    (hquery : query ≤ bound)
    (hoccurrence : occurrence + edges.length ≤ bound)
    (hencoding : cliqueEdgesEncodingLength edges ≤ bound) :
    edgesSteps query occurrence edges ≤
      32 * edges.length * (bound + 1) + 1 := by
  induction edges generalizing occurrence with
  | nil => simp [edgesSteps]
  | cons edge edges ih =>
      have hencoding' :
          edge.1 + edge.2 + 3 + cliqueEdgesEncodingLength edges ≤
            bound := by
        simpa [cliqueEdgesEncodingLength, Nat.add_assoc] using hencoding
      have hedgeLeft : edge.1 ≤ bound := by omega
      have hedgeRight : edge.2 ≤ bound := by omega
      have htailEncoding : cliqueEdgesEncodingLength edges ≤ bound := by
        omega
      have htailOccurrence : occurrence + 1 + edges.length ≤ bound := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hoccurrence
      have hrest := ih (occurrence + 1) htailOccurrence htailEncoding
      have hleft := leftFieldSteps_le query 0 edge.1
      have hright := rightFieldSteps_le query 0 edge.2
      have hocc : occurrence ≤ bound := by omega
      have hemitFalse := emitOccurrenceSteps_le occurrence false
      have hemitTrue := emitOccurrenceSteps_le occurrence true
      have hleftBound : leftFieldSteps query 0 edge.1 ≤
          12 * (bound + 1) := by omega
      have hrightBound : rightFieldSteps query 0 edge.2 ≤
          12 * (bound + 1) := by omega
      have hemitFalseBound : emitOccurrenceSteps occurrence false ≤
          5 * (bound + 1) := by omega
      have hemitTrueBound : emitOccurrenceSteps occurrence true ≤
          5 * (bound + 1) := by omega
      have hmul : 32 * (edges.length + 1) * (bound + 1) + 1 =
          32 * (bound + 1) +
            (32 * edges.length * (bound + 1) + 1) := by ring
      by_cases hleftMatch : edge.1 = query
      · have hleftBound' : leftFieldSteps query 0 query ≤
            12 * (bound + 1) := by
          simpa [hleftMatch] using hleftBound
        simp only [edgesSteps, hleftMatch, if_pos]
        simp only [List.length_cons]
        rw [hmul]
        omega
      · by_cases hrightMatch : edge.2 = query
        · have hrightBound' : rightFieldSteps query 0 query ≤
              12 * (bound + 1) := by
            simpa [hrightMatch] using hrightBound
          simp only [edgesSteps, hleftMatch, hrightMatch, if_false, if_pos]
          simp only [List.length_cons]
          rw [hmul]
          omega
        · simp only [edgesSteps, hleftMatch, hrightMatch, if_false]
          simp only [List.length_cons]
          rw [hmul]
          omega

private theorem iterationSteps_le (query : Nat) (I : VertexCoverInstance)
    (hquery : query < I.vertexCount) :
    iterationSteps query I ≤
      40 * ((encodeVertexCoverInstance I).length + 1) ^ 2 := by
  let graphLength := (encodeVertexCoverInstance I).length
  have hlength : graphLength =
      I.vertexCount + I.targetSize + 3 +
        cliqueEdgesEncodingLength I.edges := by
    simpa [graphLength] using encodeCliqueInstance_length I
  have hvertex : I.vertexCount ≤ graphLength := by omega
  have hquery' : query ≤ graphLength := by omega
  have hedgeEncoding : cliqueEdgesEncodingLength I.edges ≤ graphLength := by
    omega
  have hedgeCount : I.edges.length ≤ graphLength := by
    exact (edges_length_le_encoding I.edges).trans hedgeEncoding
  have hedges := edgesSteps_le_of_bound query 0 graphLength I.edges
    hquery' (by simpa using hedgeCount) hedgeEncoding
  have hheader : headerSteps I ≤ graphLength := by
    simp [headerSteps, graphLength, encodeCliqueInstance]
    omega
  unfold iterationSteps querySteps
  change 2 * query + 2 + headerSteps I + edgesSteps query 0 I.edges +
      (query + I.edges.length + graphLength + 6) ≤ _
  nlinarith

private theorem iterationsSteps_le (queries : List Nat)
    (I : VertexCoverInstance)
    (hqueries : ∀ query ∈ queries, query < I.vertexCount) :
    iterationsSteps queries I ≤
      40 * queries.length * ((encodeVertexCoverInstance I).length + 1) ^ 2 +
        (encodeVertexCoverInstance I).length + 8 := by
  induction queries with
  | nil => simp [iterationsSteps]
  | cons query queries ih =>
      have hquery : query < I.vertexCount := hqueries query (by simp)
      have htail : ∀ q ∈ queries, q < I.vertexCount := by
        intro q hq
        exact hqueries q (by simp [hq])
      have hfirst := iterationSteps_le query I hquery
      have hrest := ih htail
      simp only [iterationsSteps, List.length_cons]
      nlinarith

/-- The exact full scanner execution is bounded by one fixed cubic
polynomial in the shared paired-input length. -/
theorem scannerSteps_le (I : VertexCoverInstance) :
    scannerSteps I ≤
      60 * (Incidence.inputStream I).length.succ ^ 3 := by
  let graphLength := (encodeVertexCoverInstance I).length
  let inputLength := (Incidence.inputStream I).length
  let queryLength := (Incidence.vertexQueryStream I).length
  have hinput : queryLength + graphLength + 1 = inputLength := by
    simp [queryLength, graphLength, inputLength, Incidence.inputStream,
      pairEncoding, Nat.add_assoc, Nat.add_comm]
  have hqueries : ∀ query ∈ (List.range I.vertexCount).reverse,
      query < I.vertexCount := by
    intro query hquery
    simpa using hquery
  have hiters := iterationsSteps_le (List.range I.vertexCount).reverse I
    hqueries
  have hgraph : graphLength ≤ inputLength := by omega
  have hvertex : I.vertexCount ≤ graphLength := by
    dsimp [graphLength]
    rw [encodeCliqueInstance_length]
    omega
  have hqueryLength : queryLength + 2 ≤ inputLength + 1 := by omega
  have hiters' : iterationsSteps (List.range I.vertexCount).reverse I ≤
      40 * I.vertexCount * (graphLength + 1) ^ 2 + graphLength + 8 := by
    simpa [graphLength] using hiters
  have hcount : 40 * I.vertexCount * (graphLength + 1) ^ 2 ≤
      40 * (graphLength + 1) ^ 3 := by
    calc
      40 * I.vertexCount * (graphLength + 1) ^ 2 ≤
          40 * (graphLength + 1) * (graphLength + 1) ^ 2 := by
            exact Nat.mul_le_mul_right ((graphLength + 1) ^ 2)
              (Nat.mul_le_mul_left 40 (by omega))
      _ = 40 * (graphLength + 1) ^ 3 := by ring
  have hgraphCube : graphLength + 1 ≤ (graphLength + 1) ^ 3 := by
    have hsquare : 1 ≤ (graphLength + 1) ^ 2 := by
      exact Nat.one_le_pow' 2 graphLength
    calc
      graphLength + 1 = (graphLength + 1) * 1 := by omega
      _ ≤ (graphLength + 1) * (graphLength + 1) ^ 2 :=
        Nat.mul_le_mul_left _ hsquare
      _ = (graphLength + 1) ^ 3 := by ring
  have hitersCube : iterationsSteps (List.range I.vertexCount).reverse I ≤
      48 * (graphLength + 1) ^ 3 := by
    omega
  have hcube : (graphLength + 1) ^ 3 ≤ (inputLength + 1) ^ 3 := by
    exact Nat.pow_le_pow_left (by omega) 3
  have hitersInput : iterationsSteps (List.range I.vertexCount).reverse I ≤
      48 * (inputLength + 1) ^ 3 :=
    hitersCube.trans (Nat.mul_le_mul_left 48 hcube)
  have hinputCube : inputLength + 1 ≤ (inputLength + 1) ^ 3 := by
    have hsquare : 1 ≤ (inputLength + 1) ^ 2 := by
      exact Nat.one_le_pow' 2 inputLength
    calc
      inputLength + 1 = (inputLength + 1) * 1 := by omega
      _ ≤ (inputLength + 1) * (inputLength + 1) ^ 2 :=
        Nat.mul_le_mul_left _ hsquare
      _ = (inputLength + 1) ^ 3 := by ring
  unfold scannerSteps loadSteps
  change queryLength + 2 +
      iterationsSteps (List.range I.vertexCount).reverse I ≤
        60 * (inputLength + 1) ^ 3
  omega

/-- The compiled fixed controller emits the raw incidence rows within the
displayed cubic budget. -/
def rawOutput_outputs_in_time (I : VertexCoverInstance) :
    TM2OutputsInTime (compile program) (Incidence.inputStream I)
      (some (rawOutput I))
      (60 * (Incidence.inputStream I).length.succ ^ 3) := by
  have builderRun := scanner_run I
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (Incidence.inputStream I))
      (some (haltList (compile program) (rawOutput I)))
      (60 * (Incidence.inputStream I).length.succ ^ 3)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (scannerSteps_le I)⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- Polynomial-time computability of the raw prepend-only output. -/
noncomputable def rawComputableInPolyTime :
    TM2ComputableInPolyTime Incidence.inputStream id rawOutput where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 60 * (Polynomial.X + 1) ^ 3
  outputsFun := fun I => by
    have run := rawOutput_outputs_in_time I
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.succ_eq_add_one]
    all_goals
      change List.map id _ = _
      exact List.map_id _

/-- Same row contents, with the row order reversed at the type level. -/
def reversedFamily (I : VertexCoverInstance) : UnaryFrameMarkedRowFamily where
  rows := (incidenceFamily I).rows.reverse
  frameEnd_free := by
    intro row hrow symbol hsymbol
    exact (incidenceFamily I).frameEnd_free row (by simpa using hrow)
      symbol hsymbol

theorem reversedFamily_encode (I : VertexCoverInstance) :
    encodeUnaryFrameMarkedRowFamily (reversedFamily I) = descendingStream I := by
  rfl

theorem reversedFamily_reverse_encode (I : VertexCoverInstance) :
    encodeUnaryFrameMarkedRowOrderReverse (reversedFamily I) = stream I := by
  simp [reversedFamily, stream, incidenceFamily,
    encodeUnaryFrameMarkedRowFamily,
    encodeUnaryFrameMarkedRowOrderReverse]

private noncomputable def inputComputableAsIdentity :
    TM2ComputableInPolyTime encodeVertexCoverInstance Incidence.inputStream
      (fun I : VertexCoverInstance => I) := by
  let machine := Incidence.inputStreamComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        simpa using machine.outputsFun I }

private noncomputable def rawComputableAsIdentity :
    TM2ComputableInPolyTime Incidence.inputStream rawOutput
      (fun I : VertexCoverInstance => I) := by
  exact
    { tm := rawComputableInPolyTime.tm
      inputAlphabet := rawComputableInPolyTime.inputAlphabet
      outputAlphabet := rawComputableInPolyTime.outputAlphabet
      time := rawComputableInPolyTime.time
      outputsFun := fun I => by
        simpa using rawComputableInPolyTime.outputsFun I }

private noncomputable def reverseComputableAsIdentity :
    TM2ComputableInPolyTime rawOutput descendingStream
      (fun I : VertexCoverInstance => I) := by
  let machine := reverse_computableInPolyTime (Γ := UnaryFrameSym)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun (rawOutput I)
        simpa [rawOutput] using output }

private noncomputable def rowOrderComputableAsIdentity :
    TM2ComputableInPolyTime descendingStream stream
      (fun I : VertexCoverInstance => I) := by
  let machine := unaryFrameMarkedRowOrderReverse_computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun (reversedFamily I)
        simpa [reversedFamily_encode, reversedFamily_reverse_encode] using output }

/-- A fixed polynomial-time TM2 computes the canonical forward incidence
row stream directly from the original VERTEX-COVER encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id stream := by
  let builtInput := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    inputComputableAsIdentity rawComputableAsIdentity
  let rawMachine : TM2ComputableInPolyTime encodeVertexCoverInstance rawOutput
      (fun I : VertexCoverInstance => I) := by
    simpa [Function.comp_def] using Classical.choice builtInput
  let reversed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawMachine reverseComputableAsIdentity
  let descendingMachine :
      TM2ComputableInPolyTime encodeVertexCoverInstance descendingStream
        (fun I : VertexCoverInstance => I) := by
    simpa [Function.comp_def] using Classical.choice reversed
  let ordered := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    descendingMachine rowOrderComputableAsIdentity
  let machine : TM2ComputableInPolyTime encodeVertexCoverInstance stream
      (fun I : VertexCoverInstance => I) := by
    simpa [Function.comp_def] using Classical.choice ordered
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa using output }

/-- Public serialization equation for the scanner output. -/
theorem stream_encode (I : VertexCoverInstance) :
    stream I = encodeUnaryFrameMarkedRowFamily (incidenceFamily I) := by
  rfl

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner
