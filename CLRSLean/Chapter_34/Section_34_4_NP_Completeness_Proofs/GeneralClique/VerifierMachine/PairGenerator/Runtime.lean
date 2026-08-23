import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Run
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Certificate pair-row generator: polynomial runtime

This module compiles the complete reverse-output run, restores forward row
order with the shared reversal machine, and connects the result to the generic
occurrence-row pair controller.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

open PolyBuilder

private theorem rowsStepsFrom_le (position : Nat) (vertices : List Nat) :
    rowsStepsFrom position vertices ≤
      vertices.length *
        (2 * vertices.sum + 5 * (position + vertices.length) + 11) := by
  induction vertices generalizing position with
  | nil => simp [rowsStepsFrom]
  | cons vertex vertices ih =>
      have htail := ih (position + 1)
      calc
        rowsStepsFrom position (vertex :: vertices) =
            1 + (2 * vertex + 5 * position + 10) +
              rowsStepsFrom (position + 1) vertices := rfl
        _ ≤ 1 + (2 * vertex + 5 * position + 10) +
            vertices.length *
              (2 * vertices.sum +
                5 * (position + 1 + vertices.length) + 11) :=
          Nat.add_le_add_left htail _
        _ ≤ (vertex :: vertices).length *
            (2 * (vertex :: vertices).sum +
              5 * (position + (vertex :: vertices).length) + 11) := by
          simp only [List.length_cons, List.sum_cons]
          have hgap :
              (vertices.length + 1) *
                  (2 * (vertex + vertices.sum) +
                    5 * (position + (vertices.length + 1)) + 11) =
                (1 + (2 * vertex + 5 * position + 10) +
                  vertices.length *
                    (2 * vertices.sum +
                      5 * (position + 1 + vertices.length) + 11)) +
                  (2 * vertices.length * vertex + 2 * vertices.sum +
                    5 * vertices.length + 5) := by
            ring
          rw [hgap]
          omega

private theorem encodeCliqueCertificate_length_eq (vertices : List Nat) :
    (encodeCliqueCertificate vertices).length =
      1 + vertices.sum + 2 * vertices.length := by
  have records : (vertices.flatMap encodeCliqueVertex).length =
      vertices.sum + 2 * vertices.length := by
    induction vertices with
    | nil => simp
    | cons vertex vertices ih =>
        simp only [List.flatMap_cons, List.length_append,
          encodeCliqueVertex_length, List.sum_cons, List.length_cons]
        omega
  simp [encodeCliqueCertificate, records]
  omega

/-- The exact reverse-output run is bounded quadratically by the physical
certificate encoding length. -/
theorem revSteps_le_input (vertices : List Nat) :
    revSteps vertices ≤
      20 * ((encodeCliqueCertificate vertices).length + 1) ^ 2 := by
  let inputLength := (encodeCliqueCertificate vertices).length
  have hrows := rowsStepsFrom_le 0 vertices
  have hlength := encodeCliqueCertificate_length_eq vertices
  have hcount : vertices.length ≤ inputLength := by
    simp only [inputLength]
    omega
  have hsum : vertices.sum ≤ inputLength := by
    simp only [inputLength]
    omega
  simp only [revSteps]
  nlinarith [sq_nonneg (inputLength + 1)]

/-- Compiled reverse-output row generator. -/
noncomputable def rev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
      (fun vertices : List Nat =>
        (TMClique.encodeIndexedOccurrenceEntries
          (certificatePairEntries vertices)).reverse) where
  tm := compile revProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun := fun vertices => by
    have builderRun := revRun vertices
    have compiledRun := compile_evalsToInTime revProgram builderRun
    have machineRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (encodeCliqueCertificate vertices))
        (some (_root_.Turing.haltList (compile revProgram)
          (TMClique.encodeIndexedOccurrenceEntries
            (certificatePairEntries vertices)).reverse))
        (revSteps vertices) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime := revSteps_le_input vertices
    have polynomialBound : revSteps vertices ≤
        (20 * (Polynomial.X + 1) ^ 2).eval
          (encodeCliqueCertificate vertices).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using htime
    have boundedRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (encodeCliqueCertificate vertices))
        (some (_root_.Turing.haltList (compile revProgram)
          (TMClique.encodeIndexedOccurrenceEntries
            (certificatePairEntries vertices)).reverse))
        ((20 * (Polynomial.X + 1) ^ 2).eval
          (encodeCliqueCertificate vertices).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans polynomialBound⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order canonical row serialization of all certificate vertices. -/
noncomputable def rows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
      (fun vertices : List Nat =>
        TMClique.encodeIndexedOccurrenceEntries
          (certificatePairEntries vertices)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      rev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- The same compiled machine, exposed at the semantic row-family boundary
needed by the reusable pair controller. -/
noncomputable def entries_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      TMClique.encodeIndexedOccurrenceEntries certificatePairEntries := by
  let rows := rows_computableInPolyTime
  exact
    { tm := rows.tm
      inputAlphabet := rows.inputAlphabet
      outputAlphabet := rows.outputAlphabet
      time := rows.time
      outputsFun := fun vertices => by
        simpa using rows.outputsFun vertices }

/-- Serialized pair stream generated from every pair of certificate positions. -/
def encodeCertificatePairIterations (vertices : List Nat) : List CliqueSym :=
  TMClique.encodeCompatibleOccurrenceIterations
    (certificatePairEntries vertices).reverse

/-- A fixed polynomial-time TM2 maps a canonical CLIQUE certificate directly
to its complete stream of positional vertex pairs. -/
noncomputable def pairIterations_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
      encodeCertificatePairIterations := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      entries_computableInPolyTime
      TMClique.compatibilityEdgesEntries_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
    (fun vertices : List Nat =>
      TMClique.encodeCompatibleOccurrenceIterations
        (certificatePairEntries vertices).reverse)
  simpa [Function.comp_def,
    TMClique.encodeCompatibleOccurrenceIterationsReverse] using
      Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
