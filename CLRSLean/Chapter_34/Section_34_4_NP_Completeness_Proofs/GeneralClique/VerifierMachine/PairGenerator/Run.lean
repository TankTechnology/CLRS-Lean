import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Simulation
import Mathlib.Tactic

/-!
# Certificate pair-row generator: complete run

The local row simulation is lifted to every vertex record in a canonical
certificate.  The controller then clears its persistent position counter and
halts with the exact reverse serialization of the synthetic occurrence rows.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

open PolyBuilder

/-- Exact scan cost for a certificate suffix whose first vertex has the given
position.  The leading one in each nonempty case consumes `vertexMark`. -/
def rowsStepsFrom : Nat → List Nat → Nat
  | _, [] => 0
  | position, vertex :: vertices =>
      1 + (2 * vertex + 5 * position + 10) +
        rowsStepsFrom (position + 1) vertices

/-- A complete certificate suffix is converted to reverse-order synthetic
occurrence rows.  The final input buffer and test bit are intentionally hidden:
they are cleared by the common terminating suffix below. -/
def rowsRun (position : Nat) (vertices : List Nat)
    (tail : List CliqueSym) (output : List UnaryFrameSym)
    (buffer : Option CliqueSym) (test : Bool) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step revProgram)
        (cfg .scan buffer test
          (vertices.flatMap encodeCliqueVertex ++ tail)
          output (List.replicate position ()) [])
        (some (cfg .scan finalBuffer finalTest tail
          ((TMClique.encodeIndexedOccurrenceEntries
            (certificatePairEntriesFrom position vertices)).reverse ++ output)
          (List.replicate (position + vertices.length) ()) []))
        (rowsStepsFrom position vertices) := by
  induction vertices generalizing position output buffer test with
  | nil =>
      refine ⟨buffer, test, ?_⟩
      exact ⟨⟨0, by simp [certificatePairEntriesFrom,
        TMClique.encodeIndexedOccurrenceEntries, cfg]⟩, le_rfl⟩
  | cons vertex vertices ih =>
      let remainingInput := vertices.flatMap encodeCliqueVertex ++ tail
      have marker : EvalsToInTime (step revProgram)
          (cfg .scan buffer test
            ((vertex :: vertices).flatMap encodeCliqueVertex ++ tail)
            output (List.replicate position ()) [])
          (some (cfg .vertex (some .vertexMark) test
            ((encodeCliqueVertex vertex).tail ++ remainingInput)
            output (List.replicate position ()) [])) 1 := by
        simp only [List.flatMap_cons]
        simpa [remainingInput, encodeCliqueVertex, List.append_assoc] using
          (show EvalsToInTime (step revProgram)
              (cfg .scan buffer test
                (.vertexMark ::
                  ((encodeCliqueVertex vertex).tail ++ remainingInput))
                output (List.replicate position ()) [])
              (some (cfg .vertex (some .vertexMark) test
                ((encodeCliqueVertex vertex).tail ++ remainingInput)
                output (List.replicate position ()) [])) 1 from
            ⟨⟨1, rfl⟩, le_rfl⟩)
      have row := rowRun position vertex remainingInput output
        (some .vertexMark) test
      rcases ih (position + 1)
          ((TMClique.encodeIndexedOccurrenceEntry
            (certificatePairOccurrence position, vertex)).reverse ++ output)
          (some .recordEnd) false with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let first := EvalsToInTime.trans (step revProgram)
        1 (2 * vertex + 5 * position + 10) _ _ _ marker row
      let full := EvalsToInTime.trans (step revProgram)
        _ (rowsStepsFrom (position + 1) vertices) _ _ _ first remaining
      simpa [remainingInput, rowsStepsFrom, certificatePairEntriesFrom,
        TMClique.encodeIndexedOccurrenceEntries, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        full

private theorem clearPosition_eval (position : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (output : List UnaryFrameSym) :
    (flip Option.bind (step revProgram))^[position + 1]
      (some (cfg .clearPosition buffer test [] output
        (List.replicate position ()) [])) =
      some (cfg .clearScratch buffer false [] output [] []) := by
  induction position generalizing test with
  | zero => rfl
  | succ position ih =>
      rw [show position + 1 + 1 = (position + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[position + 1]
          (some (cfg .clearPosition buffer true [] output
            (List.replicate position ()) [])) = _
      exact ih true

/-- Exact full cost of the reverse-output certificate row generator. -/
def revSteps (vertices : List Nat) : Nat :=
  1 + rowsStepsFrom 0 vertices + vertices.length + 4

/-- The fixed reverse-output controller accepts the canonical certificate
encoding, clears all scratch state, and halts with exactly the required rows. -/
def revRun (vertices : List Nat) :
    EvalsToInTime (step revProgram)
      (initialCfg revProgram (encodeCliqueCertificate vertices))
      (some (haltCfg revProgram
        (TMClique.encodeIndexedOccurrenceEntries
          (certificatePairEntries vertices)).reverse))
      (revSteps vertices) := by
  have start : EvalsToInTime (step revProgram)
      (initialCfg revProgram (encodeCliqueCertificate vertices))
      (some (cfg .scan (some .certificateMark) false
        (vertices.flatMap encodeCliqueVertex) [] [] [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  rcases rowsRun 0 vertices [] [] (some .certificateMark) false with
    ⟨finalBuffer, finalTest, rows⟩
  let reverseOutput :=
    (TMClique.encodeIndexedOccurrenceEntries
      (certificatePairEntries vertices)).reverse
  have scanEmpty : EvalsToInTime (step revProgram)
      (cfg .scan finalBuffer finalTest [] reverseOutput
        (List.replicate vertices.length ()) [])
      (some (cfg .clearPosition none finalTest [] reverseOutput
        (List.replicate vertices.length ()) [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have clearPosition : EvalsToInTime (step revProgram)
      (cfg .clearPosition none finalTest [] reverseOutput
        (List.replicate vertices.length ()) [])
      (some (cfg .clearScratch none false [] reverseOutput [] []))
      (vertices.length + 1) :=
    ⟨⟨vertices.length + 1,
      clearPosition_eval vertices.length none finalTest reverseOutput⟩, le_rfl⟩
  have clearScratch : EvalsToInTime (step revProgram)
      (cfg .clearScratch none false [] reverseOutput [] [])
      (some (cfg .halt none false [] reverseOutput [] [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have halt : EvalsToInTime (step revProgram)
      (cfg .halt none false [] reverseOutput [] [])
      (some (haltCfg revProgram reverseOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step revProgram)
    1 (rowsStepsFrom 0 vertices) _ _ _ start (by
      simpa [certificatePairEntries, reverseOutput] using rows)
  let second := EvalsToInTime.trans (step revProgram)
    _ 1 _ _ _ first scanEmpty
  let third := EvalsToInTime.trans (step revProgram)
    _ (vertices.length + 1) _ _ _ second clearPosition
  let fourth := EvalsToInTime.trans (step revProgram)
    _ 1 _ _ _ third clearScratch
  let full := EvalsToInTime.trans (step revProgram)
    _ 1 _ _ _ fourth halt
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [revSteps]
    omega)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
