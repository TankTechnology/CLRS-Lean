import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Selector.Run
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# VERTEX-COVER complement machine: selector runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector

open PolyBuilder
open _root_.Turing

private theorem selectSteps_le (bit : Bool) (edge : Nat × Nat) :
    selectSteps bit edge ≤ 1 + 2 * (encodeCliqueEdge edge).length := by
  cases bit <;> simp [selectSteps]

private theorem iterationsSteps_le (edges : List (Nat × Nat))
    (bits : List Bool) (hlength : edges.length = bits.length) :
    iterationsSteps edges bits ≤
      2 * (edges.flatMap encodeCliqueEdge).length +
        2 * bits.length + 2 := by
  induction edges generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [iterationsSteps]
      | cons bit bits => simp at hlength
  | cons edge edges ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have htail : edges.length = bits.length := by
            simpa using hlength
          have hselect := selectSteps_le bit edge
          have hrest := ih bits htail
          simp only [iterationsSteps, List.flatMap_cons, List.length_append,
            List.length_cons]
          omega

/-- The exact selector execution is bounded by a fixed linear polynomial in
the paired input length. -/
theorem selectorSteps_le (edges : List (Nat × Nat)) (bits : List Bool)
    (hlength : edges.length = bits.length) :
    selectorSteps edges bits ≤ 4 * (inputEncoding (edges, bits)).length + 4 := by
  have hiterations := iterationsSteps_le edges bits hlength
  simp only [selectorSteps]
  have hinput : (inputEncoding (edges, bits)).length =
      (edges.flatMap encodeCliqueEdge).length + bits.length + 1 := by
    simp [inputEncoding, pairEncoding, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  rw [hinput]
  omega

/-- Domain of the reusable selector: one answer for every candidate. -/
def AlignedInput :=
  { pair : List (Nat × Nat) × List Bool // pair.1.length = pair.2.length }

def alignedInputEncoding (input : AlignedInput) :
    List (Option CliqueSym) :=
  inputEncoding input.1

def alignedSelectedEdges (input : AlignedInput) : List (Nat × Nat) :=
  selectedEdges input.1.1 input.1.2

def alignedSelectedStream (input : AlignedInput) : List CliqueSym :=
  selectedStream input.1.1 input.1.2

def alignedSelectedReverseStream (input : AlignedInput) : List CliqueSym :=
  selectedReverseStream input.1.1 input.1.2

def outputs_in_time (input : AlignedInput) :
    TM2OutputsInTime (compile program) (alignedInputEncoding input)
      (some (alignedSelectedReverseStream input))
      (4 * (alignedInputEncoding input).length + 4) := by
  rcases input with ⟨⟨edges, bits⟩, hlength⟩
  have builderRun := run edges bits hlength
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (inputEncoding (edges, bits)))
      (some (haltList (compile program) (selectedReverseStream edges bits)))
      (4 * (inputEncoding (edges, bits)).length + 4)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (selectorSteps_le edges bits hlength)⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

noncomputable def revComputableInPolyTime :
    TM2ComputableInPolyTime alignedInputEncoding id
      alignedSelectedReverseStream where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 4
  outputsFun := fun input => by
    have output := outputs_in_time input
    convert output using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

/-- A fixed polynomial-time TM2 emits the selected records in forward order. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime alignedInputEncoding id alignedSelectedStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    revComputableInPolyTime (reverse_computableInPolyTime (Γ := CliqueSym))
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [Function.comp_def, alignedSelectedReverseStream,
          alignedSelectedStream, selectedReverseStream] using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector
