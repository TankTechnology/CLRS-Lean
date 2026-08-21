import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairCodecCore
import Mathlib.Tactic

/-!
# Exact simulation of the fixed-pair decoder
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Exact number of direct decoder steps on every physical input. -/
def fixedPairDecodeSteps {Δ : Type} : List Δ → Nat
  | [] => 2
  | [_] => 3
  | _ :: _ :: rest => 3 + fixedPairDecodeSteps rest

/-- Exact contextual run of the reverse-output fixed-pair decoder. -/
def fixedPairDecodeRev_context {Γ Δ : Type} [Fintype Δ]
    (decode : Δ → Δ → Γ) (buffer : Option Δ)
    (input : List Δ) (output : List Γ) :
    EvalsToInTime (step (fixedPairDecodeRevProgram decode))
      (fixedPairDecodeCfg decode .scan buffer input output)
      (some (haltCfg (fixedPairDecodeRevProgram decode)
        ((fixedPairDecode decode input).reverse ++ output)))
      (fixedPairDecodeSteps input) := by
  induction input using List.twoStepInduction generalizing buffer output with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | singleton first => exact ⟨⟨3, rfl⟩, le_rfl⟩
  | cons_cons first second rest ih _ =>
      have hprefix : EvalsToInTime
          (step (fixedPairDecodeRevProgram decode))
          (fixedPairDecodeCfg decode .scan buffer
            (first :: second :: rest) output)
          (some (fixedPairDecodeCfg decode .scan (some second) rest
            (decode first second :: output))) 3 :=
        ⟨⟨3, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans
        (step (fixedPairDecodeRevProgram decode))
        3 (fixedPairDecodeSteps rest) _
        (fixedPairDecodeCfg decode .scan (some second) rest
          (decode first second :: output)) _
        hprefix (ih (some second) (decode first second :: output))
      convert full using 1 <;>
        simp [fixedPairDecodeSteps, fixedPairDecode,
          List.reverse_cons, List.append_assoc] <;> omega

/-- Canonical exact direct decoder run. -/
def fixedPairDecodeRev_run {Γ Δ : Type} [Fintype Δ]
    (decode : Δ → Δ → Γ) (input : List Δ) :
    EvalsToInTime (step (fixedPairDecodeRevProgram decode))
      (initialCfg (fixedPairDecodeRevProgram decode) input)
      (some (haltCfg (fixedPairDecodeRevProgram decode)
        (fixedPairDecode decode input).reverse))
      (fixedPairDecodeSteps input) := by
  change EvalsToInTime _
    (fixedPairDecodeCfg decode .scan none input []) _ _
  simpa using fixedPairDecodeRev_context decode none input []

/-- The total decoder has a uniform linear physical-input bound. -/
theorem fixedPairDecodeSteps_le {Δ : Type} (input : List Δ) :
    fixedPairDecodeSteps input ≤ 2 * input.length + 2 := by
  induction input using List.twoStepInduction with
  | nil => simp [fixedPairDecodeSteps]
  | singleton first => simp [fixedPairDecodeSteps]
  | cons_cons first second rest ih _ =>
      simp only [fixedPairDecodeSteps, List.length_cons]
      omega

end CLRS.Chapter34.Turing.PolyBuilder
