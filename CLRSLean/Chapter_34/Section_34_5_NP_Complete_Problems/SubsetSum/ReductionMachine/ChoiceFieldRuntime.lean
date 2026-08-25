import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceFieldSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Choice fields: compiled polynomial-time formatter

The family simulation is closed to a successful halt, bounded linearly in
the physical delimiter encoding, compiled to one fixed TM2, and composed with
the already verified choice-block source.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- Successful controller cost, including empty-input detection and halt. -/
def choiceFieldCanonicalSteps (items : List (List Bool)) : Nat :=
  choiceFieldFamilySteps items + 2

/-- The fixed formatter successfully halts on every canonical item-family
encoding. -/
def choiceFieldCanonical_run (items : List (List Bool)) :
    EvalsToInTime (step choiceFieldProgram)
      (initialCfg choiceFieldProgram (choiceBlockItemsInput items))
      (some (haltCfg choiceFieldProgram
        (choiceBitFields items).reverse))
      (choiceFieldCanonicalSteps items) := by
  have family := choiceField_familyRun items [] [] none false
  have finish : EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .scan none none false []
        (choiceBitFields items).reverse [] [])
      (some (haltCfg choiceFieldProgram
        (choiceBitFields items).reverse)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step choiceFieldProgram)
    (choiceFieldFamilySteps items) 2 _ _ _
    (by simpa [initialCfg, List.append_nil, List.append_nil] using family)
    finish
  simpa [choiceFieldCanonicalSteps, Nat.add_comm,
    initialCfg, choiceFieldCfg, choiceFieldProgram] using full

private theorem choiceFieldCanonSteps_le (started : Bool)
    (bits : List Bool) :
    choiceFieldCanonSteps started bits ≤ 2 * bits.length + 2 := by
  induction bits generalizing started with
  | nil => cases started <;> simp [choiceFieldCanonSteps]
  | cons bit bits ih =>
      cases started <;> cases bit <;>
        simp [choiceFieldCanonSteps] at ih ⊢ <;> omega

private theorem choiceFieldItemSteps_le (bits : List Bool) :
    choiceFieldItemSteps bits ≤ 5 * (bits.length + 1) := by
  have hcanon := choiceFieldCanonSteps_le false bits.reverse
  simp only [List.length_reverse] at hcanon
  simp [choiceFieldItemSteps, choiceFieldScanSteps]
  omega

private theorem choiceFieldFamilySteps_le (items : List (List Bool)) :
    choiceFieldFamilySteps items ≤
      5 * (choiceBlockItemsInput items).length := by
  induction items with
  | nil => simp [choiceFieldFamilySteps, choiceBlockItemsInput]
  | cons bits items ih =>
      have hitem := choiceFieldItemSteps_le bits
      have ih' : choiceFieldFamilySteps items ≤
          5 * (items.flatMap fun payload =>
            payload.map ChoiceBlockSym.bit ++ [.itemEnd]).length := by
        simpa [choiceBlockItemsInput] using ih
      simp only [choiceFieldFamilySteps, choiceBlockItemsInput,
        List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, List.length_nil]
      omega

/-- Linear bound in the actual word consumed by the compiled formatter. -/
theorem choiceFieldCanonicalSteps_le (items : List (List Bool)) :
    choiceFieldCanonicalSteps items ≤
      7 * ((choiceBlockItemsInput items).length + 1) := by
  have hfamily := choiceFieldFamilySteps_le items
  simp [choiceFieldCanonicalSteps]
  omega

/-- Native reversed fields computed by the formatter. -/
def choiceBitFieldsRev (items : List (List Bool)) : List SubsetSumSym :=
  (choiceBitFields items).reverse

/-- With delimiter encoding as its input representation, the formatter is a
fixed polynomial-time TM2. -/
noncomputable def choiceBitFieldsRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime choiceBlockItemsInput id
      choiceBitFieldsRev where
  tm := compile choiceFieldProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 7 * (Polynomial.X + 1)
  outputsFun := fun items => by
    have builderRun := choiceFieldCanonical_run items
    have compiledRun := compile_evalsToInTime choiceFieldProgram builderRun
    have htime : choiceFieldCanonicalSteps items ≤
        (7 * (Polynomial.X + 1)).eval
          (choiceBlockItemsInput items).length := by
      have hbound := choiceFieldCanonicalSteps_le items
      simpa [Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X] using hbound
    have bounded : EvalsToInTime
        (compile choiceFieldProgram).step
        (_root_.Turing.initList (compile choiceFieldProgram)
          (choiceBlockItemsInput items))
        (some (_root_.Turing.haltList (compile choiceFieldProgram)
          (choiceBitFieldsRev items)))
        ((7 * (Polynomial.X + 1)).eval
          (choiceBlockItemsInput items).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        choiceBitFieldsRev]
    simp only [_root_.Turing.TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [id_eq, Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _

/-- Reinterpret the verified block source through its exact delimiter-family
equation. -/
noncomputable def choiceGeneratedBitItems_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id choiceBlockItemsInput
      (choiceGeneratedBitItems truth) := by
  let source := choiceBlockStream_computableInPolyTime truth
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have output := source.outputsFun input
        simpa only [choiceBlockStream_eq_items truth input, id_eq] using output }

/-- One fixed polynomial-time TM2 emits the generated truth-family fields in
forward public order from a raw CNF word. -/
noncomputable def choiceGeneratedFields_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceGeneratedFields truth) := by
  let reversed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceGeneratedBitItems_computableInPolyTime truth)
      choiceBitFieldsRev_computableInPolyTime
  let restored :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice reversed)
      (reverse_computableInPolyTime (Γ := SubsetSumSym))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => choiceBitFields (choiceGeneratedBitItems truth input))
  simpa [Function.comp_def, choiceGeneratedFields,
    choiceBitFieldsRev] using Classical.choice restored

end CLRS.Chapter34.Turing.SubsetSumReduction
