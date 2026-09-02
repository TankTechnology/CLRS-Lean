import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceDigitMergeRuntime
import Mathlib.Tactic

/-!
# Choice digits: polynomial runtime bound

The canonical merger has a quadratic bound in the length of the exact tagged
word that it consumes.  This keeps the machine theorem honest at the physical
encoding boundary used by later composition.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

@[simp] theorem choiceOccurrenceDigits_length (formula : CNF)
    (index : Nat) (truth : Bool) :
    (choiceOccurrenceDigits formula index truth).length = formula.length := by
  simp [choiceOccurrenceDigits]

theorem choiceOccurrenceStream_length (formula : CNF) (truth : Bool) :
    (choiceOccurrenceStream formula truth).length =
      reductionVariableCount formula * (formula.length + 1) := by
  simp [choiceOccurrenceStream, List.length_flatMap]

theorem choiceDigitMergeInput_length (truth : Bool) (input : List CNFSym) :
    (choiceDigitMergeInput truth input).length =
      reductionVariableCount (decodeCNF input) + 1 +
        reductionVariableCount (decodeCNF input) *
          ((decodeCNF input).length + 1) := by
  simp [choiceDigitMergeInput, choiceOccurrenceCounts,
    choiceOccurrenceStream_length]
  omega

private theorem choiceDigitMergeFamilySteps_le (formula : CNF)
    (start count : Nat) :
    choiceDigitMergeFamilySteps formula start count ≤
      count * (7 * (start + count) + 10 + 2 * formula.length) := by
  induction count generalizing start with
  | zero => simp [choiceDigitMergeFamilySteps]
  | succ count ih =>
      have hrest := ih (start := start + 1)
      rw [choiceDigitMergeFamilySteps, choiceDigitMergeItemSteps,
        choiceDigitMergePrefixSteps_eq]
      nlinarith

private theorem choiceDigitMergeCanonicalArithmetic
    (count formulaLength familySteps inputLength : Nat)
    (hfamily : familySteps ≤
      count * (7 * count + 10 + 2 * formulaLength))
    (hlength : inputLength =
      count + 1 + count * (formulaLength + 1)) :
    (2 * count + 1) + familySteps + (2 * count + 4) ≤
      20 * (inputLength + 1) ^ 2 := by
  have hc : count ≤ inputLength := by
    nlinarith
  have hcf : count * formulaLength ≤ inputLength := by
    nlinarith
  have hsq : count * count ≤ inputLength * inputLength :=
    Nat.mul_le_mul hc hc
  nlinarith

/-- Uniform quadratic bound in the actual canonical merger-input length. -/
theorem choiceDigitMergeCanonicalSteps_le (truth : Bool)
    (input : List CNFSym) :
    choiceDigitMergeCanonicalSteps input ≤
      20 * ((choiceDigitMergeInput truth input).length + 1) ^ 2 := by
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  have hfamily := choiceDigitMergeFamilySteps_le formula 0 count
  have hlength : (choiceDigitMergeInput truth input).length =
      count + 1 + count * (formula.length + 1) := by
    simpa [formula, count] using choiceDigitMergeInput_length truth input
  change choiceDigitMergeLoadSteps count +
      choiceDigitMergeFamilySteps formula 0 count + (2 * count + 4) ≤ _
  rw [choiceDigitMergeLoadSteps]
  exact choiceDigitMergeCanonicalArithmetic count formula.length _ _
    (by simpa using hfamily) hlength

/-- Reversed digit stream produced directly by the fixed merger. -/
def choiceDigitStreamRev (truth : Bool) (input : List CNFSym) :
    List ChoiceCountSym :=
  (choiceDigitStream (decodeCNF input) truth).reverse

/-- With `choiceDigitMergeInput` as its input encoding, the fixed merger is a
polynomial-time TM2 for the reversed digit stream. -/
noncomputable def choiceDigitStreamRev_fromMergeInput_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime (choiceDigitMergeInput truth) id
      (choiceDigitStreamRev truth) where
  tm := compile choiceDigitMergeProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun := fun input => by
    have builderRun := choiceDigitMergeCanonical_run truth input
    have compiledRun := compile_evalsToInTime choiceDigitMergeProgram builderRun
    have htime : choiceDigitMergeCanonicalSteps input ≤
        (20 * (Polynomial.X + 1) ^ 2).eval
          (choiceDigitMergeInput truth input).length := by
      have hbound := choiceDigitMergeCanonicalSteps_le truth input
      simpa [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X] using hbound
    have bounded : EvalsToInTime
        (compile choiceDigitMergeProgram).step
        (_root_.Turing.initList (compile choiceDigitMergeProgram)
          (choiceDigitMergeInput truth input))
        (some (_root_.Turing.haltList (compile choiceDigitMergeProgram)
          (choiceDigitStreamRev truth input)))
        ((20 * (Polynomial.X + 1) ^ 2).eval
          (choiceDigitMergeInput truth input).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        choiceDigitStreamRev]
    simp only [_root_.Turing.TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [id_eq, Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.SubsetSumReduction
