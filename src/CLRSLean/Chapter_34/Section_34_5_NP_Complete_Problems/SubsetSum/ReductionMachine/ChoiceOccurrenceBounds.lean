import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsBounds
import Mathlib.Tactic

/-!
# Choice occurrence counter: polynomial bounds

The controller is used only behind the canonical batch encoding.  Its running
time is bounded here by a quadratic polynomial in the length of that encoding;
this is the interface needed to compose it with the verified batch generator.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Physical length of one canonical occurrence batch. -/
def choiceOccurrenceBatchSize (formula : CNF) : Nat :=
  reductionBlockWidth formula + reductionVariableCount formula +
    (encCNF formula).length + 1

@[simp] theorem choiceOccurrenceBatchInput_length (formula : CNF) :
    (choiceOccurrenceBatchInput
      (reductionBlockWidth formula) (reductionVariableCount formula)
      formula).length = choiceOccurrenceBatchSize formula := by
  simp [choiceOccurrenceBatchInput, choiceOccurrenceFormulaInput,
    choiceOccurrenceBatchSize, Nat.add_assoc]

theorem choiceBatches_length (input : List CNFSym) :
    (choiceBatches input).length =
      reductionVariableCount (decodeCNF input) *
        choiceOccurrenceBatchSize (decodeCNF input) := by
  rw [← choiceOccurrenceBatchFamilyInput_eq_choiceBatches]
  simp [choiceOccurrenceBatchFamilyInput]

private theorem choiceOccurrenceLiteralSteps_le
    (index bound : Nat) (literal : Literal)
    (hindex : index < bound)
    (hvariable : litIndex literal + 1 ≤ bound) :
    choiceOccurrenceLiteralSteps index literal ≤ 20 * (bound + 1) := by
  cases literal <;>
    simp [choiceOccurrenceLiteralSteps, choiceOccurrenceComparisonSteps,
      litIndex] at hvariable ⊢ <;> omega

private theorem choiceOccurrenceClauseSteps_le
    (index bound : Nat) (clause : Clause)
    (hindex : index < bound)
    (hvariables : ∀ literal ∈ clause, litIndex literal + 1 ≤ bound) :
    choiceOccurrenceClauseSteps index clause ≤
      clause.length * (20 * (bound + 1)) := by
  induction clause with
  | nil => simp [choiceOccurrenceClauseSteps]
  | cons literal clause ih =>
      have hhead := choiceOccurrenceLiteralSteps_le index bound literal
        hindex (hvariables literal (by simp))
      have htail := ih (fun current hcurrent =>
        hvariables current (by simp [hcurrent]))
      rw [choiceOccurrenceClauseSteps_cons]
      simp only [List.length_cons, Nat.add_mul]
      omega

private theorem choiceOccurrenceRemainingSteps_le
    (truth : Bool) (index bound : Nat) (formula : CNF)
    (hindex : index < bound)
    (hvariables : ∀ clause ∈ formula, ∀ literal ∈ clause,
      litIndex literal + 1 ≤ bound) :
    choiceOccurrenceRemainingSteps truth index formula ≤
      30 * (bound + 1) *
        (cnfLiteralCount formula + formula.length) := by
  induction formula with
  | nil => simp [choiceOccurrenceRemainingSteps, cnfLiteralCount]
  | cons clause formula ih =>
      have hclause := choiceOccurrenceClauseSteps_le index bound clause hindex
        (fun literal hliteral =>
          hvariables clause (by simp) literal hliteral)
      have hrest := ih (fun current hcurrent literal hliteral =>
        hvariables current (by simp [hcurrent]) literal hliteral)
      have hcount : clause.count (itemLiteral index truth) ≤ clause.length :=
        List.count_le_length
      simp only [choiceOccurrenceRemainingSteps,
        cnfLiteralCount_cons, List.length_cons,
        choiceOccurrenceDispatchSteps]
      nlinarith

private theorem clauseLength_add_one_le_encClause_length (clause : Clause) :
    clause.length + 1 ≤ (encClause clause).length := by
  induction clause with
  | nil => simp [encClause]
  | cons literal clause ih =>
      cases literal <;>
        simp [encClause, encLit, litSym] at ih ⊢ <;> omega

private theorem cnfSize_le_encCNF_length (formula : CNF) :
    cnfLiteralCount formula + formula.length ≤ (encCNF formula).length := by
  induction formula with
  | nil => simp [cnfLiteralCount, encCNF]
  | cons clause formula ih =>
      have hclause := clauseLength_add_one_le_encClause_length clause
      simp only [cnfLiteralCount_cons, List.length_cons, encCNF,
        List.flatMap_cons, List.length_append] at ih ⊢
      omega

private theorem choiceOccurrenceBatchSteps_le
    (truth : Bool) (formula : CNF) (index : Nat)
    (hindex : index < reductionVariableCount formula) :
    choiceOccurrenceBatchSteps truth index
        (reductionBlockWidth formula) (reductionVariableCount formula)
        formula ≤
      70 * (choiceOccurrenceBatchSize formula + 1) ^ 2 := by
  let bound := choiceOccurrenceBatchSize formula
  have hnlt : reductionVariableCount formula < bound := by
    simp [bound, choiceOccurrenceBatchSize]
    omega
  have hindex' : index < bound := lt_trans hindex hnlt
  have hvariables : ∀ clause ∈ formula, ∀ literal ∈ clause,
      litIndex literal + 1 ≤ bound := by
    intro clause hclause literal hliteral
    have hliteralBound := literalIndex_lt_reductionVariableCount
      hclause hliteral
    cases literal <;>
      simp [litIndex, literalIndex] at hliteralBound ⊢ <;> omega
  have hremaining := choiceOccurrenceRemainingSteps_le truth index bound
    formula hindex' hvariables
  have hformulaSize := cnfSize_le_encCNF_length formula
  have hencBound : (encCNF formula).length < bound := by
    simp [bound, choiceOccurrenceBatchSize]
  have hsizeBound : cnfLiteralCount formula + formula.length ≤ bound :=
    hformulaSize.trans (Nat.le_of_lt hencBound)
  have hremaining' : choiceOccurrenceRemainingSteps truth index formula ≤
      30 * (bound + 1) * bound :=
    hremaining.trans (Nat.mul_le_mul_left (30 * (bound + 1)) hsizeBound)
  have hdimensions : reductionBlockWidth formula +
      reductionVariableCount formula ≤ bound := by
    simp [bound, choiceOccurrenceBatchSize]
    omega
  simp only [choiceOccurrenceBatchSteps]
  dsimp [bound] at hremaining' hdimensions ⊢
  nlinarith

private theorem choiceOccurrenceBatchFamilySteps_le
    (truth : Bool) (formula : CNF) (start count : Nat)
    (hlimit : start + count ≤ reductionVariableCount formula) :
    choiceOccurrenceBatchFamilySteps truth start count
        (reductionBlockWidth formula) (reductionVariableCount formula)
        formula ≤
      count * (70 * (choiceOccurrenceBatchSize formula + 1) ^ 2) := by
  induction count generalizing start with
  | zero => simp [choiceOccurrenceBatchFamilySteps]
  | succ count ih =>
      have hstart : start < reductionVariableCount formula := by omega
      have hrest : start + 1 + count ≤
          reductionVariableCount formula := by omega
      have hhead := choiceOccurrenceBatchSteps_le truth formula start hstart
      have htail := ih (start := start + 1) hrest
      simp only [choiceOccurrenceBatchFamilySteps, List.range'_succ,
        List.map_cons, List.sum_cons]
      simp only [choiceOccurrenceBatchFamilySteps] at htail
      simp only [Nat.add_mul]
      omega

private theorem choiceOccurrenceCanonicalArithmetic
    (count batchSize familySteps : Nat)
    (hcount : 0 < count) (hbatch : 0 < batchSize)
    (hfamily : familySteps ≤
      count * (70 * (batchSize + 1) ^ 2)) :
    1 + familySteps + (count + 4) ≤
      300 * (count * batchSize + 1) ^ 2 := by
  have hbatchSquare : (batchSize + 1) ^ 2 ≤ 4 * batchSize ^ 2 := by
    nlinarith
  have hfamily' : familySteps ≤ 280 * count * batchSize ^ 2 := by
    nlinarith
  nlinarith

/-- Uniform quadratic bound in the actual canonical batch-stream length. -/
theorem choiceOccurrenceCanonicalSteps_le (truth : Bool)
    (input : List CNFSym) :
    choiceOccurrenceCanonicalSteps truth input ≤
      300 * ((choiceBatches input).length + 1) ^ 2 := by
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  let batchSize := choiceOccurrenceBatchSize formula
  have hfamily := choiceOccurrenceBatchFamilySteps_le truth formula 0 count
    (by omega)
  have hlength : (choiceBatches input).length = count * batchSize := by
    simpa [formula, count, batchSize] using choiceBatches_length input
  by_cases hcount : count = 0
  · rw [hlength, hcount]
    simp [choiceOccurrenceCanonicalSteps, formula, count, hcount,
      choiceOccurrenceBatchFamilySteps]
  · have hcountPos : 0 < count := Nat.pos_of_ne_zero hcount
    have hbatchPos : 0 < batchSize := by
      simp [batchSize, choiceOccurrenceBatchSize]
    rw [hlength]
    change 1 + choiceOccurrenceBatchFamilySteps truth 0 count
        (reductionBlockWidth formula) (reductionVariableCount formula)
        formula + (count + 4) ≤
      300 * (count * batchSize + 1) ^ 2
    exact choiceOccurrenceCanonicalArithmetic count batchSize _
      hcountPos hbatchPos hfamily

/-- Semantic reversed occurrence stream produced by the controller. -/
def choiceOccurrenceCountsRev (truth : Bool) (input : List CNFSym) :
    List ChoiceCountSym :=
  (choiceOccurrenceStream (decodeCNF input) truth).reverse

/-- With `choiceBatches` as the input encoding, the fixed occurrence
controller is a polynomial-time TM2 on every semantic raw CNF value. -/
noncomputable def choiceOccurrenceCountsRev_fromBatches_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime choiceBatches id
      (choiceOccurrenceCountsRev truth) where
  tm := compile (choiceOccurrenceProgram truth)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 300 * (Polynomial.X + 1) ^ 2
  outputsFun := fun input => by
    have builderRun := choiceOccurrenceCanonical_run truth input
    have compiledRun := compile_evalsToInTime
      (choiceOccurrenceProgram truth) builderRun
    have htime : choiceOccurrenceCanonicalSteps truth input ≤
        (300 * (Polynomial.X + 1) ^ 2).eval
          (choiceBatches input).length := by
      have hbound := choiceOccurrenceCanonicalSteps_le truth input
      simpa [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X] using hbound
    have bounded : EvalsToInTime
        (compile (choiceOccurrenceProgram truth)).step
        (_root_.Turing.initList (compile (choiceOccurrenceProgram truth))
          (choiceBatches input))
        (some (_root_.Turing.haltList
          (compile (choiceOccurrenceProgram truth))
          (choiceOccurrenceCountsRev truth input)))
        ((300 * (Polynomial.X + 1) ^ 2).eval
          (choiceBatches input).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        choiceOccurrenceCountsRev]
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
