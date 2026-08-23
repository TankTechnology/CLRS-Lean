import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesGenericRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds

/-!
# Generic polynomial runtime of the occurrence-row pair controller
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.TMClique

open PolyBuilder

/-- Named semantic output used by the generic polynomial-time witness. -/
def encodeCompatibleOccurrenceIterationsReverse
    (entries : List (IndexedOccurrence × Nat)) : List CliqueSym :=
  encodeCompatibleOccurrenceIterations entries.reverse

/-- The generic terminating controller has the same cubic bound as its
formula-specific specialization. -/
theorem compatibilityEdgesEntriesSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesEntriesSteps entries ≤
      80 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 3 := by
  let inputLength := (encodeIndexedOccurrenceEntries entries).length
  have hreverse :
      (encodeIndexedOccurrenceEntries entries.reverse).length =
        inputLength := by
    simpa [inputLength] using
      encodeIndexedOccurrenceEntries_reverse_length entries
  have hload := compatibilityEdgesLoadRowsSteps_le_input entries
  have houter :=
    compatibilityEdgesOuterIterationsSteps_le_input entries.reverse
  rw [hreverse] at houter
  have hlinear : inputLength + 1 ≤ (inputLength + 1) ^ 3 :=
    Nat.le_pow (by omega)
  simp only [compatibilityEdgesEntriesSteps]
  change compatibilityEdgesLoadRowsSteps entries +
      compatibilityEdgesOuterIterationsSteps entries.reverse + 3 ≤
    80 * (inputLength + 1) ^ 3
  nlinarith

/-- Polynomial-time computability of the reusable arbitrary-row controller. -/
noncomputable def compatibilityEdgesEntries_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeIndexedOccurrenceEntries id
      encodeCompatibleOccurrenceIterationsReverse where
  tm := compile compatibilityEdgesProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 80 * (Polynomial.X + 1) ^ 3
  outputsFun := fun entries => by
    have builderRun := compatibilityEdges_entriesRun entries
    have compiledRun := compile_evalsToInTime compatibilityEdgesProgram
      builderRun
    have machineRun : EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceEntries entries))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeCompatibleOccurrenceIterations entries.reverse)))
        (compatibilityEdgesEntriesSteps entries) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime := compatibilityEdgesEntriesSteps_le_input entries
    have polynomialBound : compatibilityEdgesEntriesSteps entries ≤
        (80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceEntries entries).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using htime
    have boundedRun : EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceEntries entries))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeCompatibleOccurrenceIterations entries.reverse)))
        ((80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceEntries entries).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans polynomialBound⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile,
      encodeCompatibleOccurrenceIterationsReverse] using boundedRun

end CLRS.Chapter34.Turing.TMClique
