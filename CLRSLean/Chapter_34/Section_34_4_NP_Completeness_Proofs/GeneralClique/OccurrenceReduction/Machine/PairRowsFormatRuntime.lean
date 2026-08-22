import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormatBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Formatting triangular pair rows: compiled runtime
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Concrete compiled formatter before restoring forward output order. -/
noncomputable def pairRowsFormatRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime pairRowsFormatInput id
      (fun count => (completePairEdgeStream count).reverse) where
  tm := compile pairRowsFormatRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 12 * (Polynomial.X + 1) ^ 3
  outputsFun := fun count => by
    have builderRun := pairRowsFormatRev_run count
    have compiledRun := compile_evalsToInTime
      pairRowsFormatRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile pairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile pairRowsFormatRevProgram)
          (pairRowsFormatInput count))
        (some (_root_.Turing.haltList (compile pairRowsFormatRevProgram)
          (completePairEdgeStream count).reverse))
        (pairRowsFormatRevSteps count) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : pairRowsFormatRevSteps count ≤
        (12 * (Polynomial.X + 1) ^ 3).eval
          (pairRowsFormatInput count).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat] using
        pairRowsFormatRevSteps_le_input count
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile pairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile pairRowsFormatRevProgram)
          (pairRowsFormatInput count))
        (some (_root_.Turing.haltList (compile pairRowsFormatRevProgram)
          (completePairEdgeStream count).reverse))
        ((12 * (Polynomial.X + 1) ^ 3).eval
          (pairRowsFormatInput count).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order formatter for every canonical triangular row input. -/
noncomputable def pairRowsFormat_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime pairRowsFormatInput id
      completePairEdgeStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      pairRowsFormatRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CliqueSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- The fixed compiled-and-composed formatter used by the public reduction. -/
noncomputable def pairRowsFormatMachine : _root_.Turing.FinTM2 :=
  pairRowsFormat_computableInPolyTime.tm

/-- Direct output contract for the fixed formatter machine. -/
theorem pairRowsFormatMachine_outputs (count : Nat) :
    Nonempty (_root_.Turing.TM2OutputsInTime
      pairRowsFormat_computableInPolyTime.tm
      (List.map pairRowsFormat_computableInPolyTime.inputAlphabet.invFun
        (pairRowsFormatInput count))
      (some (List.map
        pairRowsFormat_computableInPolyTime.outputAlphabet.invFun
        (completePairEdgeStream count)))
      (pairRowsFormat_computableInPolyTime.time.eval
        (pairRowsFormatInput count).length)) :=
  ⟨pairRowsFormat_computableInPolyTime.outputsFun count⟩

/-- Reinterpret the already verified raw-input row generator with its decoded
occurrence count as the semantic output value. -/
noncomputable def canonicalOccurrencePairRows_asCount_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id pairRowsFormatInput
      (fun input : List CNFSym => cnfLiteralCount (decodeCNF input)) := by
  let rows := canonicalOccurrencePairRows_computableInPolyTime
  exact
    { tm := rows.tm
      inputAlphabet := rows.inputAlphabet
      outputAlphabet := rows.outputAlphabet
      time := rows.time
      outputsFun := fun input => by
        simpa [pairRowsFormatInput, canonicalOccurrencePairRows,
          canonicalOccurrencePairRowFamily] using rows.outputsFun input }

/-- A fixed polynomial-time TM2 maps every raw CNF word to the complete stream
of normalized candidate occurrence pairs. -/
noncomputable def canonicalCompletePairEdgeStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalCompletePairEdgeStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrencePairRows_asCount_computableInPolyTime
      pairRowsFormat_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List CNFSym =>
      completePairEdgeStream (cnfLiteralCount (decodeCNF input)))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
