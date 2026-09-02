import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsRuntime

/-!
# Occurrence compatibility edges: compiled polynomial runtime

The exact builder run is compiled to a fixed TM2 with a cubic polynomial
bound.  A second theorem composes it with the already verified raw-CNF row
generator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- The compiled compatibility controller computes the canonical occurrence
edge suffix from the semantic formula's indexed-row encoding. -/
noncomputable def compatibilityEdges_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun formula : CNF => encodeIndexedOccurrenceRows formula) id
      encodeOccurrenceCliqueEdges where
  tm := compile compatibilityEdgesProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 80 * (Polynomial.X + 1) ^ 3
  outputsFun := fun formula => by
    have builderRun := compatibilityEdges_run formula
    have compiledRun := compile_evalsToInTime compatibilityEdgesProgram
      builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceRows formula))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeOccurrenceCliqueEdges formula)))
        (compatibilityEdgesSteps formula) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : compatibilityEdgesSteps formula ≤
        (80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceRows formula).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using compatibilityEdgesSteps_le_input formula
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceRows formula))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeOccurrenceCliqueEdges formula)))
        ((80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceRows formula).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reinterpret the raw-input indexed-row machine as returning the decoded
formula through the indexed-row representation expected by the edge phase. -/
noncomputable def canonicalIndexedOccurrenceRows_asFormula_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id encodeIndexedOccurrenceRows
      (fun input : List CNFSym => decodeCNF input) := by
  let rows := canonicalIndexedOccurrenceRows_computableInPolyTime
  exact
    { tm := rows.tm
      inputAlphabet := rows.inputAlphabet
      outputAlphabet := rows.outputAlphabet
      time := rows.time
      outputsFun := fun input => by
        simpa [canonicalIndexedOccurrenceRows] using rows.outputsFun input }

/-- A fixed polynomial-time TM2 maps every raw CNF word to the canonical edge
suffix of its decoded occurrence graph. -/
noncomputable def canonicalOccurrenceCliqueEdges_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym =>
        encodeOccurrenceCliqueEdges (decodeCNF input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalIndexedOccurrenceRows_asFormula_computableInPolyTime
      compatibilityEdges_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
