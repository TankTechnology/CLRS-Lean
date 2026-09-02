import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# HAM-CYCLE incidence-chain formatter: polynomial-time public interface
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction
open _root_.Turing

/-- Physical prepend-only output of the formatter. -/
def rawOutput (I : VertexCoverInstance) : List CliqueSym :=
  (chainEdgeStream I).reverse

/-- The compiled fixed controller emits the raw chain-edge stream within a
linear budget in the scanner-stream length. -/
def rawOutput_outputs_in_time (I : VertexCoverInstance) :
    TM2OutputsInTime (compile program) (Scanner.stream I)
      (some (rawOutput I))
      (52 * (Scanner.stream I).length.succ) := by
  have builderRun := formatter_run I
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (Scanner.stream I))
      (some (haltList (compile program) (rawOutput I)))
      (52 * (Scanner.stream I).length.succ)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (formatterSteps_le I)⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg, rawOutput]

/-- Polynomial-time computability of the prepend-only result. -/
noncomputable def rawComputableInPolyTime :
    TM2ComputableInPolyTime Scanner.stream id rawOutput where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 52 * (Polynomial.X + 1)
  outputsFun := fun I => by
    have run := rawOutput_outputs_in_time I
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.succ_eq_add_one]
    all_goals
      change List.map id _ = _
      exact List.map_id _

private noncomputable def scannerComputableAsIdentity :
    TM2ComputableInPolyTime encodeVertexCoverInstance Scanner.stream
      (fun I : VertexCoverInstance => I) := by
  let machine := Scanner.computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by simpa using machine.outputsFun I }

private noncomputable def rawComputableAsIdentity :
    TM2ComputableInPolyTime Scanner.stream rawOutput
      (fun I : VertexCoverInstance => I) := by
  exact
    { tm := rawComputableInPolyTime.tm
      inputAlphabet := rawComputableInPolyTime.inputAlphabet
      outputAlphabet := rawComputableInPolyTime.outputAlphabet
      time := rawComputableInPolyTime.time
      outputsFun := fun I => by simpa using rawComputableInPolyTime.outputsFun I }

private noncomputable def reverseComputableAsIdentity :
    TM2ComputableInPolyTime rawOutput chainEdgeStream
      (fun I : VertexCoverInstance => I) := by
  let machine := reverse_computableInPolyTime (Γ := CliqueSym)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun (rawOutput I)
        simpa [rawOutput] using output }

/-- A fixed polynomial-time TM2 computes every incidence-chain edge directly
from the original VERTEX-COVER encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id chainEdgeStream := by
  let scanned := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    scannerComputableAsIdentity rawComputableAsIdentity
  let rawMachine :
      TM2ComputableInPolyTime encodeVertexCoverInstance rawOutput
        (fun I : VertexCoverInstance => I) := by
    simpa [Function.comp_def] using Classical.choice scanned
  let reversed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawMachine reverseComputableAsIdentity
  let machine :
      TM2ComputableInPolyTime encodeVertexCoverInstance chainEdgeStream
        (fun I : VertexCoverInstance => I) := by
    simpa [Function.comp_def] using Classical.choice reversed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by simpa using machine.outputsFun I }

/-- Public serialization equation for the formatter output. -/
theorem chainEdgeStream_encode (I : VertexCoverInstance) :
    chainEdgeStream I =
      (allIncidenceChainEdges I).flatMap encodeCliqueEdge := by
  rfl

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain
