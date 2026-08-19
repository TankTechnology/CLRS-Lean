import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementLayout

/-!
# Seed-complete transition dispatch artifacts

The label dispatch is reconstructed here without any proof-carrying builders.
Each artifact contains the complete recursive statement script and the full
whole-row mux operand frames; the accumulated fallback is the arithmetic mux
output row from the preceding label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Builder-free artifact recursion for an arbitrary suffix of fixed program
labels.  The source row is unchanged across labels, while `fallback` advances
to each preceding arithmetic mux output row. -/
def transitionDispatchLabelArtifacts (tm : _root_.Turing.FinTM2)
    (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    (start : Nat) → CfgWires tm (workHeight tm height) → List tm.Λ →
      List (TransitionDispatchLabelArtifact tm)
  | _, _, [] => []
  | start, fallback, label :: labels =>
      let statement := transitionStmtScript tm (workHeight tm height)
        falseWire trueWire start source (tm.m label)
        (stmtPushSet_program_subset tm label)
      let statementWires := transitionStmtOutputWires tm
        (workHeight tm height) falseWire trueWire start source (tm.m label)
        (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm height) (tm.m label)
      { label := label
        start := start
        statement := statement
        selector := selector
        muxFrames := affineMuxFinCanonicalFrames muxStart selector _
          (fun coordinate => statementWires
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate))
          (fun coordinate => fallback
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate)) } ::
        transitionDispatchLabelArtifacts tm height falseWire trueWire source
          (muxStart + (3 * cfgBitCount tm (workHeight tm height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm height) muxStart) labels

/-- The proof-carrying label recursion is exactly the builder-free artifact
recursion, including every nested statement operand and every mux arm. -/
theorem compileDispatchLabelsListArtifacts_eq_arithmetic
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels =
      transitionDispatchLabelArtifacts tm height pool.falseWire pool.trueWire
        source base.gates.length fallback labels := by
  induction labels generalizing base fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts,
        transitionDispatchLabelArtifacts]
      rw [compileStmtScript_eq_transitionStmtScript]
      congr 1
      · rw [compileStmt_gate_delta]
        rw [compileStmt_wires_eq_transitionStmtOutputWires]
      · rw [ih]
        rw [cfgMux_wires_eq_arithmetic]
        rw [cfgMux_gate_delta, compileStmt_gate_delta]
        simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
          CircuitBuilder.BoolWirePool.mono_trueWire, Nat.add_assoc]

/-- Complete canonical-label artifact family decoded directly from one raw
transition-row seed. -/
def transitionDispatchArtifactsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (TransitionDispatchLabelArtifact tm) :=
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  transitionDispatchLabelArtifacts tm seed.height seed.start (seed.start + 1)
    source (seed.start + 2) source (programLabels tm)

/-- Actual widening plus complete proof-carrying dispatch artifacts are equal,
not merely projectionwise equal, to the raw-seed reconstruction. -/
theorem arithmeticWidening_dispatchArtifacts_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid =
      transitionDispatchArtifactsFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_eq_arithmetic]
  unfold transitionDispatchArtifactsFromSeed
  rw [widenCfg_falseWire_eq, widenCfg_trueWire_eq,
    widenCfg_arithmetic_wires_eq, widenCfg_gate_delta]

end CLRS.Chapter34.Turing.CookLevin
