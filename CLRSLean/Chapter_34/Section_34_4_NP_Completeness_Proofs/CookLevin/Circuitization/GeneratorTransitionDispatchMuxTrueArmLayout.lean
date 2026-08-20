import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmLayout

/-!
# Canonical true-arm rows of transition dispatch muxes

Every label's `whenTrue` row is the complete output bundle of its fixed
recursive TM2 statement.  This module extracts that row from actual mux
frames and proves exact agreement with the builder-free
`transitionStmtOutputWires` recursion.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- True-input row extracted from one proof-carrying label artifact. -/
def TransitionDispatchLabelArtifact.muxTrueInputValues
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) : List Nat :=
  artifact.muxFrames.map fun frame => frame.whenTrue

/-- Canonical mux frames preserve their true-input function in coordinate
order. -/
theorem affineMuxFinCanonicalFrames_whenTrue_values
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    (affineMuxFinCanonicalFrames start selector width
        whenTrue whenFalse).map (fun frame => frame.whenTrue) =
      List.ofFn whenTrue := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [affineMuxFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

/-- Builder-free row recurrence for the statement output of every fixed
program label. -/
def transitionDispatchTrueArmRowsForLabels
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    Nat → List tm.Λ → List (List Nat)
  | _, [] => []
  | start, label :: labels =>
      transitionCfgWireValues tm (workHeight tm height)
          (transitionStmtOutputWires tm (workHeight tm height)
            falseWire trueWire start source (tm.m label)
            (stmtPushSet_program_subset tm label)) ::
        transitionDispatchTrueArmRowsForLabels tm height falseWire trueWire
          source
          (start + compileStmtGateCost tm (workHeight tm height)
              (tm.m label) +
            (3 * cfgBitCount tm (workHeight tm height) + 1))
          labels

/-- Complete seed-only true-arm row family. -/
def transitionDispatchTrueArmRowsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  transitionDispatchTrueArmRowsForLabels tm seed.height seed.start
    (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2) (programLabels tm)

/-- Builder-free label artifacts carry exactly the recursive statement output
rows in their true-input fields. -/
theorem transitionDispatchLabelArtifacts_trueArmRows
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    (transitionDispatchLabelArtifacts tm height falseWire trueWire source
        start fallback labels).map
          TransitionDispatchLabelArtifact.muxTrueInputValues =
      transitionDispatchTrueArmRowsForLabels tm height falseWire trueWire
        source start labels := by
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchLabelArtifacts,
        transitionDispatchTrueArmRowsForLabels, List.map_cons]
      congr 1
      · unfold TransitionDispatchLabelArtifact.muxTrueInputValues
        rw [affineMuxFinCanonicalFrames_whenTrue_values]
        rfl
      · exact ih _ _

/-- Seed-derived artifacts have exactly the seed-only true-arm family. -/
theorem transitionDispatchArtifactsFromSeed_trueArmRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).map
        TransitionDispatchLabelArtifact.muxTrueInputValues =
      transitionDispatchTrueArmRowsFromSeed tm seed := by
  unfold transitionDispatchArtifactsFromSeed
    transitionDispatchTrueArmRowsFromSeed
  exact transitionDispatchLabelArtifacts_trueArmRows tm seed.height
    seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (programLabels tm)

/-- The original proof-carrying widening/dispatch pipeline has the same
true-arm rows as the seed-only recurrence. -/
theorem arithmeticWidening_dispatchArtifact_trueArmRows_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map
          TransitionDispatchLabelArtifact.muxTrueInputValues =
      transitionDispatchTrueArmRowsFromSeed tm
        { height := height, start := base.gates.length,
          rowBase := rowBase } := by
  dsimp only
  rw [arithmeticWidening_dispatchArtifacts_eq_seed]
  exact transitionDispatchArtifactsFromSeed_trueArmRows tm
    { height := height, start := base.gates.length, rowBase := rowBase }

end CLRS.Chapter34.Turing.CookLevin
