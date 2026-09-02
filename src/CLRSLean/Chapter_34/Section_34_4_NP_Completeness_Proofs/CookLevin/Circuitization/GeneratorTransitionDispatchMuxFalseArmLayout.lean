import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchSeed

/-!
# Canonical false-arm rows of transition dispatch muxes

The first label mux receives the widened source row as its false arm.  Each
later label receives the output row of the preceding mux.  This module states
that recurrence without proof-carrying builders and proves exact agreement
with every `whenFalse` field of the actual dispatch artifacts.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical coordinate-order values of a configuration wire bundle. -/
def transitionCfgWireValues (tm : _root_.Turing.FinTM2) (height : Nat)
    (wires : CfgWires tm height) : List Nat :=
  List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
    wires ((cfgSlotEquivFin tm height).symm coordinate)

/-- False-input row extracted from one proof-carrying label artifact. -/
def TransitionDispatchLabelArtifact.muxFalseInputValues
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) : List Nat :=
  artifact.muxFrames.map fun frame => frame.whenFalse

/-- Canonical mux frames preserve their false-input function in coordinate
order. -/
theorem affineMuxFinCanonicalFrames_whenFalse_values
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    (affineMuxFinCanonicalFrames start selector width
        whenTrue whenFalse).map (fun frame => frame.whenFalse) =
      List.ofFn whenFalse := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [affineMuxFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

/-- Builder-free recurrence for all label-local false-input rows. -/
def transitionDispatchFalseArmRowsForLabels
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    Nat → CfgWires tm (workHeight tm height) → List tm.Λ →
      List (List Nat)
  | _, _, [] => []
  | start, fallback, label :: labels =>
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm height) (tm.m label)
      transitionCfgWireValues tm (workHeight tm height) fallback ::
        transitionDispatchFalseArmRowsForLabels tm height source
          (muxStart + (3 * cfgBitCount tm (workHeight tm height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm height) muxStart) labels

/-- Complete false-arm rows reconstructed from one transition seed. -/
def transitionDispatchFalseArmRowsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  transitionDispatchFalseArmRowsForLabels tm seed.height source
    (seed.start + 2) source (programLabels tm)

/-- The builder-free artifacts' false-input rows are exactly the closed
fallback recurrence. -/
theorem transitionDispatchLabelArtifacts_falseArmRows
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    (transitionDispatchLabelArtifacts tm height falseWire trueWire source
        start fallback labels).map
          TransitionDispatchLabelArtifact.muxFalseInputValues =
      transitionDispatchFalseArmRowsForLabels tm height source
        start fallback labels := by
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchLabelArtifacts,
        transitionDispatchFalseArmRowsForLabels, List.map_cons]
      congr 1
      · unfold TransitionDispatchLabelArtifact.muxFalseInputValues
        rw [affineMuxFinCanonicalFrames_whenFalse_values]
        rfl
      · exact ih _ _

/-- Seed-derived artifacts carry exactly the seed-only false-arm row family. -/
theorem transitionDispatchArtifactsFromSeed_falseArmRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).map
        TransitionDispatchLabelArtifact.muxFalseInputValues =
      transitionDispatchFalseArmRowsFromSeed tm seed := by
  unfold transitionDispatchArtifactsFromSeed
    transitionDispatchFalseArmRowsFromSeed
  exact transitionDispatchLabelArtifacts_falseArmRows tm seed.height
    seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (programLabels tm)

/-- The first false-arm row, when present, is literally the canonical widened
fallback compiled in the preceding modules. -/
theorem transitionDispatchFalseArmRowsFromSeed_head
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (label : tm.Λ) (labels : List tm.Λ)
    (hlabels : programLabels tm = label :: labels) :
    (transitionDispatchFalseArmRowsFromSeed tm seed).head? =
      some (transitionWidenedFallbackValues tm seed) := by
  unfold transitionDispatchFalseArmRowsFromSeed
  rw [hlabels]
  simp only [transitionDispatchFalseArmRowsForLabels, List.head?_cons]
  congr 1
  unfold transitionCfgWireValues
  exact transitionWidenedFallbackValues_eq_canonical tm seed |>.symm

end CLRS.Chapter34.Turing.CookLevin
