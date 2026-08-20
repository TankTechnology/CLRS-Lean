import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFamily
import Mathlib.Tactic

/-!
# Affine source data for transition-dispatch mux skeletons

Each fixed label arm ends in a whole-workspace mux.  This module isolates the
runtime data that is independent of the two mux arms: the public-row selector
and the three fresh coordinates allocated for every workspace coordinate.
The coordinates form one affine triple progression per label, so no wire
index is stored in finite control.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed affine form selecting one program label from the public row. -/
def transitionDispatchSelectorForm (tm : _root_.Turing.FinTM2)
    (label : tm.Λ) : AffineUnaryTripleForm :=
  { constant := 1 + (labelEquivFin tm label).val
    first := 0
    second := 0
    third := 1 }

@[simp] theorem transitionDispatchSelectorForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (label : tm.Λ) :
    affineUnaryTripleFormValue (transitionDispatchSelectorForm tm label)
        (transitionTailAffineSeed seed) =
      seed.rowBase + (1 + (labelEquivFin tm label).val) := by
  simp [transitionDispatchSelectorForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue]
  omega

/-- Fixed label-order selector table for one dispatch row. -/
def transitionDispatchSelectorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (programLabels tm).map (transitionDispatchSelectorForm tm)

/-- Evaluating the fixed selector table returns exactly the selector list
extracted from the seed-derived widened row. -/
theorem transitionDispatchSelectorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchSelectorForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchSelectors tm seed := by
  rw [transitionDispatchSelectors_eq]
  simp [transitionDispatchSelectorForms, affineUnaryTripleMap]

/-- One label-local mux together with the runtime progression generating its
shared selector-negation and two fresh AND-output coordinates. -/
structure TransitionDispatchMuxRuntime where
  selector : Nat
  progression : AffineUnaryTripleProgression
deriving DecidableEq, Repr

/-- Runtime mux skeletons for a fixed label suffix.  This definition follows
the semantic label recursion, but retains only selector and fresh coordinates.
-/
def transitionDispatchMuxRuntimesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    Nat → List tm.Λ → List TransitionDispatchMuxRuntime
  | _, [] => []
  | start, label :: labels =>
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm seed.height) (tm.m label)
      { selector := seed.rowBase + (1 + (labelEquivFin tm label).val)
        progression :=
          { base₁ := muxStart
            base₂ := muxStart + 1
            base₃ := muxStart + 2
            step₁ := 0
            step₂ := 3
            step₃ := 3
            count := cfgBitCount tm (workHeight tm seed.height) } } ::
        transitionDispatchMuxRuntimesForLabels tm seed
          (muxStart + (3 * cfgBitCount tm (workHeight tm seed.height) + 1))
          labels

/-- Complete fixed-label mux runtime family of one transition row. -/
def transitionDispatchMuxRuntimes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List TransitionDispatchMuxRuntime :=
  transitionDispatchMuxRuntimesForLabels tm seed (seed.start + 2)
    (programLabels tm)

/-- Forget the progression representation and recover the existing mux fresh
layout interface. -/
def TransitionDispatchMuxRuntime.layout
    (runtime : TransitionDispatchMuxRuntime) :
    TransitionDispatchMuxFreshLayout :=
  { selector := runtime.selector
    coordinates :=
      (affineUnaryTripleProgressionRows runtime.progression).map id }

/-- One runtime progression denotes literally the canonical mux fresh
coordinate list. -/
theorem transitionDispatchMuxRuntime_layout_eq
    (selector muxStart width : Nat) :
    TransitionDispatchMuxRuntime.layout
        { selector := selector
          progression :=
            { base₁ := muxStart, base₂ := muxStart + 1,
              base₃ := muxStart + 2, step₁ := 0, step₂ := 3,
              step₃ := 3, count := width } } =
      transitionDispatchMuxFreshLayout muxStart selector width := by
  unfold TransitionDispatchMuxRuntime.layout
    transitionDispatchMuxFreshLayout
  congr 1
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [List.map_id]
  apply List.ofFn_inj.mpr
  funext coordinate
  simp
  omega

/-- The progression family is an exact representation of the previously
verified seed-only mux skeleton, not merely a list with matching lengths. -/
theorem transitionDispatchMuxRuntimes_layouts_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxRuntimes tm seed).map
        TransitionDispatchMuxRuntime.layout =
      transitionDispatchMuxFreshLayoutsFromSeed tm seed := by
  unfold transitionDispatchMuxRuntimes
    transitionDispatchMuxFreshLayoutsFromSeed
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  change
    (transitionDispatchMuxRuntimesForLabels tm seed (seed.start + 2)
        (programLabels tm)).map TransitionDispatchMuxRuntime.layout =
      transitionDispatchMuxFreshLayouts tm seed.height source
        (seed.start + 2) (programLabels tm)
  generalize programLabels tm = labels
  generalize seed.start + 2 = start
  induction labels generalizing start with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchMuxRuntimesForLabels,
        transitionDispatchMuxFreshLayouts, List.map_cons]
      congr 1
      · have hselector :
            source.label (Fin.castSucc (labelEquivFin tm label)) =
              seed.rowBase + (1 + (labelEquivFin tm label).val) := by
          unfold source arithmeticWidenedCfgWires
          change (arithmeticCfgWires tm seed.height seed.rowBase).label
              (Fin.castSucc (labelEquivFin tm label)) = _
          rw [arithmeticCfgWires_label]
          rfl
        rw [hselector]
        exact transitionDispatchMuxRuntime_layout_eq _ _ _
      · exact ih _

/-- The concrete proof-carrying widening and dispatch artifacts therefore
have exactly the layouts represented by the runtime progressions. -/
theorem arithmeticWidening_dispatchArtifact_muxRuntimeLayouts_eq
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map
          TransitionDispatchLabelArtifact.muxFreshLayout =
      (transitionDispatchMuxRuntimes tm
        { height := height, start := base.gates.length,
          rowBase := rowBase }).map TransitionDispatchMuxRuntime.layout := by
  dsimp only
  rw [arithmeticWidening_dispatchArtifact_muxFreshLayouts_eq_seed]
  exact (transitionDispatchMuxRuntimes_layouts_eq tm
    { height := height, start := base.gates.length,
      rowBase := rowBase }).symm

/-- Height-affine data embedded as a form over a transition row seed. -/
def transitionDispatchHeightForm
    (form : TransitionAffineNat) : AffineUnaryTripleForm :=
  { constant := form.constant
    first := form.coefficient
    second := 0
    third := 0 }

@[simp] theorem transitionDispatchHeightForm_value
    (form : TransitionAffineNat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue (transitionDispatchHeightForm form)
        (transitionTailAffineSeed seed) = form.eval seed.height := by
  simp [transitionDispatchHeightForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval]

/-- Seven fixed forms describing one label's fresh-coordinate progression. -/
def transitionDispatchMuxDescriptorBlock
    (tm : _root_.Turing.FinTM2) (muxOffset : TransitionAffineNat) :
    List AffineUnaryTripleForm :=
  [ transitionAbsoluteStartForm muxOffset,
    transitionAbsoluteStartForm
      (muxOffset.add (TransitionAffineNat.const 1)),
    transitionAbsoluteStartForm
      (muxOffset.add (TransitionAffineNat.const 2)),
    transitionDispatchHeightForm (TransitionAffineNat.const 0),
    transitionDispatchHeightForm (TransitionAffineNat.const 3),
    transitionDispatchHeightForm (TransitionAffineNat.const 3),
    transitionDispatchHeightForm
      ((transitionCfgBitAffine tm).shiftInput (maxPushesPerStep tm)) ]

/-- Fixed descriptor table for all label muxes, threading the affine gate
offset contributed by every preceding statement and mux. -/
def transitionDispatchMuxDescriptorFormsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List AffineUnaryTripleForm
  | _, [] => []
  | offset, label :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchMuxDescriptorBlock tm muxOffset ++
        transitionDispatchMuxDescriptorFormsForLabels tm
          (muxOffset.add (transitionDispatchMuxGateAffine tm)) labels

/-- Complete verifier-fixed mux progression descriptor table. -/
def transitionDispatchMuxDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchMuxDescriptorFormsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

end CLRS.Chapter34.Turing.CookLevin
