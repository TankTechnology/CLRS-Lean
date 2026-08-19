import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidening
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DispatchController

/-!
# Label-local layout of the Cook--Levin transition dispatch

The semantic dispatch compiler is recursive over the fixed machine's finite
program labels.  This module exposes one artifact per label, proves that their
flattening is exactly the existing continuous dispatch script, and closes the
label-start and selector coordinates arithmetically from a transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## One artifact per fixed program label -/

/-- Runtime data contributed by one label arm: its recursive statement script
followed by the complete-row selector mux. -/
structure TransitionDispatchLabelArtifact (tm : _root_.Turing.FinTM2) where
  label : tm.Λ
  start : Nat
  statement : List AffineStmtPhase
  selector : Nat
  muxFrames : List AffineMuxFinPairFrame

/-- Flatten one label artifact back to the statement controller's phase list. -/
def TransitionDispatchLabelArtifact.script
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) : List AffineStmtPhase :=
  artifact.statement ++ [.mux artifact.selector artifact.muxFrames]

/-- The proof-carrying dispatch recursion, packaged at label boundaries. -/
def compileDispatchLabelsListArtifacts
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base) :
    List tm.Λ → List (TransitionDispatchLabelArtifact tm)
  | [] => []
  | label :: labels =>
      let compiled := compileStmt tm (workHeight tm height) base pool source
        hsource (tm.m label) (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let hselector : compiled.builder.WireValid selector :=
        compiled.extension.wireValid (hsource.label _)
      let selected := cfgMux compiled.builder selector compiled.wires fallback
        hselector compiled.valid (hfallback.mono compiled.extension)
      let stepExtension := compiled.extension.trans selected.extension
      { label := label
        start := base.gates.length
        statement := compileStmtScript tm (workHeight tm height) base pool
          source hsource (tm.m label) (stmtPushSet_program_subset tm label)
        selector := selector
        muxFrames := affineMuxFinCanonicalFrames
          compiled.builder.gates.length selector _
          (fun coordinate => compiled.wires
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate))
          (fun coordinate => fallback
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate)) } ::
        compileDispatchLabelsListArtifacts tm height selected.builder
          (pool.mono stepExtension) source selected.wires
          (hsource.mono stepExtension) selected.valid labels

/-- Flattening the label artifacts recovers the pre-existing canonical
continuous dispatch script exactly. -/
theorem compileDispatchLabelsListArtifacts_flatMap_script
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).flatMap
        TransitionDispatchLabelArtifact.script =
      compileDispatchLabelsListScript tm height base pool source fallback
        hsource hfallback labels := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts,
        compileDispatchLabelsListScript, List.flatMap_cons]
      rw [ih]
      rfl

/-- Artifact packaging preserves the canonical label order exactly. -/
theorem compileDispatchLabelsListArtifacts_labels_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).map (fun artifact => artifact.label) =
      labels := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts, List.map_cons]
      congr 1
      exact ih _ _ _ _ _ _

/-- Complete canonical-label artifact family. -/
def compileDispatchArtifacts
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm height))
    (hvalid : source.ValidIn base) :
    List (TransitionDispatchLabelArtifact tm) :=
  compileDispatchLabelsListArtifacts tm height base pool source source hvalid
    hvalid (programLabels tm)

/-- The complete artifact family is an exact label-boundary partition of the
canonical dispatch script. -/
theorem compileDispatchArtifacts_flatMap_script
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm height))
    (hvalid : source.ValidIn base) :
    (compileDispatchArtifacts tm height base pool source hvalid).flatMap
        TransitionDispatchLabelArtifact.script =
      compileDispatchScript tm height base pool source hvalid := by
  exact compileDispatchLabelsListArtifacts_flatMap_script tm height base pool
    source source hvalid hvalid (programLabels tm)

/-- Complete dispatch has one artifact for each fixed machine label. -/
@[simp] theorem compileDispatchArtifacts_length
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm height))
    (hvalid : source.ValidIn base) :
    (compileDispatchArtifacts tm height base pool source hvalid).length =
      labelCount tm := by
  have hlabels := compileDispatchLabelsListArtifacts_labels_eq tm height base
    pool source source hvalid hvalid (programLabels tm)
  have := congrArg List.length hlabels
  simpa [compileDispatchArtifacts, programLabels] using this

/-! ## Closed label starts -/

/-- First fresh gate of each label arm in a fixed dispatch suffix. -/
def transitionDispatchLabelStarts (tm : _root_.Turing.FinTM2)
    (height : Nat) : Nat → List tm.Λ → List Nat
  | _, [] => []
  | start, label :: labels =>
      start :: transitionDispatchLabelStarts tm height
        (start + compileStmtGateCost tm (workHeight tm height) (tm.m label) +
          (3 * cfgBitCount tm (workHeight tm height) + 1)) labels

/-- Complete canonical dispatch starts decoded from a local transition seed.
The dispatch begins after the seed's two widening constants. -/
def transitionDispatchStarts (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchLabelStarts tm seed.height (seed.start + 2)
    (programLabels tm)

/-- Artifact recursion advances by the exact statement-plus-mux cost, so all
label starts are functions only of the initial gate index and fixed machine. -/
theorem compileDispatchLabelsListArtifacts_starts_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).map (fun artifact => artifact.start) =
      transitionDispatchLabelStarts tm height base.gates.length labels := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts, List.map_cons,
        transitionDispatchLabelStarts]
      congr 1
      rw [ih]
      congr 2
      rw [cfgMux_gate_delta, compileStmt_gate_delta]

/-- The proof-carrying widening feeds dispatch at exactly the seed-derived
label starts. -/
theorem arithmeticWidening_dispatchArtifact_starts_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map (fun artifact => artifact.start) =
      transitionDispatchStarts tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_starts_eq]
  unfold transitionDispatchStarts
  rw [widenCfg_gate_delta]

/-! ## Arithmetic fresh skeleton of every label mux -/

/-- Fresh coordinates of one label's whole-workspace selection.  The two arm
operands are deliberately excluded; they are the remaining statement-output
and accumulated-fallback rows. -/
structure TransitionDispatchMuxFreshLayout where
  selector : Nat
  coordinates : List (Nat × Nat × Nat)

/-- Extract the selector-negation and two AND outputs from actual mux frames. -/
def TransitionDispatchLabelArtifact.muxFreshLayout
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) :
    TransitionDispatchMuxFreshLayout :=
  { selector := artifact.selector
    coordinates := artifact.muxFrames.map fun frame =>
      (frame.selectorNot, frame.trueArm, frame.falseArm) }

/-- Closed fresh skeleton of a canonical finite mux. -/
def transitionDispatchMuxFreshLayout (start selector width : Nat) :
    TransitionDispatchMuxFreshLayout :=
  { selector := selector
    coordinates := List.ofFn fun coordinate : Fin width =>
      (start, start + 1 + 3 * coordinate.val,
        start + 2 + 3 * coordinate.val) }

private theorem affineMuxFinCanonicalFrames_freshCoordinates
    (start selector : Nat) :
    ∀ (width : Nat) (whenTrue whenFalse : Fin width → CircuitBuilder.Wire),
      (affineMuxFinCanonicalFrames start selector width
          whenTrue whenFalse).map (fun frame =>
            (frame.selectorNot, frame.trueArm, frame.falseArm)) =
        List.ofFn fun coordinate : Fin width =>
          (start, start + 1 + 3 * coordinate.val,
            start + 2 + 3 * coordinate.val) := by
  intro width
  induction width with
  | zero =>
      intro whenTrue whenFalse
      rfl
  | succ width ih =>
      intro whenTrue whenFalse
      simp only [affineMuxFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

/-- Every label artifact's mux fresh skeleton is determined recursively by
the label start and that statement's exact cost. -/
def transitionDispatchMuxFreshLayouts
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    Nat → List tm.Λ → List TransitionDispatchMuxFreshLayout
  | _, [] => []
  | start, label :: labels =>
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm height) (tm.m label)
      transitionDispatchMuxFreshLayout muxStart selector
          (cfgBitCount tm (workHeight tm height)) ::
        transitionDispatchMuxFreshLayouts tm height source
          (muxStart + (3 * cfgBitCount tm (workHeight tm height) + 1))
          labels

/-- Label artifacts have exactly the recursive arithmetic mux skeleton. -/
theorem compileDispatchLabelsListArtifacts_muxFreshLayouts_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).map
          TransitionDispatchLabelArtifact.muxFreshLayout =
      transitionDispatchMuxFreshLayouts tm height source base.gates.length
        labels := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts,
        transitionDispatchMuxFreshLayouts, List.map_cons]
      congr 1
      · unfold TransitionDispatchLabelArtifact.muxFreshLayout
          transitionDispatchMuxFreshLayout
        rw [affineMuxFinCanonicalFrames_freshCoordinates]
        rw [compileStmt_gate_delta]
      · rw [ih]
        congr 2
        rw [cfgMux_gate_delta, compileStmt_gate_delta]

/-- Seed-only mux skeleton for the complete fixed-label dispatch. -/
def transitionDispatchMuxFreshLayoutsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List TransitionDispatchMuxFreshLayout :=
  transitionDispatchMuxFreshLayouts tm seed.height
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2) (programLabels tm)

/-- Actual widening plus label artifacts use exactly the seed-only mux fresh
skeleton. -/
theorem arithmeticWidening_dispatchArtifact_muxFreshLayouts_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map
          TransitionDispatchLabelArtifact.muxFreshLayout =
      transitionDispatchMuxFreshLayoutsFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_muxFreshLayouts_eq]
  unfold transitionDispatchMuxFreshLayoutsFromSeed
  rw [widenCfg_arithmetic_wires_eq, widenCfg_gate_delta]

/-! ## Arithmetic output row of the complete dispatch -/

/-- Whole-row mux outputs occupy every third wire after the shared negation. -/
def arithmeticMuxCfgWires (tm : _root_.Turing.FinTM2)
    (height muxStart : Nat) : CfgWires tm height :=
  fun slot => muxStart + 3 + 3 * (cfgSlotEquivFin tm height slot).val

/-- The proof-carrying whole-row mux returns exactly the arithmetic output
bundle, independently of both arm payloads. -/
theorem cfgMux_wires_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm height)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    (cfgMux base selector whenTrue whenFalse
      hselector htrue hfalse).wires =
      arithmeticMuxCfgWires tm height base.gates.length := by
  funext slot
  rw [cfgMux_wire_eq]
  rfl

/-- Output-row wires after a dispatch suffix.  Every nonempty step replaces
the fallback with its fresh arithmetic mux row. -/
def transitionDispatchListOutputWires
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    Nat → List tm.Λ → CfgWires tm (workHeight tm height) →
      CfgWires tm (workHeight tm height)
  | _, [], fallback => fallback
  | start, label :: labels, _fallback =>
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm height) (tm.m label)
      transitionDispatchListOutputWires tm height
        (muxStart + (3 * cfgBitCount tm (workHeight tm height) + 1))
        labels
        (arithmeticMuxCfgWires tm (workHeight tm height) muxStart)

/-- The semantic dispatch recursion's output wires obey the pure arithmetic
suffix recurrence. -/
theorem dispatchLabelsList_wires_eq_arithmetic
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (dispatchLabelsList tm height base pool source fallback hsource hfallback
      labels).wires =
      transitionDispatchListOutputWires tm height base.gates.length labels
        fallback := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [dispatchLabelsList, transitionDispatchListOutputWires]
      rw [ih]
      rw [cfgMux_wires_eq_arithmetic]
      congr 2
      · rw [cfgMux_gate_delta, compileStmt_gate_delta]
      · rw [compileStmt_gate_delta]

/-- Complete dispatched workspace row decoded from one local transition seed. -/
def transitionDispatchOutputWires (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : CfgWires tm (workHeight tm seed.height) :=
  transitionDispatchListOutputWires tm seed.height (seed.start + 2)
    (programLabels tm)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- Actual proof-carrying widening and finite-label dispatch return exactly the
seed-only arithmetic workspace row. -/
theorem arithmeticWidening_dispatchLabels_wires_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (dispatchLabels tm height widened.builder widened.constants widened.wires
      widened.valid).wires =
      transitionDispatchOutputWires tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [dispatchLabels]
  rw [dispatchLabelsList_wires_eq_arithmetic]
  unfold transitionDispatchOutputWires
  rw [widenCfg_arithmetic_wires_eq, widenCfg_gate_delta]

/-! ## Seed-derived selectors -/

/-- Selector wire for every label arm, directly from one transition seed's
arithmetic widened row. -/
def transitionDispatchSelectors (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : List Nat :=
  (programLabels tm).map fun label =>
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase).label
      (Fin.castSucc (labelEquivFin tm label))

/-- Selector wires are simply the public row's contiguous label block; they
do not depend on the fresh transition start. -/
theorem transitionDispatchSelectors_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchSelectors tm seed =
      (programLabels tm).map fun label =>
        seed.rowBase + (1 + (labelEquivFin tm label).val) := by
  unfold transitionDispatchSelectors
  apply List.map_congr_left
  intro label hlabel
  change (arithmeticCfgWires tm seed.height seed.rowBase).label
      (Fin.castSucc (labelEquivFin tm label)) = _
  rw [arithmeticCfgWires_label]
  rfl

/-- Every label artifact reads its selector from the unchanged dispatch source
row, independent of the accumulated fallback. -/
theorem compileDispatchLabelsListArtifacts_selectors_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).map (fun artifact => artifact.selector) =
      labels.map fun label =>
        source.label (Fin.castSucc (labelEquivFin tm label)) := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts, List.map_cons]
      congr 1
      exact ih _ _ _ _ _ _

/-- For an arithmetic public row, the actual proof-carrying widening and
dispatch artifacts use exactly the selector list decoded from the row seed. -/
theorem arithmeticWidening_dispatchArtifact_selectors_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map
          (fun artifact => artifact.selector) =
      transitionDispatchSelectors tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_selectors_eq]
  unfold transitionDispatchSelectors
  rw [widenCfg_arithmetic_wires_eq]

end CLRS.Chapter34.Turing.CookLevin
