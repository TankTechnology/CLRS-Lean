import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailCoordinates
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyScript

/-!
# Row-seed bridge for Cook--Levin transition tails

The transition-family builder is prefix recursive, whereas the concrete seed
source is row major.  This file proves that both enumerate exactly the same
local starts.  Consequently each raw-input transition seed reconstructs all
fresh post-dispatch coordinates of the corresponding canonical runtime script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All post-dispatch coordinates that do not depend on the dispatched row
payload itself.  Source operands are deliberately retained in the canonical
script; this layout records its complete fresh-wire skeleton. -/
structure TransitionTailLayout where
  narrowRights : List Nat
  narrowSource : Nat
  eqCoordinates : List (Nat × Nat × Nat)
  finalAnd : AffineAndFinPairFrame
deriving DecidableEq, Repr

/-- Extract the fresh-wire skeleton from an actual runtime script. -/
def transitionScriptTailLayout
    (script : AffineTransitionScript) : TransitionTailLayout :=
  { narrowRights := script.narrowFrames.map (fun frame => frame.right)
    narrowSource := script.narrowSource
    eqCoordinates := script.eqFrames.map fun frame =>
      (frame.eqStart, frame.matched, frame.previous)
    finalAnd := script.finalAnd }

/-- Closed post-dispatch skeleton at one local transition start. -/
def transitionTailLayoutAt (tm : _root_.Turing.FinTM2)
    (height start : Nat) : TransitionTailLayout :=
  { narrowRights :=
      (List.range (Fintype.card tm.K * maxPushesPerStep tm)).map
        (fun offset => transitionNarrowStart tm height start + offset)
    narrowSource := transitionNarrowSourceWire tm height start
    eqCoordinates :=
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        (transitionEqStart tm height start + 1 + 6 * coordinate.val,
          transitionEqStart tm height start + 5 + 6 * coordinate.val,
          transitionEqStart tm height start + 6 * coordinate.val)
    finalAnd := transitionFinalAndFrame tm height start }

/-- Every canonical local script has precisely the closed fresh-wire skeleton
at its input builder's current gate length. -/
theorem compileTransitionScript_tailLayout_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    transitionScriptTailLayout
        (compileTransitionScript tm height base current next hcurrent hnext) =
      transitionTailLayoutAt tm height base.gates.length := by
  unfold transitionScriptTailLayout transitionTailLayoutAt
  rw [compileTransitionScript_narrowFrameRights,
    compileTransitionScript_narrowSource_eq,
    compileTransitionScript_eqFrameCoordinates,
    compileTransitionScript_finalAnd_eq]

/-- Prefix recursion enumerates local starts in increasing row order, paying
the exact local transition cost between consecutive scripts. -/
theorem compileTransitionFamilyScripts_tailLayouts_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (T : Nat)
    (rows : Fin (T + 1) → CfgWires tm height)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (compileTransitionFamilyScripts tm height base T rows hrows).map
        transitionScriptTailLayout =
      List.ofFn fun step : Fin T =>
        transitionTailLayoutAt tm height
          (base.gates.length +
            step.val * transitionCircuitGateCost tm height) := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [compileTransitionScript_tailLayout_eq]
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1
      rw [transitionCircuitFamily_gate_delta]
      simp

/-! ## Public next-row equality operands -/

/-- Next-row operands extracted from one actual runtime script. -/
def transitionScriptEqRightOperands
    (script : AffineTransitionScript) : List Nat :=
  script.eqFrames.map (fun frame => frame.right)

/-- Closed canonical next-row operand list at an arithmetic row base. -/
def transitionEqRightOperandsAt (tm : _root_.Turing.FinTM2)
    (height nextRowBase : Nat) : List Nat :=
  List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
    nextRowBase + coordinate.val

/-- Prefix recursion pairs every local script with the immediately following
public tableau row. -/
theorem compileTransitionFamilyScripts_eqRightOperands_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (T : Nat)
    (rows : Fin (T + 1) → CfgWires tm height)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (compileTransitionFamilyScripts tm height base T rows hrows).map
        transitionScriptEqRightOperands =
      List.ofFn fun step : Fin T =>
        List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
          rows step.succ ((cfgSlotEquivFin tm height).symm coordinate) := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts, List.map_append,
        List.map_singleton]
      rw [ih]
      unfold transitionScriptEqRightOperands
      rw [compileTransitionScript_eqFrameRights]
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1

/-- At dimension-only arithmetic rows, all next-row equality operands are one
contiguous row block following the current row seed. -/
theorem compileTransitionFamilyScriptsAt_eqRightOperands_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height T : Nat) :
    (compileTransitionFamilyScriptsAt tm height T).map
        transitionScriptEqRightOperands =
      List.ofFn fun step : Fin T =>
        transitionEqRightOperandsAt tm height
          ((step.val + 1) * cfgBitCount tm height) := by
  unfold compileTransitionFamilyScriptsAt
  rw [compileTransitionFamilyScripts_eqRightOperands_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext step
  unfold transitionEqRightOperandsAt
  apply List.ofFn_inj.mpr
  funext coordinate
  let row : Fin (tableauRowCount T) :=
    ⟨step.val + 1, by simp [tableauRowCount]⟩
  have hrow := allocateTableauRows_rows_eq_arithmetic
    tm height T row
  have hstep : step.succ = row := by
    apply Fin.ext
    rfl
  have hrowEq :
      (arithmeticRowsAt tm height T).rows step.succ =
        arithmeticCfgWires tm height
          ((step.val + 1) * cfgBitCount tm height) := by
    rw [hstep]
    simpa [arithmeticRowsAt, row] using hrow
  rw [hrowEq]
  simp [arithmeticCfgWires]

/-- Raw-input transition seeds reconstruct every canonical public next-row
equality operand, not merely the number of equality coordinates. -/
theorem verifierTransitionRowSeeds_expand_eqRightOperands_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map (fun seed =>
        transitionEqRightOperandsAt W.machine.tm seed.height
          (seed.rowBase + cfgBitCount W.machine.tm seed.height)) =
      (compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)).map
          transitionScriptEqRightOperands := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  rw [compileTransitionFamilyScriptsAt_eqRightOperands_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext step
  simp only [Function.comp_apply]
  unfold transitionEqRightOperandsAt
  apply List.ofFn_inj.mpr
  funext coordinate
  ring

/-! ## The unique dispatched-row operand boundary -/

/-- Source operands in the post-dispatch tail: overflow coordinates for
narrowing and the public-height projection for row equality. -/
structure TransitionDispatchOperandLayout where
  narrowLefts : List Nat
  eqLefts : List Nat
deriving DecidableEq, Repr

/-- Extract all dispatched-row operands from an actual transition script. -/
def transitionScriptDispatchOperandLayout
    (script : AffineTransitionScript) : TransitionDispatchOperandLayout :=
  { narrowLefts := script.narrowFrames.map (fun frame => frame.left)
    eqLefts := script.eqFrames.map (fun frame => frame.left) }

/-- The two fixed projections of one semantic dispatched workspace row. -/
def transitionDispatchOperandLayout (tm : _root_.Turing.FinTM2)
    (height : Nat) (dispatched : CfgWires tm (workHeight tm height)) :
    TransitionDispatchOperandLayout :=
  { narrowLefts := (narrowCfgOverflowWires dispatched).reverse
    eqLefts := List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
      narrowCfgWireProjection dispatched
        ((cfgSlotEquivFin tm height).symm coordinate) }

/-- Both post-dispatch source-operand families reconstructed directly from
the raw transition seed.  The intervening semantic dispatch row has already
been eliminated by the arithmetic `cfgMux` output theorem. -/
def transitionDispatchOperandLayoutFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchOperandLayout :=
  transitionDispatchOperandLayout tm seed.height
    (transitionDispatchOutputWires tm seed)

/-- Both non-arithmetic post-dispatch operand families are projections of the
same canonical `dispatchLabels` output row. -/
theorem compileTransitionScript_dispatchOperandLayout_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    transitionScriptDispatchOperandLayout
        (compileTransitionScript tm height base current next hcurrent hnext) =
      transitionDispatchOperandLayout tm height
        (dispatchLabels tm height
          (widenCfg base current hcurrent).builder
          (widenCfg base current hcurrent).constants
          (widenCfg base current hcurrent).wires
          (widenCfg base current hcurrent).valid).wires := by
  unfold transitionScriptDispatchOperandLayout
    transitionDispatchOperandLayout
  rw [compileTransitionScript_narrowFrameLefts,
    compileTransitionScript_eqFrameLefts]

/-- For an arithmetic public tableau row, every narrowing and equality source
operand in the actual transition script is a closed function of the row seed.
No semantic statement result remains in this post-dispatch tail interface. -/
theorem arithmeticTransitionScript_dispatchOperandLayout_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hcurrent : (arithmeticCfgWires tm height rowBase).ValidIn base)
    (next : CfgWires tm height) (hnext : next.ValidIn base) :
    transitionScriptDispatchOperandLayout
        (compileTransitionScript tm height base
          (arithmeticCfgWires tm height rowBase) next hcurrent hnext) =
      transitionDispatchOperandLayoutFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  rw [compileTransitionScript_dispatchOperandLayout_eq]
  unfold transitionDispatchOperandLayoutFromSeed
  rw [arithmeticWidening_dispatchLabels_wires_eq_seed]

/-- Prefix recursion preserves the seed-only dispatched-operand formula for
any family whose public rows have arithmetic wire layouts. -/
theorem compileTransitionFamilyScripts_dispatchOperandLayouts_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (T : Nat)
    (rows : Fin (T + 1) → CfgWires tm height)
    (hrows : ∀ row, (rows row).ValidIn base)
    (rowBase : Fin (T + 1) → Nat)
    (hrowsEq : ∀ row,
      rows row = arithmeticCfgWires tm height (rowBase row)) :
    (compileTransitionFamilyScripts tm height base T rows hrows).map
        transitionScriptDispatchOperandLayout =
      List.ofFn fun step : Fin T =>
        transitionDispatchOperandLayoutFromSeed tm
          { height := height
            start := base.gates.length +
              step.val * transitionCircuitGateCost tm height
            rowBase := rowBase step.castSucc } := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts, List.map_append,
        List.map_singleton]
      have hprefixEq : ∀ row : Fin (T + 1),
          rows row.castSucc =
            arithmeticCfgWires tm height (rowBase row.castSucc) :=
        fun row => hrowsEq row.castSucc
      rw [ih base (fun row => rows row.castSucc)
        (fun row => hrows row.castSucc)
        (fun row => rowBase row.castSucc) hprefixEq]
      let previous := transitionCircuitFamily tm height base
        (fun row => rows row.castSucc) (fun row => hrows row.castSucc)
      let currentRow : Fin (T + 2) := (Fin.last T).castSucc
      let nextRow : Fin (T + 2) := Fin.last (T + 1)
      have hcurrentArithmetic :
          (arithmeticCfgWires tm height (rowBase currentRow)).ValidIn
            previous.builder := by
        rw [← hrowsEq currentRow]
        exact (hrows currentRow).mono previous.extension
      have hlast := arithmeticTransitionScript_dispatchOperandLayout_eq_seed
        tm height (rowBase currentRow) previous.builder hcurrentArithmetic
        (rows nextRow) ((hrows nextRow).mono previous.extension)
      have hlast' :
          transitionScriptDispatchOperandLayout
              (compileTransitionScript tm height previous.builder
                (rows currentRow) (rows nextRow)
                ((hrows currentRow).mono previous.extension)
                ((hrows nextRow).mono previous.extension)) =
            transitionDispatchOperandLayoutFromSeed tm
              { height := height
                start := previous.builder.gates.length
                rowBase := rowBase currentRow } := by
        simpa only [hrowsEq currentRow] using hlast
      rw [hlast']
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1
      rw [transitionCircuitFamily_gate_delta]
      simp [currentRow]

/-- The canonical dimension-only family has the closed dispatched-operand
layout obtained from the row-major arithmetic transition seeds. -/
theorem compileTransitionFamilyScriptsAt_dispatchOperandLayouts_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height T : Nat) :
    (compileTransitionFamilyScriptsAt tm height T).map
        transitionScriptDispatchOperandLayout =
      List.ofFn fun step : Fin T =>
        transitionDispatchOperandLayoutFromSeed tm
          { height := height
            start := (arithmeticValidityAt tm height T).builder.gates.length +
              step.val * transitionCircuitGateCost tm height
            rowBase := step.val * cfgBitCount tm height } := by
  unfold compileTransitionFamilyScriptsAt
  apply compileTransitionFamilyScripts_dispatchOperandLayouts_eq_ofFn
    tm height (arithmeticValidityAt tm height T).builder T
    (arithmeticRowsAt tm height T).rows
    (fun row =>
      ((arithmeticRowsAt tm height T).rowValid row).mono
        ((arithmeticPoolAt tm height T).extension.trans
          (arithmeticValidityAt tm height T).extension))
    (fun row => row.val * cfgBitCount tm height)
  intro row
  simpa [arithmeticRowsAt] using
    allocateTableauRows_rows_eq_arithmetic tm height T row

/-- The raw-input transition seed stream reconstructs every dispatched-row
operand used by the canonical transition-family scripts, in exact row order. -/
theorem verifierTransitionRowSeeds_expand_dispatchOperandLayouts_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map
        (transitionDispatchOperandLayoutFromSeed W.machine.tm) =
      (compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)).map
          transitionScriptDispatchOperandLayout := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  rw [compileTransitionFamilyScriptsAt_dispatchOperandLayouts_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext step
  simp only [Function.comp_apply]
  rw [verifierTransitionStartPolynomial_eval_eq_validity_length]

/-- Four disjoint views needed to reconstruct a complete transition script:
the statement/dispatch phases, the fresh tail skeleton, the single dispatched
row's fixed projections, and the public next-row operands. -/
structure TransitionScriptDecomposition where
  dispatch : List AffineStmtPhase
  fresh : TransitionTailLayout
  dispatched : TransitionDispatchOperandLayout
  nextRow : List Nat
deriving Repr

/-- Extract the complete operand decomposition from one runtime script. -/
def transitionScriptDecomposition
    (script : AffineTransitionScript) : TransitionScriptDecomposition :=
  { dispatch := script.dispatch
    fresh := transitionScriptTailLayout script
    dispatched := transitionScriptDispatchOperandLayout script
    nextRow := transitionScriptEqRightOperands script }

/-- The canonical local script decomposition isolates exactly one remaining
structured object: the fixed-machine dispatch computation and its output row.
Every other coordinate is fixed by the local start or the public next row. -/
theorem compileTransitionScript_decomposition_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    transitionScriptDecomposition
        (compileTransitionScript tm height base current next hcurrent hnext) =
      let widened := widenCfg base current hcurrent
      let dispatched := dispatchLabels tm height widened.builder
        widened.constants widened.wires widened.valid
      { dispatch := compileDispatchScript tm height widened.builder
          widened.constants widened.wires widened.valid
        fresh := transitionTailLayoutAt tm height base.gates.length
        dispatched := transitionDispatchOperandLayout tm height
          dispatched.wires
        nextRow := List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
          next ((cfgSlotEquivFin tm height).symm coordinate) } := by
  simp only [transitionScriptDecomposition]
  rw [compileTransitionScript_tailLayout_eq,
    compileTransitionScript_dispatchOperandLayout_eq]
  unfold transitionScriptEqRightOperands
  rw [compileTransitionScript_eqFrameRights]
  rfl

/-- Expand one raw-input row seed to the skeleton expected by the verified
local transition controller. -/
def expandTransitionRowSeedTailLayout
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionTailLayout :=
  transitionTailLayoutAt tm seed.height seed.start

/-- Raw-input seed order is byte-for-byte aligned with the canonical
transition-family script order at the level of all fresh tail coordinates. -/
theorem verifierTransitionRowSeeds_expand_tailLayouts_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map
        (expandTransitionRowSeedTailLayout W.machine.tm) =
      (compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)).map
          transitionScriptTailLayout := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  unfold compileTransitionFamilyScriptsAt
  rw [compileTransitionFamilyScripts_tailLayouts_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext row
  rw [verifierTransitionStartPolynomial_eval_eq_validity_length]
  rfl

end CLRS.Chapter34.Turing.CookLevin
