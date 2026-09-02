import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchSeed
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailLayout

/-!
# Complete local transition decomposition from row seeds

This file joins the seed-complete fixed-label dispatch to the already closed
post-dispatch tail coordinates.  One raw transition row seed plus the public
base of the following row now determines every operand view of the canonical
local transition script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Flatten the seed-derived label artifacts to the exact statement-controller
phase list used by one local transition. -/
def transitionDispatchScriptFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineStmtPhase :=
  (transitionDispatchArtifactsFromSeed tm seed).flatMap
    TransitionDispatchLabelArtifact.script

/-- Widening and complete dispatch over one arithmetic public row have exactly
the phase list reconstructed from the raw row seed. -/
theorem arithmeticWidening_compileDispatchScript_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    compileDispatchScript tm height widened.builder widened.constants
        widened.wires widened.valid =
      transitionDispatchScriptFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only
  rw [← compileDispatchArtifacts_flatMap_script]
  rw [arithmeticWidening_dispatchArtifacts_eq_seed]
  rfl

/-- The dispatch field of the canonical local transition script is therefore
seed-only, independently of the following public row. -/
theorem arithmeticTransitionScript_dispatch_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hcurrent : (arithmeticCfgWires tm height rowBase).ValidIn base)
    (next : CfgWires tm height) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base
        (arithmeticCfgWires tm height rowBase) next hcurrent hnext).dispatch =
      transitionDispatchScriptFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  change
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hcurrent
    compileDispatchScript tm height widened.builder widened.constants
      widened.wires widened.valid = _
  exact arithmeticWidening_compileDispatchScript_eq_seed tm height rowBase
    base hcurrent

/-- Every operand view of one local transition, reconstructed from the current
row seed and the following arithmetic public-row base. -/
def transitionScriptDecompositionFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (nextRowBase : Nat) : TransitionScriptDecomposition :=
  { dispatch := transitionDispatchScriptFromSeed tm seed
    fresh := transitionTailLayoutAt tm seed.height seed.start
    dispatched := transitionDispatchOperandLayoutFromSeed tm seed
    nextRow := transitionEqRightOperandsAt tm seed.height nextRowBase }

/-- The complete canonical local transition decomposition equals the direct
row-seed reconstruction. -/
theorem arithmeticTransitionScript_decomposition_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase nextRowBase : Nat)
    (base : CircuitBuilder)
    (hcurrent : (arithmeticCfgWires tm height rowBase).ValidIn base)
    (hnext : (arithmeticCfgWires tm height nextRowBase).ValidIn base) :
    transitionScriptDecomposition
        (compileTransitionScript tm height base
          (arithmeticCfgWires tm height rowBase)
          (arithmeticCfgWires tm height nextRowBase) hcurrent hnext) =
      transitionScriptDecompositionFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase }
        nextRowBase := by
  unfold transitionScriptDecomposition transitionScriptDecompositionFromSeed
  rw [arithmeticTransitionScript_dispatch_eq_seed]
  rw [compileTransitionScript_tailLayout_eq]
  rw [arithmeticTransitionScript_dispatchOperandLayout_eq_seed]
  unfold transitionScriptEqRightOperands transitionEqRightOperandsAt
  rw [compileTransitionScript_eqFrameRights]
  congr 1
  apply List.ofFn_inj.mpr
  funext coordinate
  simp [arithmeticCfgWires]

/-! ## Reassembly to the complete runtime script -/

/-- Reassemble an operand decomposition into the transition controller's
runtime record.  The canonical decomposition has aligned component lists;
`zipWith` merely reconnects the fields that were projected apart. -/
def transitionScriptOfDecomposition
    (decomposition : TransitionScriptDecomposition) : AffineTransitionScript :=
  { dispatch := decomposition.dispatch
    narrowFrames := List.zipWith
      (fun left right : Nat => ({ left := left, right := right } :
        AffineOrFinPairFrame))
      decomposition.dispatched.narrowLefts decomposition.fresh.narrowRights
    narrowSource := decomposition.fresh.narrowSource
    eqFrames := List.zipWith3
      (fun coordinates left right =>
        ({ eqStart := coordinates.1
           left := left
           right := right
           matched := coordinates.2.1
           previous := coordinates.2.2 } : AffineEqFinPairFrame))
      decomposition.fresh.eqCoordinates decomposition.dispatched.eqLefts
      decomposition.nextRow
    finalAnd := decomposition.fresh.finalAnd }

private theorem zipWith_narrowFrame_projections
    (frames : List AffineOrFinPairFrame) :
    List.zipWith
        (fun left right : Nat => ({ left := left, right := right } :
          AffineOrFinPairFrame))
        (frames.map (fun frame => frame.left))
        (frames.map (fun frame => frame.right)) = frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      cases frame
      simp [ih]

private theorem zipWith3_eqFrame_projections
    (frames : List AffineEqFinPairFrame) :
    List.zipWith3
        (fun coordinates left right =>
          ({ eqStart := coordinates.1
             left := left
             right := right
             matched := coordinates.2.1
             previous := coordinates.2.2 } : AffineEqFinPairFrame))
        (frames.map fun frame =>
          (frame.eqStart, frame.matched, frame.previous))
        (frames.map (fun frame => frame.left))
        (frames.map (fun frame => frame.right)) = frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      cases frame
      simp [ih, List.zipWith3]

/-- Extracting all four views from any runtime script and reconnecting them is
an exact left inverse. -/
theorem transitionScriptOfDecomposition_decomposition
    (script : AffineTransitionScript) :
    transitionScriptOfDecomposition (transitionScriptDecomposition script) =
      script := by
  cases script with
  | mk dispatch narrowFrames narrowSource eqFrames finalAnd =>
      simp [transitionScriptOfDecomposition, transitionScriptDecomposition,
        transitionScriptTailLayout, transitionScriptDispatchOperandLayout,
        transitionScriptEqRightOperands,
        zipWith3_eqFrame_projections]

/-- Complete seed-derived runtime script for one local transition. -/
def transitionScriptFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (nextRowBase : Nat) : AffineTransitionScript :=
  transitionScriptOfDecomposition
    (transitionScriptDecompositionFromSeed tm seed nextRowBase)

/-- The actual canonical local transition runtime script is exactly the
seed-derived script, field for field. -/
theorem arithmeticCompileTransitionScript_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase nextRowBase : Nat)
    (base : CircuitBuilder)
    (hcurrent : (arithmeticCfgWires tm height rowBase).ValidIn base)
    (hnext : (arithmeticCfgWires tm height nextRowBase).ValidIn base) :
    compileTransitionScript tm height base
        (arithmeticCfgWires tm height rowBase)
        (arithmeticCfgWires tm height nextRowBase) hcurrent hnext =
      transitionScriptFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase }
        nextRowBase := by
  rw [← transitionScriptOfDecomposition_decomposition
    (compileTransitionScript tm height base
      (arithmeticCfgWires tm height rowBase)
      (arithmeticCfgWires tm height nextRowBase) hcurrent hnext)]
  rw [arithmeticTransitionScript_decomposition_eq_seed]
  rfl

/-! ## Complete adjacent-row family -/

/-- Prefix recursion preserves the complete seed-derived script formula for
any family whose public rows have arithmetic layouts. -/
theorem compileTransitionFamilyScripts_eq_seed_ofFn
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (T : Nat)
    (rows : Fin (T + 1) → CfgWires tm height)
    (hrows : ∀ row, (rows row).ValidIn base)
    (rowBase : Fin (T + 1) → Nat)
    (hrowsEq : ∀ row,
      rows row = arithmeticCfgWires tm height (rowBase row)) :
    compileTransitionFamilyScripts tm height base T rows hrows =
      List.ofFn fun step : Fin T =>
        transitionScriptFromSeed tm
          { height := height
            start := base.gates.length +
              step.val * transitionCircuitGateCost tm height
            rowBase := rowBase step.castSucc }
          (rowBase step.succ) := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts]
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
      have hnextArithmetic :
          (arithmeticCfgWires tm height (rowBase nextRow)).ValidIn
            previous.builder := by
        rw [← hrowsEq nextRow]
        exact (hrows nextRow).mono previous.extension
      have hlast := arithmeticCompileTransitionScript_eq_seed tm height
        (rowBase currentRow) (rowBase nextRow) previous.builder
        hcurrentArithmetic hnextArithmetic
      have hlast' :
          compileTransitionScript tm height previous.builder
              (rows currentRow) (rows nextRow)
              ((hrows currentRow).mono previous.extension)
              ((hrows nextRow).mono previous.extension) =
            transitionScriptFromSeed tm
              { height := height
                start := previous.builder.gates.length
                rowBase := rowBase currentRow }
              (rowBase nextRow) := by
        simpa only [hrowsEq currentRow, hrowsEq nextRow] using hlast
      rw [hlast']
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1
      rw [transitionCircuitFamily_gate_delta]
      simp [currentRow, nextRow]

/-- Dimension-only canonical transition scripts are exactly the arithmetic
row-seed family in adjacent-row order. -/
theorem compileTransitionFamilyScriptsAt_eq_seeds_ofFn
    (tm : _root_.Turing.FinTM2) (height T : Nat) :
    compileTransitionFamilyScriptsAt tm height T =
      List.ofFn fun step : Fin T =>
        transitionScriptFromSeed tm
          { height := height
            start := (arithmeticValidityAt tm height T).builder.gates.length +
              step.val * transitionCircuitGateCost tm height
            rowBase := step.val * cfgBitCount tm height }
          ((step.val + 1) * cfgBitCount tm height) := by
  unfold compileTransitionFamilyScriptsAt
  apply compileTransitionFamilyScripts_eq_seed_ofFn tm height
    (arithmeticValidityAt tm height T).builder T
    (arithmeticRowsAt tm height T).rows
    (fun row =>
      ((arithmeticRowsAt tm height T).rowValid row).mono
        ((arithmeticPoolAt tm height T).extension.trans
          (arithmeticValidityAt tm height T).extension))
    (fun row => row.val * cfgBitCount tm height)
  intro row
  simpa [arithmeticRowsAt] using
    allocateTableauRows_rows_eq_arithmetic tm height T row

/-- The polynomial-time raw-input seed stream expands to the exact complete
canonical transition-family runtime scripts, not merely their phase tags or
tail projections. -/
theorem verifierTransitionRowSeeds_expand_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map (fun seed =>
        transitionScriptFromSeed W.machine.tm seed
          (seed.rowBase + cfgBitCount W.machine.tm seed.height)) =
      compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  rw [compileTransitionFamilyScriptsAt_eq_seeds_ofFn]
  apply List.ofFn_inj.mpr
  funext step
  simp only [Function.comp_apply]
  rw [verifierTransitionStartPolynomial_eval_eq_validity_length]
  congr 2 <;> ring

end CLRS.Chapter34.Turing.CookLevin
