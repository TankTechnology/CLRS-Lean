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

end CLRS.Chapter34.Turing.CookLevin
