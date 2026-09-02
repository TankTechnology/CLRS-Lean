import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchMuxFrames

/-!
# Whole-row mux views for recursively compiled statements

This module replaces the terminal-arm-only mux view with one whose true and
false rows use the total statement-output route.  Consequently either arm may
contain arbitrarily nested branches while the existing canonical mux frame
assembler remains unchanged.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Canonical mux invocation whose two input rows are total recursive
statement routes. -/
def transitionStmtRecursiveBranchMuxInvocationView
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) : TransitionDispatchMuxInvocationView :=
  let trueContext := transitionStmtBranchTrueContext tm context test
  let falseContext :=
    transitionStmtBranchFalseContext tm context test whenTrue
  let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
    whenFalse hsupport
  let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
    whenFalse hsupport
  { selector := affineUnaryTripleFormValue
      (transitionStmtBranchSelectorForm tm labelOffset context test)
      (transitionTailAffineSeed seed)
    coordinates := transitionStmtBranchMuxCoordinates tm seed labelOffset
      context test whenTrue whenFalse
    whenTrue := transitionStmtOutputRouteValues tm seed labelOffset
      trueContext whenTrue htrueSupport
    whenFalse := transitionStmtOutputRouteValues tm seed labelOffset
      falseContext whenFalse hfalseSupport }

/-- Generic reassembly of a canonical mux invocation from its four rows. -/
theorem transitionCanonicalMuxInvocationView_frames
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    TransitionDispatchMuxInvocationView.frames
        { selector := selector
          coordinates := List.ofFn fun coordinate : Fin width =>
            (start, start + 1 + 3 * coordinate.val,
              start + 2 + 3 * coordinate.val)
          whenTrue := List.ofFn whenTrue
          whenFalse := List.ofFn whenFalse } =
      affineMuxFinCanonicalFrames start selector width whenTrue whenFalse := by
  let frames := affineMuxFinCanonicalFrames start selector width
    whenTrue whenFalse
  have hcoordinates :
      frames.map (fun frame =>
        (frame.selectorNot, frame.trueArm, frame.falseArm)) =
        List.ofFn fun coordinate : Fin width =>
          (start, start + 1 + 3 * coordinate.val,
            start + 2 + 3 * coordinate.val) :=
    affineMuxFinCanonicalFrames_freshCoordinates start selector width
      whenTrue whenFalse
  have htrue : frames.map (fun frame => frame.whenTrue) =
      List.ofFn whenTrue :=
    affineMuxFinCanonicalFrames_whenTrue_values start selector width
      whenTrue whenFalse
  have hfalse : frames.map (fun frame => frame.whenFalse) =
      List.ofFn whenFalse :=
    affineMuxFinCanonicalFrames_whenFalse_values start selector width
      whenTrue whenFalse
  rw [← hcoordinates, ← htrue, ← hfalse]
  exact affineMuxFinCanonicalFrames_reassemble start selector width
    whenTrue whenFalse

/-- Recursive arm routes and fresh-coordinate rows have one common width. -/
theorem transitionStmtRecursiveBranchMuxInvocationView_rowAligned
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (htrueCapacity : ∀ result,
      transitionStmtLinearResult tm
        (transitionStmtBranchTrueContext tm context test) whenTrue
        (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
          hsupport) = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤
            workHeight tm seed.height)
    (hfalseCapacity : ∀ result,
      transitionStmtLinearResult tm
        (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
        (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
          hsupport) = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤
            workHeight tm seed.height) :
    (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
      context test whenTrue whenFalse hsupport).RowAligned := by
  have htrue := transitionStmtOutputRouteValues_eq_output tm seed hwork
    labelOffset (transitionStmtBranchTrueContext tm context test) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
    htrueCapacity
  have hfalse := transitionStmtOutputRouteValues_eq_output tm seed hwork
    labelOffset (transitionStmtBranchFalseContext tm context test whenTrue)
    whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
    hfalseCapacity
  unfold TransitionDispatchMuxInvocationView.RowAligned
    transitionStmtRecursiveBranchMuxInvocationView
    transitionStmtBranchMuxCoordinates
  dsimp only
  rw [htrue, hfalse]
  simp [transitionCfgWireValues]

/-- The recursive invocation reassembles to the literal whole-row mux in the
ordinary statement semantics. -/
theorem transitionStmtRecursiveBranchMuxInvocationView_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (htrueCapacity : ∀ result,
      transitionStmtLinearResult tm
        (transitionStmtBranchTrueContext tm context test) whenTrue
        (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
          hsupport) = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤
            workHeight tm seed.height)
    (hfalseCapacity : ∀ result,
      transitionStmtLinearResult tm
        (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
        (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
          hsupport) = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤
            workHeight tm seed.height) :
    (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
      context test whenTrue whenFalse hsupport).frames =
      affineMuxFinCanonicalFrames
        (transitionStmtBranchSemanticMuxStart tm seed labelOffset context
          test whenTrue whenFalse)
        (transitionStmtBranchSemanticSelector tm seed labelOffset context test)
        (cfgBitCount tm (workHeight tm seed.height))
        (fun coordinate =>
          transitionStmtBranchSemanticTrueWires tm seed labelOffset context
            test whenTrue whenFalse hsupport
            ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm coordinate))
        (fun coordinate =>
          transitionStmtBranchSemanticFalseWires tm seed labelOffset context
            test whenTrue whenFalse hsupport
            ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
              coordinate)) := by
  have hselector := transitionStmtBranchSelectorForm_value tm seed
    labelOffset context test
  have hmuxStart := transitionStmtBranchMuxStartForm_value tm seed hwork
    labelOffset context test whenTrue whenFalse
  have htrue := transitionStmtOutputRouteValues_eq_output tm seed hwork
    labelOffset (transitionStmtBranchTrueContext tm context test) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
    htrueCapacity
  have hfalse := transitionStmtOutputRouteValues_eq_output tm seed hwork
    labelOffset (transitionStmtBranchFalseContext tm context test whenTrue)
    whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
    hfalseCapacity
  simp only [transitionStmtBranchTrueContext,
    TransitionStmtAffineContext.rowWires,
    TransitionStmtAffineContext.advance_wires] at htrue
  simp only [transitionStmtBranchFalseContext,
    TransitionStmtAffineContext.rowWires,
    TransitionStmtAffineContext.advance_wires] at hfalse
  have htrueSemantic :
      transitionStmtOutputRouteValues tm seed labelOffset
          (transitionStmtBranchTrueContext tm context test) whenTrue
          (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
            hsupport) =
        transitionCfgWireValues tm (workHeight tm seed.height)
          (transitionStmtBranchSemanticTrueWires tm seed labelOffset context
            test whenTrue whenFalse hsupport) := by
    simpa [transitionStmtBranchSemanticTrueWires,
      transitionStmtBranchTrueContext,
      transitionStmtBranchPredicateCost,
      TransitionStmtAffineContext.advance,
      TransitionAffineNat.eval_add,
      TransitionStmtAffineContext.rowWires, Nat.add_assoc] using htrue
  have hfalseSemantic :
      transitionStmtOutputRouteValues tm seed labelOffset
          (transitionStmtBranchFalseContext tm context test whenTrue)
          whenFalse
          (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
            hsupport) =
        transitionCfgWireValues tm (workHeight tm seed.height)
          (transitionStmtBranchSemanticFalseWires tm seed labelOffset context
            test whenTrue whenFalse hsupport) := by
    simpa [transitionStmtBranchSemanticFalseWires,
      transitionStmtBranchFalseContext,
      transitionStmtBranchPredicateCost,
      TransitionStmtAffineContext.advance,
      TransitionAffineNat.eval_add,
      TransitionStmtAffineContext.rowWires,
      compileStmtGateAffine_eval tm whenTrue
        (workHeight tm seed.height) hwork,
      Nat.add_assoc] using hfalse
  unfold transitionStmtRecursiveBranchMuxInvocationView
    transitionStmtBranchMuxCoordinates
  dsimp only
  rw [hselector, hmuxStart, htrueSemantic, hfalseSemantic]
  unfold transitionCfgWireValues transitionStmtBranchSemanticMuxStart
    transitionStmtBranchSemanticSelector
  exact transitionCanonicalMuxInvocationView_frames _ _ _ _ _

end CLRS.Chapter34.Turing.CookLevin
