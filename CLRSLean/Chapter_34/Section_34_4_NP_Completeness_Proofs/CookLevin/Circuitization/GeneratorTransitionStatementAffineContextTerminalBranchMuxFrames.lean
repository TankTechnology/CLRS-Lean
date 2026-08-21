import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchMux
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketWellFormed

/-!
# Canonical whole-row mux frames for terminal statement branches

The two routed terminal arms are now reassembled with the existing generic
mux invocation view.  The main theorem identifies the reconstructed frames
with the literal canonical mux occurring in `transitionStmtScript`; hence the
same runtime mux controller can consume this branch layer without rebuilding
either arm.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Runtime predicate wire of a branch starting in an affine context. -/
def transitionStmtBranchSemanticSelector
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool) : Nat :=
  (CircuitBuilder.disjunctionGateTrace
    ((seed.start + labelOffset.eval seed.height) +
      context.gateOffset.eval (workHeight tm seed.height))
    (oneHotPredicateWires
      (context.rowWires tm seed labelOffset).state
      (stmtPredicateTable tm test))).wire

/-- Runtime start of the final whole-row branch mux. -/
def transitionStmtBranchSemanticMuxStart
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  ((seed.start + labelOffset.eval seed.height) +
      context.gateOffset.eval (workHeight tm seed.height)) +
    ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1) +
    compileStmtGateCost tm (workHeight tm seed.height) whenTrue +
    compileStmtGateCost tm (workHeight tm seed.height) whenFalse

/-- Semantic output bundle of the true arm at its literal script start. -/
def transitionStmtBranchSemanticTrueWires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    CfgWires tm (workHeight tm seed.height) :=
  transitionStmtOutputWires tm (workHeight tm seed.height)
    seed.start (seed.start + 1)
    (((seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height)) +
      ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1))
    (context.rowWires tm seed labelOffset) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)

/-- Semantic output bundle of the false arm at its literal script start. -/
def transitionStmtBranchSemanticFalseWires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    CfgWires tm (workHeight tm seed.height) :=
  transitionStmtOutputWires tm (workHeight tm seed.height)
    seed.start (seed.start + 1)
    ((((seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height)) +
      ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)) +
      compileStmtGateCost tm (workHeight tm seed.height) whenTrue)
    (context.rowWires tm seed labelOffset) whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)

/-- Canonical fresh triples allocated by the final whole-row mux. -/
def transitionStmtBranchMuxCoordinates
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    List (Nat × Nat × Nat) :=
  let muxStart := affineUnaryTripleFormValue
    (transitionStmtBranchMuxStartForm tm labelOffset context test
      whenTrue whenFalse)
    (transitionTailAffineSeed seed)
  List.ofFn fun coordinate : Fin (cfgBitCount tm (workHeight tm seed.height)) =>
    (muxStart, muxStart + 1 + 3 * coordinate.val,
      muxStart + 2 + 3 * coordinate.val)

/-- Complete variable-width mux invocation reconstructed from the fixed
selector/start forms and the two compact terminal routes. -/
def TransitionStmtTerminalBranchPlan.muxInvocationView
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (plan : TransitionStmtTerminalBranchPlan tm) :
    TransitionDispatchMuxInvocationView :=
  { selector := affineUnaryTripleFormValue
      (transitionStmtBranchSelectorForm tm labelOffset context test)
      (transitionTailAffineSeed seed)
    coordinates := transitionStmtBranchMuxCoordinates tm seed labelOffset
      context test whenTrue whenFalse
    whenTrue := plan.trueRouteValues tm seed labelOffset
    whenFalse := plan.falseRouteValues tm seed labelOffset }

private theorem canonicalMuxInvocationView_frames
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

/-- The three coordinate-indexed rows have exactly the same runtime width. -/
theorem transitionStmtTerminalBranchPlan_muxInvocationView_rowAligned
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (htrueCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height)
    (hfalseCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).RowAligned := by
  have htrue := transitionStmtTerminalBranchPlan_trueRouteValues_eq tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    htrueCapacity
  have hfalse := transitionStmtTerminalBranchPlan_falseRouteValues_eq tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    hfalseCapacity
  unfold TransitionDispatchMuxInvocationView.RowAligned
    TransitionStmtTerminalBranchPlan.muxInvocationView
    transitionStmtBranchMuxCoordinates
  dsimp only
  rw [htrue, hfalse]
  simp [transitionCfgWireValues]

/-- The reconstructed invocation is the literal canonical whole-row mux of
the original branch semantics. -/
theorem transitionStmtTerminalBranchPlan_muxInvocationView_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (htrueCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height)
    (hfalseCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).frames =
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
  have htrue := transitionStmtTerminalBranchPlan_trueRouteValues_eq tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    htrueCapacity
  have hfalse := transitionStmtTerminalBranchPlan_falseRouteValues_eq tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    hfalseCapacity
  unfold TransitionStmtTerminalBranchPlan.muxInvocationView
    transitionStmtBranchMuxCoordinates
  rw [hselector, hmuxStart, htrue, hfalse]
  unfold transitionStmtBranchSemanticSelector
    transitionStmtBranchSemanticMuxStart
    transitionStmtBranchSemanticTrueWires
    transitionStmtBranchSemanticFalseWires transitionCfgWireValues
  exact canonicalMuxInvocationView_frames _ _ _ _ _

/-- The exact delimiter-bearing payload agrees with the canonical branch mux
controller input. -/
theorem transitionStmtTerminalBranchPlan_muxInvocationView_encode
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (htrueCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height)
    (hfalseCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).encode =
      encodeAffineMuxFinFrames
        (transitionStmtBranchSemanticSelector tm seed labelOffset context test)
        (affineMuxFinCanonicalFrames
          (transitionStmtBranchSemanticMuxStart tm seed labelOffset context
            test whenTrue whenFalse)
          (transitionStmtBranchSemanticSelector tm seed labelOffset context
            test)
          (cfgBitCount tm (workHeight tm seed.height))
          (fun coordinate =>
            transitionStmtBranchSemanticTrueWires tm seed labelOffset context
              test whenTrue whenFalse hsupport
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate))
          (fun coordinate =>
            transitionStmtBranchSemanticFalseWires tm seed labelOffset context
              test whenTrue whenFalse hsupport
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate))) := by
  unfold TransitionDispatchMuxInvocationView.encode
  rw [transitionStmtTerminalBranchPlan_muxInvocationView_frames tm seed hwork
    labelOffset context test whenTrue whenFalse hsupport plan hplan
    htrueCapacity hfalseCapacity]
  have hselector := transitionStmtBranchSelectorForm_value tm seed
    labelOffset context test
  rw [show (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).selector =
      transitionStmtBranchSemanticSelector tm seed labelOffset context test by
    simpa [TransitionStmtTerminalBranchPlan.muxInvocationView,
      transitionStmtBranchSemanticSelector] using hselector]

end CLRS.Chapter34.Turing.CookLevin
