import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextStep

/-!
# Complete pop blocks from affine statement contexts

A recursive `pop` contributes two controller phases: the height merge and the
state/head pair lookup.  Both phases are generated together here so the later
statement recursion never leaves a half-compiled primitive.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic two-phase pop block at the current continuation context. -/
noncomputable def transitionStmtContextPopPhaseForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    List TransitionAffineStmtPhaseForm :=
  let state := context.stateForm tm labelOffset
  let head := context.stackCellFrontForm tm labelOffset k
  let pairStart := transitionAbsoluteStartForm
    ((context.absoluteOffset tm labelOffset).add
      (TransitionAffineNat.const 1))
  [ .pop
      [{ left := context.stackHeightFrontForm tm labelOffset k 0
         right := context.stackHeightFrontForm tm labelOffset k 1 }],
    .oneHotPairMap
      (transitionOneHotPairAndForms state head)
      (transitionAffineOneHotPairCanonicalGroups pairStart
        (stmtHeadStateTable tm k update)) ]

/-- Ordinary builder-free pop block starting from the row denoted by the
context. -/
def transitionStmtContextPopPhaseBlock
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    List AffineStmtPhase :=
  let start := (seed.start + labelOffset.eval seed.height) +
    context.gateOffset.eval (workHeight tm seed.height)
  let source := context.rowWires tm seed labelOffset
  let popped := arithmeticPopCfgWires tm (workHeight tm seed.height) k
    seed.start (seed.start + 1) start source
  let head := arithmeticPopHeadWires tm k seed.start (seed.start + 1)
    (workHeight tm seed.height) (source.stack k)
  [ .pop (affinePopFrames source k),
    .oneHotPairMap
      (affineOneHotPairMapAndFrames popped.state head)
      (affineOneHotPairMapOrGroups (start + 1) popped.state head
        (stmtHeadStateTable tm k update)) ]

/-- Affine evaluation recovers the literal two-phase pop block. -/
theorem transitionStmtContextPopPhaseForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ)
    (hpadding :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    (transitionStmtContextPopPhaseForms tm labelOffset context k update).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtContextPopPhaseBlock tm seed labelOffset context k
        update := by
  let source := context.rowWires tm seed labelOffset
  let start := (seed.start + labelOffset.eval seed.height) +
    context.gateOffset.eval (workHeight tm seed.height)
  let popped := arithmeticPopCfgWires tm (workHeight tm seed.height) k
    seed.start (seed.start + 1) start source
  let head := arithmeticPopHeadWires tm k seed.start (seed.start + 1)
    (workHeight tm seed.height) (source.stack k)
  have hwork : 0 < workHeight tm seed.height := by
    unfold workHeight
    omega
  have hframes := context.stackHeightFrontFrames_value tm seed labelOffset k
    hpadding
  have hstate :
      (fun target => affineUnaryTripleFormValue
        (context.stateForm tm labelOffset target)
        (transitionTailAffineSeed seed)) = popped.state := by
    funext target
    rw [context.stateForm_eq_wires tm seed labelOffset]
    rfl
  have hhead :
      (fun code => affineUnaryTripleFormValue
        (context.stackCellFrontForm tm labelOffset k code)
        (transitionTailAffineSeed seed)) = head := by
    funext code
    rw [context.stackCellFrontForm_value tm seed labelOffset k code hpadding]
    rw [arithmeticPeekCfgWires_eq_cell_zero tm
      (workHeight tm seed.height) hwork]
    change ((context.rowWires tm seed labelOffset).stack k).cell
        ⟨0, hwork⟩ code =
      arithmeticPopHeadWires tm k seed.start (seed.start + 1)
        (workHeight tm seed.height)
        ((context.rowWires tm seed labelOffset).stack k) code
    rw [arithmeticPopHeadWires_eq_cell_zero tm k seed.start
      (seed.start + 1) (workHeight tm seed.height) hwork]
  have hpairStart :
      affineUnaryTripleFormValue
          (transitionAbsoluteStartForm
            ((context.absoluteOffset tm labelOffset).add
              (TransitionAffineNat.const 1)))
          (transitionTailAffineSeed seed) = start + 1 := by
    rw [transitionAbsoluteStartForm_value]
    simp [TransitionStmtAffineContext.absoluteOffset, workHeight, start]
    omega
  simp only [transitionStmtContextPopPhaseForms, List.map_cons, List.map_nil,
    TransitionAffineStmtPhaseForm.eval,
    transitionStmtContextPopPhaseBlock]
  rw [hframes, transitionAffineOneHotPairAndFrames_eval,
    transitionAffineOneHotPairOrGroups_eval, hpairStart, hstate, hhead]

end CLRS.Chapter34.Turing.CookLevin
