import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalRow
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmBranchAffine

/-!
# Unified normal form for every transition true arm

Every fixed program label ends either in a whole-row branch mux or in the
terminal-row normal form.  This module packages those two cases in original
label order and proves that the resulting rows are exactly the complete
semantic dispatch `whenTrue` family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Choose the terminal row layout justified by the complementary
final-branch classification. -/
noncomputable def transitionStmtTerminalRowLayoutOfBranchNone
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hbranch : transitionStmtFinalBranchMuxOffsetAffine tm q = none) :
    TransitionStmtTerminalRowLayout tm := by
  have hterminal : (transitionStmtTerminalLayout tm q).isSome :=
    (transitionStmtTerminalLayout_isSome_iff_branch_none tm q).2 hbranch
  have hrow : (transitionStmtTerminalRowLayout tm q hsupport).isSome :=
    (transitionStmtTerminalRowLayout_isSome_iff_terminal tm q hsupport).2
      hterminal
  exact Classical.choose (Option.isSome_iff_exists.mp hrow)

theorem transitionStmtTerminalRowLayoutOfBranchNone_eq
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hbranch : transitionStmtFinalBranchMuxOffsetAffine tm q = none) :
    transitionStmtTerminalRowLayout tm q hsupport =
      some (transitionStmtTerminalRowLayoutOfBranchNone tm q hsupport
        hbranch) := by
  unfold transitionStmtTerminalRowLayoutOfBranchNone
  exact Classical.choose_spec (Option.isSome_iff_exists.mp
    ((transitionStmtTerminalRowLayout_isSome_iff_terminal tm q hsupport).2
      ((transitionStmtTerminalLayout_isSome_iff_branch_none tm q).2
        hbranch)))

/-- Proof-carrying normal form for one label's complete true-input row. -/
inductive TransitionDispatchTrueArmNormalizedLayout
    (tm : _root_.Turing.FinTM2)
  | branch (labelOffset : TransitionAffineNat) (label : tm.Λ)
      (branchOffset : TransitionAffineNat)
      (hbranch : transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) =
        some branchOffset)
  | terminal (labelOffset : TransitionAffineNat) (label : tm.Λ)
      (rowLayout : TransitionStmtTerminalRowLayout tm)
      (hlayout : transitionStmtTerminalRowLayout tm (tm.m label)
        (stmtPushSet_program_subset tm label) = some rowLayout)

/-- Unified layouts in original program-label order. -/
noncomputable def transitionDispatchTrueArmNormalizedLayoutsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ →
      List (TransitionDispatchTrueArmNormalizedLayout tm)
  | _, [] => []
  | labelOffset, label :: labels =>
      let nextOffset :=
        (labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
          (transitionDispatchMuxGateAffine tm)
      let rest := transitionDispatchTrueArmNormalizedLayoutsForLabels tm
        nextOffset labels
      match hbranch :
          transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) with
      | some branchOffset =>
          .branch labelOffset label branchOffset hbranch :: rest
      | none =>
          let rowLayout := transitionStmtTerminalRowLayoutOfBranchNone tm
            (tm.m label) (stmtPushSet_program_subset tm label) hbranch
          let hlayout := transitionStmtTerminalRowLayoutOfBranchNone_eq tm
            (tm.m label) (stmtPushSet_program_subset tm label) hbranch
          .terminal labelOffset label rowLayout hlayout :: rest

/-- Complete normalized layout family. -/
noncomputable def transitionDispatchTrueArmNormalizedLayouts
    (tm : _root_.Turing.FinTM2) :
    List (TransitionDispatchTrueArmNormalizedLayout tm) :=
  transitionDispatchTrueArmNormalizedLayoutsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Evaluate one unified layout to a complete row. -/
def TransitionDispatchTrueArmNormalizedLayout.wires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm →
      CfgWires tm (workHeight tm seed.height)
  | .branch labelOffset _ branchOffset _ =>
      arithmeticMuxCfgWires tm (workHeight tm seed.height)
        (seed.start + labelOffset.eval seed.height +
          branchOffset.eval (workHeight tm seed.height))
  | .terminal labelOffset _ rowLayout _ =>
      rowLayout.wires tm (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- Flatten one normalized row in canonical configuration-coordinate order. -/
def TransitionDispatchTrueArmNormalizedLayout.values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) : List Nat :=
  transitionCfgWireValues tm (workHeight tm seed.height)
    (layout.wires tm seed)

/-- Each unified entry evaluates to its original semantic statement row. -/
theorem TransitionDispatchTrueArmNormalizedLayout.values_eq_semantic
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.values tm seed =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          (seed.start + match layout with
            | .branch labelOffset _ _ _ => labelOffset.eval seed.height
            | .terminal labelOffset _ _ _ => labelOffset.eval seed.height)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          (match layout with
            | .branch _ label _ _ => tm.m label
            | .terminal _ label _ _ => tm.m label)
          (match layout with
            | .branch _ label _ _ => stmtPushSet_program_subset tm label
            | .terminal _ label _ _ => stmtPushSet_program_subset tm label)) := by
  cases layout with
  | branch labelOffset label branchOffset hbranch =>
      unfold TransitionDispatchTrueArmNormalizedLayout.values
        TransitionDispatchTrueArmNormalizedLayout.wires
      rw [transitionStmtOutputWires_eq_finalBranchMux tm
        (workHeight tm seed.height) hwork seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        (tm.m label) (stmtPushSet_program_subset tm label)
        branchOffset hbranch]
  | terminal labelOffset label rowLayout hlayout =>
      unfold TransitionDispatchTrueArmNormalizedLayout.values
        TransitionDispatchTrueArmNormalizedLayout.wires
      rw [transitionStmtOutputWires_terminal_row tm
        (workHeight tm seed.height) hwork seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        (tm.m label) (stmtPushSet_program_subset tm label)
        rowLayout hlayout]

/-- Normalized rows for a fixed label suffix. -/
def transitionDispatchTrueArmNormalizedRowsForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) (labels : List tm.Λ) :
    List (List Nat) :=
  (transitionDispatchTrueArmNormalizedLayoutsForLabels tm labelOffset labels).map
    (TransitionDispatchTrueArmNormalizedLayout.values tm seed)

/-- Complete normalized true-arm row family. -/
def transitionDispatchTrueArmNormalizedRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).map
    (TransitionDispatchTrueArmNormalizedLayout.values tm seed)

theorem transitionDispatchTrueArmNormalizedRowsForLabels_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ∀ (labelOffset : TransitionAffineNat) (labels : List tm.Λ),
      transitionDispatchTrueArmNormalizedRowsForLabels tm seed
          labelOffset labels =
        transitionDispatchTrueArmRowsForLabels tm seed.height seed.start
          (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          (seed.start + labelOffset.eval seed.height) labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      unfold transitionDispatchTrueArmNormalizedRowsForLabels
      simp only [transitionDispatchTrueArmNormalizedLayoutsForLabels,
        transitionDispatchTrueArmRowsForLabels]
      split <;> rename_i hbranch
      · simp only [List.map_cons]
        rw [TransitionDispatchTrueArmNormalizedLayout.values_eq_semantic
          tm seed hwork]
        have htail := ih
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm))
        simpa [transitionDispatchTrueArmNormalizedRowsForLabels,
          TransitionAffineNat.eval_add,
          transitionDispatchStmtGateAffine_eval tm label seed.height hwork,
          transitionDispatchMuxGateAffine_eval tm seed.height,
          Nat.add_assoc] using htail
      · simp only [List.map_cons]
        rw [TransitionDispatchTrueArmNormalizedLayout.values_eq_semantic
          tm seed hwork]
        have htail := ih
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm))
        simpa [transitionDispatchTrueArmNormalizedRowsForLabels,
          TransitionAffineNat.eval_add,
          transitionDispatchStmtGateAffine_eval tm label seed.height hwork,
          transitionDispatchMuxGateAffine_eval tm seed.height,
          Nat.add_assoc] using htail

/-- The unified normalized family is exactly the complete seed-only true-arm
family, without filtering out either terminal or branch-ending labels. -/
theorem transitionDispatchTrueArmNormalizedRows_eq_seed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchTrueArmNormalizedRows tm seed =
      transitionDispatchTrueArmRowsFromSeed tm seed := by
  unfold transitionDispatchTrueArmNormalizedRows
    transitionDispatchTrueArmNormalizedLayouts
    transitionDispatchTrueArmRowsFromSeed
  simpa [transitionDispatchTrueArmNormalizedRowsForLabels,
    TransitionAffineNat.eval, TransitionAffineNat.const] using
    transitionDispatchTrueArmNormalizedRowsForLabels_eq tm seed hwork
      (TransitionAffineNat.const 2) (programLabels tm)

end CLRS.Chapter34.Turing.CookLevin
