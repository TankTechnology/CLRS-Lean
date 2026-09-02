import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementFinalBranch

/-!
# Terminal layout of a transition statement

The linear spine of a bundled TM2 statement ends in exactly one of `halt`,
`goto`, or `branch`.  The branch case already has a closed output-row layout.
This module classifies the complementary `halt`/`goto` cases and records the
exact affine gate offset of their terminal instruction.  No runtime input is
inspected: the classification is fixed by the verifier program.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- The nonbranching instruction at the end of a statement's linear spine. -/
inductive TransitionStmtTerminal (tm : _root_.Turing.FinTM2)
  | halt
  | goto (jump : tm.σ → tm.Λ)

/-- A fixed terminal instruction together with the affine number of gates
emitted by the updates that precede it. -/
structure TransitionStmtTerminalLayout (tm : _root_.Turing.FinTM2) where
  offset : TransitionAffineNat
  terminal : TransitionStmtTerminal tm

/-- Gate cost of the terminal instruction itself. -/
def TransitionStmtTerminal.gateAffine (tm : _root_.Turing.FinTM2) :
    TransitionStmtTerminal tm → TransitionAffineNat
  | .halt => TransitionAffineNat.const 0
  | .goto _ =>
      TransitionAffineNat.const (stateCount tm + (labelCount tm + 1))

private theorem transitionAffineNat_add_assoc
    (first second third : TransitionAffineNat) :
    (first.add second).add third = first.add (second.add third) := by
  cases first
  cases second
  cases third
  simp [TransitionAffineNat.add, Nat.add_assoc]

/-- Static classification of a statement whose linear spine ends in `halt`
or `goto`.  `none` is reserved exactly for spines ending in `branch`. -/
noncomputable def transitionStmtTerminalLayout
    (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Option (TransitionStmtTerminalLayout tm)
  | halt => some
      { offset := TransitionAffineNat.const 0
        terminal := .halt }
  | goto jump => some
      { offset := TransitionAffineNat.const 0
        terminal := .goto jump }
  | load _ continuation =>
      (transitionStmtTerminalLayout tm continuation).map fun layout =>
        { layout with
          offset := (TransitionAffineNat.const
            (stateCount tm + stateCount tm)).add layout.offset }
  | push k _ continuation =>
      (transitionStmtTerminalLayout tm continuation).map fun layout =>
        { layout with
          offset := (TransitionAffineNat.const
            (stateCount tm + (reachableAlphabet tm k).card)).add
              layout.offset }
  | peek k _ continuation =>
      (transitionStmtTerminalLayout tm continuation).map fun layout =>
        { layout with
          offset := (TransitionAffineNat.const
            (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
              stateCount tm)).add layout.offset }
  | pop k _ continuation =>
      (transitionStmtTerminalLayout tm continuation).map fun layout =>
        { layout with
          offset := (TransitionAffineNat.const
            (1 + 2 * stateCount tm *
              ((reachableAlphabet tm k).card + 1) + stateCount tm)).add
              layout.offset }
  | branch _ _ _ => none

/-- The terminal classifier is defined exactly on the complement of the
final-branch classifier. -/
theorem transitionStmtTerminalLayout_isSome_iff_branch_none
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (transitionStmtTerminalLayout tm q).isSome ↔
      transitionStmtFinalBranchMuxOffsetAffine tm q = none := by
  induction q with
  | halt => simp [transitionStmtTerminalLayout,
      transitionStmtFinalBranchMuxOffsetAffine]
  | goto jump => simp [transitionStmtTerminalLayout,
      transitionStmtFinalBranchMuxOffsetAffine]
  | load update continuation ih =>
      simp [transitionStmtTerminalLayout,
        transitionStmtFinalBranchMuxOffsetAffine, ih]
  | push k emit continuation ih =>
      simp [transitionStmtTerminalLayout,
        transitionStmtFinalBranchMuxOffsetAffine, ih]
  | peek k update continuation ih =>
      simp [transitionStmtTerminalLayout,
        transitionStmtFinalBranchMuxOffsetAffine, ih]
  | pop k update continuation ih =>
      simp [transitionStmtTerminalLayout,
        transitionStmtFinalBranchMuxOffsetAffine, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalLayout,
        transitionStmtFinalBranchMuxOffsetAffine]

/-- The affine cost of a terminal-ending statement factors into its linear
prefix offset followed by the fixed cost of its terminal instruction. -/
theorem transitionStmtTerminalGateAffine
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (layout : TransitionStmtTerminalLayout tm)
    (hlayout : transitionStmtTerminalLayout tm q = some layout) :
    compileStmtGateAffine tm q =
      layout.offset.add (layout.terminal.gateAffine tm) := by
  induction q generalizing layout with
  | halt =>
      simp [transitionStmtTerminalLayout] at hlayout
      subst layout
      rfl
  | goto jump =>
      simp [transitionStmtTerminalLayout] at hlayout
      subst layout
      simp [compileStmtGateAffine, TransitionStmtTerminal.gateAffine,
        TransitionAffineNat.add, TransitionAffineNat.const]
  | load update continuation ih =>
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          rw [compileStmtGateAffine, ih continuationLayout hcontinuation]
          exact (transitionAffineNat_add_assoc _ _ _).symm
  | push k emit continuation ih =>
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          rw [compileStmtGateAffine, ih continuationLayout hcontinuation]
          exact (transitionAffineNat_add_assoc _ _ _).symm
  | peek k update continuation ih =>
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          rw [compileStmtGateAffine, ih continuationLayout hcontinuation]
          exact (transitionAffineNat_add_assoc _ _ _).symm
  | pop k update continuation ih =>
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          rw [compileStmtGateAffine, ih continuationLayout hcontinuation]
          exact (transitionAffineNat_add_assoc _ _ _).symm
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalLayout] at hlayout

end CLRS.Chapter34.Turing.CookLevin
