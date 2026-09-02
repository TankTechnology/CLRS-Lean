import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursivePlan

/-!
# Total output routes for arbitrary transition statements

Every statement has one of two output shapes.  A branch-free linear spine
ends in `halt` or `goto` and uses its compact normalized route; otherwise the
spine ends in a whole-row branch mux, whose fresh output coordinates already
form the complete route.  Nested branches inside either arm do not change
this dichotomy.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- The final-branch recognizer is defined exactly when the terminal-layout
recognizer is not. -/
theorem transitionStmtFinalBranchMuxOffsetAffine_isSome_iff
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (transitionStmtFinalBranchMuxOffsetAffine tm q).isSome ↔
      ¬ (transitionStmtTerminalLayout tm q).isSome := by
  induction q with
  | halt => simp [transitionStmtFinalBranchMuxOffsetAffine,
      transitionStmtTerminalLayout]
  | goto jump => simp [transitionStmtFinalBranchMuxOffsetAffine,
      transitionStmtTerminalLayout]
  | load update continuation ih =>
      simp [transitionStmtFinalBranchMuxOffsetAffine,
        transitionStmtTerminalLayout, ih]
  | push k emit continuation ih =>
      simp [transitionStmtFinalBranchMuxOffsetAffine,
        transitionStmtTerminalLayout, ih]
  | peek k update continuation ih =>
      simp [transitionStmtFinalBranchMuxOffsetAffine,
        transitionStmtTerminalLayout, ih]
  | pop k update continuation ih =>
      simp [transitionStmtFinalBranchMuxOffsetAffine,
        transitionStmtTerminalLayout, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtFinalBranchMuxOffsetAffine,
        transitionStmtTerminalLayout]

/-- Every supported statement has either a normalized linear result or a
final branch-mux offset. -/
theorem transitionStmtLinearOrBranch
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (∃ result, transitionStmtLinearResult tm context q hsupport =
        some result) ∨
      ∃ offset, transitionStmtFinalBranchMuxOffsetAffine tm q =
        some offset := by
  cases hlinear : transitionStmtLinearResult tm context q hsupport with
  | some result => exact Or.inl ⟨result, rfl⟩
  | none =>
      have hlinearIff :=
        transitionStmtLinearResult_isSome_iff_terminal tm context q hsupport
      rw [hlinear] at hlinearIff
      have hnotTerminal : ¬ (transitionStmtTerminalLayout tm q).isSome := by
        simpa using hlinearIff
      have hbranchSome :
          (transitionStmtFinalBranchMuxOffsetAffine tm q).isSome :=
        (transitionStmtFinalBranchMuxOffsetAffine_isSome_iff tm q).2
          hnotTerminal
      cases hbranch : transitionStmtFinalBranchMuxOffsetAffine tm q with
      | none => simp [hbranch] at hbranchSome
      | some offset => exact Or.inr ⟨offset, rfl⟩

/-- Canonical complete output row of any supported statement. -/
noncomputable def transitionStmtOutputRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List Nat :=
  match transitionStmtLinearResult tm context q hsupport with
  | some result => result.completeRouteValues tm seed labelOffset
  | none =>
      match transitionStmtFinalBranchMuxOffsetAffine tm q with
      | some offset =>
          transitionStmtBranchRouteValues tm seed labelOffset context offset
      | none => []

/-- The total route is the semantic output row.  Capacity is needed only in
the branch-free case, where compact stack routes are materialized; a
branch-ending statement returns fresh mux coordinates directly. -/
theorem transitionStmtOutputRouteValues_eq_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hcapacity : ∀ result,
      transitionStmtLinearResult tm context q hsupport = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤
            workHeight tm seed.height) :
    transitionStmtOutputRouteValues tm seed labelOffset context q hsupport =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          ((seed.start + labelOffset.eval seed.height) +
            context.gateOffset.eval (workHeight tm seed.height))
          (context.rowWires tm seed labelOffset) q hsupport) := by
  cases hlinear : transitionStmtLinearResult tm context q hsupport with
  | some result =>
      rw [transitionStmtOutputRouteValues, hlinear]
      exact transitionStmtLinearResult_completeRouteValues_eq_output tm seed
        hwork labelOffset context q hsupport result hlinear
          (hcapacity result hlinear)
  | none =>
      have hnotLinear :
          ¬ ∃ result, transitionStmtLinearResult tm context q hsupport =
            some result := by
        intro hexists
        rcases hexists with ⟨result, hresult⟩
        rw [hlinear] at hresult
        contradiction
      obtain ⟨offset, hoffset⟩ :=
        (transitionStmtLinearOrBranch tm context q hsupport).resolve_left
          hnotLinear
      rw [transitionStmtOutputRouteValues, hlinear, hoffset]
      exact transitionStmtBranchRouteValues_eq_output tm seed hwork
        labelOffset context q hsupport offset hoffset

end CLRS.Chapter34.Turing.CookLevin
