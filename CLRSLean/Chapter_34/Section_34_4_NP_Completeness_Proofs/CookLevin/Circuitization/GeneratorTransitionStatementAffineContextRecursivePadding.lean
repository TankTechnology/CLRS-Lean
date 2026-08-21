import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveMux
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalCapacity

/-!
# Capacity invariant for recursively nested statements

The earlier padding predicates stopped either at a terminal instruction or at
one branch with terminal arms.  This predicate follows every continuation and
both arms of every branch, retaining the public stack-front capacity required
to evaluate affine `peek` and `pop` operands at every recursive context.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Public stack-front capacity at every node of an arbitrary statement. -/
noncomputable def transitionStmtRecursiveContextPadding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) → Prop
  | context, halt, _ => ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height
  | context, goto _, _ => ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (∀ k, 2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtRecursiveContextPadding tm seed
        (context.afterLoad tm update) continuation hcontinuation
  | context, push k emit continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtRecursiveContextPadding tm seed
        (context.afterPush tm k table) continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtRecursiveContextPadding tm seed
        (context.afterPeek tm k update) continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtRecursiveContextPadding tm seed
        (context.afterPop tm k update) continuation hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      (∀ k, 2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtRecursiveContextPadding tm seed
        (transitionStmtBranchTrueContext tm context test) whenTrue
        (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
          hsupport) ∧
      transitionStmtRecursiveContextPadding tm seed
        (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
        (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
          hsupport)

/-- On a branch-free statement, recursive padding specializes to the existing
linear-padding interface. -/
theorem transitionStmtRecursiveContextPadding_to_linear
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      (transitionStmtTerminalLayout tm q).isSome →
      transitionStmtRecursiveContextPadding tm seed context q hsupport →
      transitionStmtLinearContextPadding tm seed context q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hterminal hpadding
      exact hpadding
  | goto jump =>
      intro hsupport hterminal hpadding
      exact hpadding
  | load update continuation ih =>
      intro hsupport hterminal hpadding
      rcases hpadding with ⟨hcurrent, htail⟩
      refine ⟨hcurrent, ?_⟩
      apply ih (context.afterLoad tm update)
      · simpa [transitionStmtTerminalLayout] using hterminal
      · exact htail
  | push k emit continuation ih =>
      intro hsupport hterminal hpadding
      rcases hpadding with ⟨hcurrent, htail⟩
      refine ⟨hcurrent, ?_⟩
      apply ih
      · simpa [transitionStmtTerminalLayout] using hterminal
      · exact htail
  | peek k update continuation ih =>
      intro hsupport hterminal hpadding
      rcases hpadding with ⟨hcurrent, htail⟩
      refine ⟨hcurrent, ?_⟩
      apply ih (context.afterPeek tm k update)
      · simpa [transitionStmtTerminalLayout] using hterminal
      · exact htail
  | pop k update continuation ih =>
      intro hsupport hterminal hpadding
      rcases hpadding with ⟨hcurrent, htail⟩
      refine ⟨hcurrent, ?_⟩
      apply ih (context.afterPop tm k update)
      · simpa [transitionStmtTerminalLayout] using hterminal
      · exact htail
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hterminal hpadding
      simp [transitionStmtTerminalLayout] at hterminal

/-- Recursive padding supplies the workspace capacity required by the total
output-route theorem whenever the statement has a linear result. -/
theorem transitionStmtRecursiveContextPadding_linearResult_capacity
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hpadding : transitionStmtRecursiveContextPadding tm seed context q
      hsupport) :
    ∀ result,
      transitionStmtLinearResult tm context q hsupport = some result →
      ∀ k,
        2 * (transitionStmtStackActionsFor tm k
          result.context.stackActions).length + 1 ≤
          workHeight tm seed.height := by
  intro result hresult
  have hresultIff := transitionStmtLinearResult_isSome_iff_terminal tm
    context q hsupport
  rw [hresult] at hresultIff
  have hterminal : (transitionStmtTerminalLayout tm q).isSome := by
    simpa using hresultIff
  have hlinear := transitionStmtRecursiveContextPadding_to_linear tm seed
    context q hsupport hterminal hpadding
  have hcapacity := transitionStmtLinearResult_capacity_of_padding tm seed
    context q hsupport hlinear result hresult
  intro k
  exact (hcapacity k).trans (by simp [workHeight])

end CLRS.Chapter34.Turing.CookLevin
