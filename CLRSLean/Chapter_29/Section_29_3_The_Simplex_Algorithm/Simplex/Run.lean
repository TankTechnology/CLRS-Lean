import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Equivalence

/-!
# 29.3 Fuelled SIMPLEX runs

The internal runner makes every textbook iteration executable while keeping
fuel exhaustion explicit.  Correctness of optimal and unbounded results is
proved independently of the later Bland finite-termination bound.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Outcomes of the internal fuelled SIMPLEX runner. -/
inductive SimplexRunResult (m n : ℕ) where
  | optimal (terminal : Dictionary m n)
      (reducedCostsNonpositive : ∀ j, terminal.c j ≤ 0)
  | unbounded (terminal : Dictionary m n) (entering : Fin n)
      (enteringIsBland : terminal.IsBlandEntering entering)
      (columnNonpositive : ∀ i, terminal.a i entering ≤ 0)
  | exhausted (terminal : Dictionary m n)

namespace SimplexRunResult

/-- The final dictionary stored by any internal run outcome. -/
def terminalDictionary : SimplexRunResult m n → Dictionary m n
  | .optimal D _ => D
  | .unbounded D _ _ _ => D
  | .exhausted D => D

/-- Whether an internal run ended at the optimal terminal constructor. -/
def IsOptimal : SimplexRunResult m n → Prop
  | .optimal _ _ => True
  | .unbounded _ _ _ _ => False
  | .exhausted _ => False

/-- Whether an internal run ended at the unbounded terminal constructor. -/
def IsUnbounded : SimplexRunResult m n → Prop
  | .optimal _ _ => False
  | .unbounded _ _ _ _ => True
  | .exhausted _ => False

/-- Whether the internal fuel budget was exhausted. -/
def IsExhausted : SimplexRunResult m n → Prop
  | .optimal _ _ => False
  | .unbounded _ _ _ _ => False
  | .exhausted _ => True

end SimplexRunResult

/-- Run Bland-rule SIMPLEX for at most {lit}`fuel` pivots. -/
noncomputable def simplexRun : ℕ → Dictionary m n → SimplexRunResult m n
  | 0, D => .exhausted D
  | fuel + 1, D =>
      match D.simplexStep with
      | .optimal hc => .optimal D hc
      | .unbounded e he ha => .unbounded D e he ha
      | .pivot e l _ hl =>
          simplexRun fuel
            (D.pivot l e hl.1.pivotCoefficient_pos.ne')

/-- Every terminal dictionary produced by the internal runner represents the
same problem as its input. -/
theorem simplexRun_equivalent (fuel : ℕ) (D : Dictionary m n) :
    D.Equivalent (D.simplexRun fuel).terminalDictionary := by
  induction fuel generalizing D with
  | zero =>
      exact Equivalent.refl D
  | succ fuel ih =>
      cases hstep : D.simplexStep with
      | optimal _ =>
          simpa [simplexRun, hstep,
            SimplexRunResult.terminalDictionary] using Equivalent.refl D
      | unbounded _ _ _ =>
          simpa [simplexRun, hstep,
            SimplexRunResult.terminalDictionary] using Equivalent.refl D
      | pivot e l _ hl =>
          let next := D.pivot l e hl.1.pivotCoefficient_pos.ne'
          have hpivot : D.Equivalent next :=
            D.pivot_equivalent l e hl.1.pivotCoefficient_pos.ne'
          have hrest := ih next
          simpa [simplexRun, hstep, next] using hpivot.trans hrest

/-- Basic feasibility is preserved throughout every internal run. -/
theorem simplexRun_isBasicFeasible (fuel : ℕ) (D : Dictionary m n)
    (hD : D.IsBasicFeasible) :
    (D.simplexRun fuel).terminalDictionary.IsBasicFeasible := by
  induction fuel generalizing D with
  | zero => exact hD
  | succ fuel ih =>
      cases hstep : D.simplexStep with
      | optimal _ =>
          simpa [simplexRun, hstep,
            SimplexRunResult.terminalDictionary] using hD
      | unbounded _ _ _ =>
          simpa [simplexRun, hstep,
            SimplexRunResult.terminalDictionary] using hD
      | pivot e l _ hl =>
          let next := D.pivot l e hl.1.pivotCoefficient_pos.ne'
          have hnext : next.IsBasicFeasible :=
            D.pivot_isBasicFeasible e l hD hl.1
          simpa [simplexRun, hstep, next] using ih next hnext

/-- The basic objective constant is nondecreasing throughout a feasible run. -/
theorem simplexRun_v_mono (fuel : ℕ) (D : Dictionary m n)
    (hD : D.IsBasicFeasible) :
    D.v ≤ (D.simplexRun fuel).terminalDictionary.v := by
  induction fuel generalizing D with
  | zero => exact le_rfl
  | succ fuel ih =>
      cases hstep : D.simplexStep with
      | optimal _ =>
          simp [simplexRun, hstep,
            SimplexRunResult.terminalDictionary]
      | unbounded _ _ _ =>
          simp [simplexRun, hstep,
            SimplexRunResult.terminalDictionary]
      | pivot e l he hl =>
          let next := D.pivot l e hl.1.pivotCoefficient_pos.ne'
          have hnext : next.IsBasicFeasible :=
            D.pivot_isBasicFeasible e l hD hl.1
          have hfirst : D.v ≤ next.v := D.pivot_v_mono hD he.1 hl.1
          have hrest := ih next hnext
          simpa [simplexRun, hstep, next] using hfirst.trans hrest

namespace SimplexRunResult

/-- A feasible optimal run outcome carries an optimal terminal basic
assignment. -/
theorem optimal_correct (result : SimplexRunResult m n)
    (hfeasible : result.terminalDictionary.IsBasicFeasible)
    (hresult : result.IsOptimal) :
    result.terminalDictionary.IsOptimalAssignment
      result.terminalDictionary.basicAssignment := by
  cases result with
  | optimal D hc => exact D.basicAssignment_optimal_of_reducedCosts_nonpos hfeasible hc
  | unbounded _ _ _ _ => exact False.elim hresult
  | exhausted _ => exact False.elim hresult

/-- A feasible unbounded run outcome carries a valid unboundedness
certificate. -/
theorem unbounded_correct (result : SimplexRunResult m n)
    (hfeasible : result.terminalDictionary.IsBasicFeasible)
    (hresult : result.IsUnbounded) : result.terminalDictionary.IsUnbounded := by
  cases result with
  | optimal _ _ => exact False.elim hresult
  | unbounded D e he ha =>
      exact D.unbounded_of_entering_column hfeasible e he.1 ha
  | exhausted _ => exact False.elim hresult

end SimplexRunResult

/-- Any optimal internal-run result is optimal for the input dictionary. -/
theorem simplexRun_optimal_correct (fuel : ℕ) (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hresult : (D.simplexRun fuel).IsOptimal) :
    D.IsOptimalAssignment
      (D.simplexRun fuel).terminalDictionary.basicAssignment :=
  (D.simplexRun_equivalent fuel).isOptimalAssignment
    ((D.simplexRun fuel).optimal_correct
      (D.simplexRun_isBasicFeasible fuel hD) hresult)

/-- Any unbounded internal-run result proves the input dictionary unbounded. -/
theorem simplexRun_unbounded_correct (fuel : ℕ) (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hresult : (D.simplexRun fuel).IsUnbounded) :
    D.IsUnbounded :=
  (D.simplexRun_equivalent fuel).isUnbounded
    ((D.simplexRun fuel).unbounded_correct
      (D.simplexRun_isBasicFeasible fuel hD) hresult)

end Dictionary
end Chapter29
end CLRS
