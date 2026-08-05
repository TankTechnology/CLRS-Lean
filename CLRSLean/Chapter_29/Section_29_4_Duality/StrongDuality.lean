import CLRSLean.Chapter_29.Section_29_4_Duality.DictionaryBridge
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Termination

/-!
# 29.4 Strong duality from finite SIMPLEX

For an initially basic-feasible standard-form program, finite Bland-SIMPLEX
either produces an unbounded primal ray or a terminal dictionary.  In the
terminal case its basic assignment and shadow prices are primal/dual optimal
and have the same objective value.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Strong duality, with the alternative unbounded outcome made explicit,
for programs whose initial slack dictionary is basic feasible. -/
theorem strongDuality_or_unbounded_of_initialDictionary_isBasicFeasible
    (P : StandardLP m n) (hP : P.initialDictionary.IsBasicFeasible) :
    P.IsUnbounded ∨
      ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
        P.objective x = P.dualObjective y := by
  let D₀ := P.initialDictionary
  let fuel := Dictionary.basisCount m n
  cases hrun : D₀.simplexRun fuel with
  | optimal terminal hc =>
      have hEq : D₀.Equivalent terminal := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D₀.simplexRun_equivalent fuel
      have hterminal : terminal.IsBasicFeasible := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D₀.simplexRun_isBasicFeasible fuel hP
      have hdictOptimal :
          D₀.IsOptimalAssignment terminal.basicAssignment :=
        hEq.isOptimalAssignment
          (terminal.basicAssignment_optimal_of_reducedCosts_nonpos
            hterminal hc)
      let x := Dictionary.assignmentOriginal terminal.basicAssignment
      let y := terminal.dualCertificate
      have hx : P.IsOptimal x := by
        exact Dictionary.initialDictionary_optimal_to_standardLP P
          hdictOptimal
      have hyfeasible : P.IsDualFeasible y := by
        exact terminal.dualCertificate_isDualFeasible P hEq hc
      have hterminalSatD₀ : D₀.Satisfies terminal.basicAssignment :=
        (hEq.1 terminal.basicAssignment).2
          terminal.basicAssignment_satisfies
      have hprimalValue : P.objective x = terminal.v := by
        calc
          P.objective x = D₀.objectiveRhs terminal.basicAssignment :=
            (Dictionary.initialDictionary_objectiveRhs_eq_objective_original
              P terminal.basicAssignment).symm
          _ = terminal.objectiveRhs terminal.basicAssignment :=
            hEq.2 terminal.basicAssignment hterminalSatD₀
          _ = terminal.v := terminal.objectiveRhs_basicAssignment
      have hdualValue : P.dualObjective y = terminal.v :=
        terminal.dualCertificate_objective_eq_v P hEq
      have hvalue : P.objective x = P.dualObjective y :=
        hprimalValue.trans hdualValue.symm
      have hcs : P.ComplementarySlackness x y :=
        (P.complementarySlackness_iff_objective_eq hx.1 hyfeasible).2 hvalue
      have hy : P.IsDualOptimal y :=
        P.dualOptimal_of_complementarySlackness hx.1 hyfeasible hcs
      exact Or.inr ⟨x, y, hx, hy, hvalue⟩
  | unbounded terminal entering he ha =>
      have hEq : D₀.Equivalent terminal := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D₀.simplexRun_equivalent fuel
      have hterminal : terminal.IsBasicFeasible := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D₀.simplexRun_isBasicFeasible fuel hP
      have hunbounded : D₀.IsUnbounded :=
        hEq.isUnbounded
          (terminal.unbounded_of_entering_column hterminal entering he.1 ha)
      exact Or.inl
        (Dictionary.initialDictionary_unbounded_to_standardLP P hunbounded)
  | exhausted terminal =>
      exact False.elim (D₀.simplexRun_basisCount_not_exhausted hP (by
        simpa [fuel, hrun, Dictionary.SimplexRunResult.IsExhausted]))

/-- If the primal is not unbounded, finite SIMPLEX yields primal and dual
optima with equal objective values. -/
theorem strongDuality_of_initialDictionary_isBasicFeasible
    (P : StandardLP m n) (hP : P.initialDictionary.IsBasicFeasible)
    (hbounded : ¬P.IsUnbounded) :
    ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
      P.objective x = P.dualObjective y := by
  rcases P.strongDuality_or_unbounded_of_initialDictionary_isBasicFeasible hP
      with hunbounded | hopt
  · exact False.elim (hbounded hunbounded)
  · exact hopt

end StandardLP
end Chapter29
end CLRS
