import CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.DictionaryBridge
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Termination

/-!
# 29.3 Strong duality from finite SIMPLEX

For an initially basic-feasible standard-form program, finite Bland-SIMPLEX
either produces an unbounded primal ray or a terminal dictionary.  In the
terminal case its basic assignment and shadow prices are primal/dual optimal
and have the same objective value.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Strong duality from any basic-feasible dictionary equivalent to the
program's initial dictionary. -/
theorem strongDuality_or_unbounded_of_equivalent_isBasicFeasible
    (P : StandardLP m n) (D : Dictionary m n)
    (hEq₀ : P.initialDictionary.Equivalent D)
    (hD : D.IsBasicFeasible) :
    P.IsUnbounded ∨
      ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
        P.objective x = P.dualObjective y := by
  let fuel := Dictionary.basisCount m n
  cases hrun : D.simplexRun fuel with
  | optimal terminal hc =>
      have hEq : P.initialDictionary.Equivalent terminal :=
        hEq₀.trans (by
          simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
            D.simplexRun_equivalent fuel)
      have hterminal : terminal.IsBasicFeasible := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D.simplexRun_isBasicFeasible fuel hD
      have hdictOptimal :
          P.initialDictionary.IsOptimalAssignment terminal.basicAssignment :=
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
      have hterminalSatD₀ :
          P.initialDictionary.Satisfies terminal.basicAssignment :=
        (hEq.1 terminal.basicAssignment).2
          terminal.basicAssignment_satisfies
      have hprimalValue : P.objective x = terminal.v := by
        calc
          P.objective x =
              P.initialDictionary.objectiveRhs terminal.basicAssignment :=
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
      have hEq : P.initialDictionary.Equivalent terminal :=
        hEq₀.trans (by
          simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
            D.simplexRun_equivalent fuel)
      have hterminal : terminal.IsBasicFeasible := by
        simpa [hrun, Dictionary.SimplexRunResult.terminalDictionary] using
          D.simplexRun_isBasicFeasible fuel hD
      have hunbounded : P.initialDictionary.IsUnbounded :=
        hEq.isUnbounded
          (terminal.unbounded_of_entering_column hterminal entering he.1 ha)
      exact Or.inl
        (Dictionary.initialDictionary_unbounded_to_standardLP P hunbounded)
  | exhausted terminal =>
      exact False.elim (D.simplexRun_basisCount_not_exhausted hD (by
        simp [fuel, hrun, Dictionary.SimplexRunResult.IsExhausted]))

/-- Strong duality, with the alternative unbounded outcome made explicit,
for programs whose initial slack dictionary is basic feasible. -/
theorem strongDuality_or_unbounded_of_initialDictionary_isBasicFeasible
    (P : StandardLP m n) (hP : P.initialDictionary.IsBasicFeasible) :
    P.IsUnbounded ∨
      ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
        P.objective x = P.dualObjective y :=
  P.strongDuality_or_unbounded_of_equivalent_isBasicFeasible
    P.initialDictionary (Dictionary.Equivalent.refl _) hP

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
