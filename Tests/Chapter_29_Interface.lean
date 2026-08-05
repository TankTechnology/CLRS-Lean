import CLRSLean.Chapter_29

/-!
# Chapter 29 Interface Test

Verifies that the represented Chapter 29 standard/slack and weak-duality
declarations are available through the chapter guide.
-/

namespace CLRS
namespace Chapter29

#check IsNonnegative
#check StandardLP
#check StandardLP.IsFeasible
#check StandardLP.objective
#check StandardLP.slack
#check StandardLP.IsSlackExtension
#check StandardLP.slack_nonnegative_of_feasible
#check StandardLP.slack_equation
#check StandardLP.slackExtension_of_feasible
#check StandardLP.feasible_of_slackExtension
#check StandardLP.isFeasible_iff_exists_slackExtension
#check StandardLP.slackExtension_eq_slack
#check StandardLP.existsUnique_slackExtension_iff

example {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    P.objective x = P.c ⬝ᵥ x := rfl

example {m n : ℕ} {P : StandardLP m n} {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s :=
  P.existsUnique_slackExtension_iff

#print axioms StandardLP.isFeasible_iff_exists_slackExtension
#print axioms StandardLP.existsUnique_slackExtension_iff

#check StandardLP.IsDualFeasible
#check StandardLP.dualObjective
#check StandardLP.IsDualFeasible.nonnegative
#check StandardLP.IsDualFeasible.coefficient_le

end Chapter29
end CLRS
