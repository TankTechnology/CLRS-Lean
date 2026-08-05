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

example {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    P.objective x = P.c ⬝ᵥ x := rfl

end Chapter29
end CLRS
