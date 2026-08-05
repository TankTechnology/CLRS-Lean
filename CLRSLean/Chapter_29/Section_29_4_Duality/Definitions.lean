import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

/-!
# 29.4 Dual linear programs

For a primal maximization program {lit}`max cᵀx` with {lit}`Ax ≤ b` and
{lit}`x ≥ 0`, a dual assignment satisfies {lit}`y ≥ 0` and
{lit}`Aᵀy ≥ c`; its objective is {lit}`bᵀy`.

Main declarations:

- {lit}`StandardLP.IsDualFeasible`.
- {lit}`StandardLP.dualObjective`.

Current gaps:

- Weak duality is proved in the next module.
- Strong duality and complementary slackness remain unrepresented.
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- A nonnegative vector satisfying {lit}`c ≤ Aᵀy` is dual feasible. -/
def IsDualFeasible {m n : ℕ} (P : StandardLP m n) (y : Fin m → ℝ) : Prop :=
  IsNonnegative y ∧ ∀ j, P.c j ≤ (P.A.transpose *ᵥ y) j

/-- The dual objective value {lit}`bᵀy`. -/
def dualObjective {m n : ℕ} (P : StandardLP m n) (y : Fin m → ℝ) : ℝ :=
  P.b ⬝ᵥ y

namespace IsDualFeasible

/-- A dual-feasible assignment is coordinatewise nonnegative. -/
theorem nonnegative {m n : ℕ} {P : StandardLP m n} {y : Fin m → ℝ}
    (hy : P.IsDualFeasible y) : IsNonnegative y :=
  hy.1

/-- A dual-feasible assignment bounds each primal objective coefficient by
the corresponding coordinate of {lit}`Aᵀy`. -/
theorem coefficient_le {m n : ℕ} {P : StandardLP m n} {y : Fin m → ℝ}
    (hy : P.IsDualFeasible y) :
    ∀ j, P.c j ≤ (P.A.transpose *ᵥ y) j :=
  hy.2

end IsDualFeasible
end StandardLP
end Chapter29
end CLRS
