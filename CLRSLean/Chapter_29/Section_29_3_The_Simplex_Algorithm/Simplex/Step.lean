import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Leaving

/-!
# 29.3 One textbook SIMPLEX step

One call either certifies the optimal reduced-cost test, certifies an unbounded
entering direction, or returns the Bland entering/leaving pair for a PIVOT.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- The three outcomes of one textbook SIMPLEX iteration.  Every constructor
stores the mathematical certificate for its branch. -/
inductive SimplexStepResult (D : Dictionary m n) where
  /-- No reduced cost is positive. -/
  | optimal (reducedCostsNonpositive : ∀ j, D.c j ≤ 0)
  /-- A positive-reduced-cost column has no positive constraint coefficient. -/
  | unbounded (entering : Fin n)
      (enteringIsBland : D.IsBlandEntering entering)
      (columnNonpositive : ∀ i, D.a i entering ≤ 0)
  /-- Bland's rule selects a certified minimum-ratio PIVOT. -/
  | pivot (entering : Fin n) (leaving : Fin m)
      (enteringIsBland : D.IsBlandEntering entering)
      (leavingIsBland : D.IsBlandLeaving entering leaving)

namespace SimplexStepResult

/-- Whether a step result is the optimal terminal constructor. -/
def IsOptimal {D : Dictionary m n} : D.SimplexStepResult → Prop
  | .optimal _ => True
  | .unbounded _ _ _ => False
  | .pivot _ _ _ _ => False

/-- Recover the next dictionary exactly in the PIVOT branch. -/
noncomputable def nextDictionary {D : Dictionary m n} :
    D.SimplexStepResult → Option (Dictionary m n)
  | .optimal _ => none
  | .unbounded _ _ _ => none
  | .pivot e l _ hl =>
      some (D.pivot l e hl.1.pivotCoefficient_pos.ne')

end SimplexStepResult

/-- Execute one SIMPLEX iteration using Bland's rule. -/
noncomputable def simplexStep (D : Dictionary m n) : D.SimplexStepResult :=
  match henter : D.blandEntering? with
  | none =>
      .optimal ((D.blandEntering?_eq_none_iff).1 henter)
  | some e =>
      let he := D.blandEntering?_spec henter
      match hleave : D.blandLeaving? e with
      | none =>
          .unbounded e he ((D.blandLeaving?_eq_none_iff e).1 hleave)
      | some l =>
          .pivot e l he (D.blandLeaving?_spec e hleave)

/-- The optimal constructor is returned exactly when every reduced cost is
nonpositive. -/
theorem simplexStep_optimal_iff (D : Dictionary m n) :
    D.simplexStep.IsOptimal ↔ ∀ j, D.c j ≤ 0 := by
  cases hstep : D.simplexStep with
  | optimal h =>
      exact ⟨fun _ => h, fun _ => trivial⟩
  | unbounded e he _ =>
      constructor
      · intro hfalse
        exact False.elim hfalse
      · intro hall
        exact (not_lt_of_ge (hall e)) he.1
  | pivot e _ he _ =>
      constructor
      · intro hfalse
        exact False.elim hfalse
      · intro hall
        exact (not_lt_of_ge (hall e)) he.1

end Dictionary
end Chapter29
end CLRS
