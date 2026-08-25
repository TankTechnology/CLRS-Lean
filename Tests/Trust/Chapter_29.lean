import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_29

/-! # Chapter 29 flagship trust surface -/

#check CLRS.Chapter29.GeneralLP.solve_complete
#check CLRS.Chapter29.StandardLP.strongDuality
#check CLRS.Chapter29.StandardLP.complementarySlackness_iff_optimal

#assert_axioms CLRS.Chapter29.GeneralLP.solve_complete
#assert_axioms CLRS.Chapter29.StandardLP.strongDuality
#assert_axioms CLRS.Chapter29.StandardLP.complementarySlackness_iff_optimal

example {m n : ℕ} (P : CLRS.Chapter29.StandardLP m n) (x : Fin n → ℝ) :
    P.objective x = P.c ⬝ᵥ x := by
  rfl
