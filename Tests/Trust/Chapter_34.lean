import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_34

/-! # Chapter 34 flagship trust surface -/

#check CLRS.Chapter34.Turing.CookLevin.cookLevin_theorem
#check CLRS.Chapter34.CLIQUE_npComplete
#check CLRS.Chapter34.VERTEXCOVER_npComplete
#check CLRS.Chapter34.HAMCYCLE_npComplete
#check CLRS.Chapter34.TSP_npComplete
#check CLRS.Chapter34.SUBSETSUM_npComplete

#assert_axioms CLRS.Chapter34.Turing.CookLevin.cookLevin_theorem
#assert_axioms CLRS.Chapter34.CLIQUE_npComplete

/-- One audit declaration closes over every NP-completeness theorem exposed by
§34.5, so the chapter keeps a three-declaration flagship budget without hiding
any of the four textbook reductions from the axiom audit. -/
private theorem section34_5_npComplete_bundle :
    CLRS.Chapter34.NPComplete CLRS.Chapter34.VERTEXCOVER ∧
      CLRS.Chapter34.NPComplete CLRS.Chapter34.HAMCYCLE ∧
      CLRS.Chapter34.NPComplete CLRS.Chapter34.TSP ∧
      CLRS.Chapter34.NPComplete CLRS.Chapter34.SUBSETSUM :=
  ⟨CLRS.Chapter34.VERTEXCOVER_npComplete,
    CLRS.Chapter34.HAMCYCLE_npComplete,
    CLRS.Chapter34.TSP_npComplete,
    CLRS.Chapter34.SUBSETSUM_npComplete⟩

#assert_axioms section34_5_npComplete_bundle
