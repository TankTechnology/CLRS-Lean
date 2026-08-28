import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_25

/-! # Chapter 25 flagship trust surface -/

#check CLRS.Matchings.berge_maximum_iff_no_augmentingPath
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_bfs
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_attached_cost
#check CLRS.StableMarriage.gs_man_optimal
#check CLRS.AssignmentProblem.Problem.hungarian_constructs_optimal

#assert_axioms CLRS.Matchings.berge_maximum_iff_no_augmentingPath
#assert_axioms CLRS.Matchings.flowMethod_finds_maximum_matching_with_bfs
#assert_axioms CLRS.Matchings.flowMethod_finds_maximum_matching_with_attached_cost
#assert_axioms CLRS.StableMarriage.gs_man_optimal
#assert_axioms CLRS.AssignmentProblem.Problem.hungarian_constructs_optimal

example :
    let G : CLRS.Chapter26.BipartiteGraph Bool :=
      { L := {false}
        R := {true}
        h_disjoint := by decide
        h_cover := by decide
        E := {(false, true)}
        hE_subset := by decide }
    (CLRS.Chapter26.Matching.empty G).size = 0 := by
  rfl
