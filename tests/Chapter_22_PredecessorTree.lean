import CLRSLean.FourthEdition.Chapter_22.Section_22_5_Shortest_Path_Properties.PredecessorTree

open CLRS.Chapter24
open WeightedGraph

#check WeightedGraph.shortestPathTree
#check WeightedGraph.shortestPathTree_correct
#check WeightedGraph.tightGraph_reachable_iff
#check WeightedGraph.shortestPathTree_parent_defined_iff
#check WeightedGraph.shortestPathTree_parent_depth_lt
#check WeightedGraph.shortestPathTree_path
#check WeightedGraph.shortestPathTree_acyclic

namespace PredecessorTreeTests

-- The audited zero-weight tight cycle, plus an unreachable vertex.
def zeroCycle : WeightedGraph (Fin 4) where
  edges := {(0, 1), (0, 2), (1, 2), (2, 1)}
  w := fun _ _ => 0

private theorem zero_weight (p : List (Fin 4)) : walkWeight zeroCycle.w p = 0 := by
  induction p with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp_all [walkWeight, zeroCycle]

private theorem zero_noNegCycle : zeroCycle.NoNegCycle := by
  intro x p hp
  rw [zero_weight]

private theorem source_walk : zeroCycle.IsWalkFrom 0 0 [0] := ⟨by simp, rfl, rfl⟩
private theorem one_walk : zeroCycle.IsWalkFrom 0 1 [0, 1] :=
  IsWalkFrom.append_edge zeroCycle source_walk (by decide)
private theorem two_walk : zeroCycle.IsWalkFrom 0 2 [0, 2] :=
  IsWalkFrom.append_edge zeroCycle source_walk (by decide)

private theorem distance_zero (v : Fin 4) (hr : ∃ p, zeroCycle.IsWalkFrom 0 v p) :
    zeroCycle.shortestDist 0 v = 0 := by
  obtain ht | ⟨p, hp, hw⟩ := (zeroCycle.shortestDist_isShortestDist zero_noNegCycle 0 v).2
  · exact ((zeroCycle.noPath_iff_top zero_noNegCycle 0 v).mp ht hr).elim
  · simpa [zero_weight] using hw.symm

-- All four original edges are tight, including the problematic directed cycle.
example : (zeroCycle.tightGraph 0).Adj 1 2 ∧ (zeroCycle.tightGraph 0).Adj 2 1 := by
  simp only [tightGraph_adj]
  have h1 := distance_zero 1 ⟨_, one_walk⟩
  have h2 := distance_zero 2 ⟨_, two_walk⟩
  constructor <;> refine ⟨by decide, ?_⟩
  · change zeroCycle.shortestDist 0 2 = zeroCycle.shortestDist 0 1 + (0 : WithTop ℝ)
    simp [h1, h2]
  · change zeroCycle.shortestDist 0 1 = zeroCycle.shortestDist 0 2 + (0 : WithTop ℝ)
    simp [h1, h2]

def cyclicParents (v : Fin 4) : Option (Fin 4) :=
  if v = 1 then some 2 else if v = 2 then some 1 else none

-- Tightness alone permits a cycle: these are real original zero-weight edges.
example : Relation.TransGen (fun u v => cyclicParents v = some u) 1 1 :=
  .tail (.single (by decide : cyclicParents 2 = some 1)) (by decide)

-- The actual constructor avoids the cycle and chooses direct source parents.
example : (zeroCycle.shortestPathTree 0).parent 1 = some 0 := by
  apply zeroCycle.shortestPathTree_parent_of_tight_source_edge 0 1 (by decide) (by decide)
  rw [distance_zero 1 ⟨_, one_walk⟩, distance_zero 0 ⟨_, source_walk⟩]
  simp [zeroCycle]

example : (zeroCycle.shortestPathTree 0).parent 2 = some 0 := by
  apply zeroCycle.shortestPathTree_parent_of_tight_source_edge 0 2 (by decide) (by decide)
  rw [distance_zero 2 ⟨_, two_walk⟩, distance_zero 0 ⟨_, source_walk⟩]
  simp [zeroCycle]

example : (zeroCycle.shortestPathTree 0).parent 0 = none ∧
    (zeroCycle.shortestPathTree 0).depth 0 = some 0 := by simp

private theorem three_unreachable : ¬ ∃ p, zeroCycle.IsWalkFrom 0 3 p := by
  intro hr
  have hn := zeroCycle.preds_nonempty_of_walk 0 3 (by decide) hr
  have he : zeroCycle.preds 3 = ∅ := by decide
  rw [he] at hn
  exact Finset.not_nonempty_empty hn

example : (zeroCycle.shortestPathTree 0).parent 3 = none ∧
    (zeroCycle.shortestPathTree 0).depth 3 = none :=
  zeroCycle.shortestPathTree_unreachable zero_noNegCycle 0 3 three_unreachable

example : (zeroCycle.shortestPathTree 0).distance 3 = ⊤ :=
  (zeroCycle.noPath_iff_top zero_noNegCycle 0 3).mpr three_unreachable

example (v : Fin 4) : ¬ Relation.TransGen
    (fun u w => (zeroCycle.shortestPathTree 0).parent w = some u) v v :=
  zeroCycle.shortestPathTree_acyclic 0 v

example : zeroCycle.IsShortestPathPredecessorTree 0 (zeroCycle.shortestPathTree 0) :=
  zeroCycle.shortestPathTree_correct zero_noNegCycle 0

-- The returned path follows the returned parents and has the computed weight.
example : ∃ d p, (zeroCycle.shortestPathTree 0).depth 2 = some d ∧
    zeroCycle.IsWalkFrom 0 2 p ∧ p.length = d + 1 ∧
    List.IsChain (fun u v => (zeroCycle.shortestPathTree 0).parent v = some u) p ∧
    walkWeight zeroCycle.w p = 0 := by
  obtain ⟨d, hd⟩ := (zeroCycle.shortestPathTree_depth_defined_iff zero_noNegCycle 0 2).mpr ⟨_, two_walk⟩
  obtain ⟨p, hp, hlen, hparents, hw⟩ := zeroCycle.shortestPathTree_path zero_noNegCycle 0 hd
  refine ⟨d, p, hd, hp, hlen, hparents, ?_⟩
  have hw0 : (walkWeight zeroCycle.w p : WithTop ℝ) = 0 := by
    simpa only [shortestPathTree_distance, distance_zero 2 ⟨_, two_walk⟩] using hw
  exact_mod_cast hw0

-- A nonzero-weight example checks the returned path's weighted value too.
def weightedEdge : WeightedGraph (Fin 2) where
  edges := {(0, 1)}
  w := fun _ _ => 7

private theorem weighted_nonneg (p : List (Fin 2)) : 0 ≤ walkWeight weightedEdge.w p := by
  induction p with
  | nil => norm_num [walkWeight]
  | cons x xs ih =>
    cases xs with
    | nil => norm_num [walkWeight]
    | cons y ys =>
      change 0 ≤ 7 + walkWeight weightedEdge.w (y :: ys)
      linarith

private theorem weighted_noNegCycle : weightedEdge.NoNegCycle :=
  fun _ p _ => weighted_nonneg p

private theorem weighted_source : weightedEdge.shortestDist 0 0 = 0 := by
  norm_num [shortestDist, relaxDist, relaxStep, preds, weightedEdge, Finset.univ_fin2]

private theorem weighted_distance : weightedEdge.shortestDist 0 1 = (7 : WithTop ℝ) := by
  norm_num [shortestDist, relaxDist, relaxStep, preds, weightedEdge, Finset.univ_fin2]
  have hf : {x ∈ ({0, 1} : Finset (Fin 2)) | x = 0} = {0} := by decide
  rw [hf]
  norm_num

example : ∃ p, weightedEdge.IsWalkFrom 0 1 p ∧ p.length = 2 ∧
    List.IsChain (fun u v => (weightedEdge.shortestPathTree 0).parent v = some u) p ∧
    walkWeight weightedEdge.w p = 7 := by
  have hp : (weightedEdge.shortestPathTree 0).parent 1 = some 0 := by
    apply weightedEdge.shortestPathTree_parent_of_tight_source_edge 0 1 (by decide) (by decide)
    rw [weighted_source, weighted_distance]
    norm_num [weightedEdge]
  obtain ⟨_, _, d, h0, h1⟩ := weightedEdge.shortestPathTree_parent_step 0 hp
  have hd0 : d = 0 := by
    rw [shortestPathTree_source_depth] at h0
    exact (Option.some.inj h0).symm
  rw [hd0] at h1
  obtain ⟨p, hwalk, hlen, hparents, hw⟩ := weightedEdge.shortestPathTree_path weighted_noNegCycle 0 h1
  refine ⟨p, hwalk, hlen, hparents, ?_⟩
  have hw7 : (walkWeight weightedEdge.w p : WithTop ℝ) = (7 : WithTop ℝ) := by
    simpa only [shortestPathTree_distance, weighted_distance] using hw
  exact WithTop.coe_injective hw7

#print axioms WeightedGraph.tightGraph_reachable_iff
#print axioms WeightedGraph.shortestPathTree_correct
#print axioms WeightedGraph.shortestPathTree_path
#print axioms WeightedGraph.shortestPathTree_acyclic

end PredecessorTreeTests
