import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API

/-!
# 25.3. The Hungarian algorithm for the assignment problem

This section formalizes the **assignment problem** and its solution by the
Hungarian algorithm, following CLRS §25.3.  A set of persons must be assigned
to the same number of tasks, each assignment carrying a cost; we must find a
minimum-cost perfect assignment.  This is modeled as a minimum-weight perfect
matching in a complete bipartite graph with equal-sized partitions.

The main structural result is **duality via potentials**: a feasible potential
(pair of dual labels satisfying `y_l + y_r ≤ w(l, r)` on every edge) makes the
*equality graph* of tight edges the right place to look.  Lemma 25.8 states that
any perfect matching lying entirely in the equality graph is an optimal
assignment.  The Hungarian algorithm maintains a feasible potential and a
matching in the equality graph, and iteratively either augments the matching or
adjusts the potential until a perfect matching is found.

Main results:

- `Problem`: a complete bipartite graph with equal-sized partitions and real
  edge weights
- `Matching.Perfect`: a matching of size `G.L.card` (covering every vertex)
- `cost` / `Optimal`: total weight of a matching; optimal assignments
- `Feasible`: a potential is feasible when `y_l + y_r ≤ w(l, r)` on every edge
- `Tight` / `IsTightMatching`: tight edges and matchings in the equality graph
- `perfect_tight_optimal` (Lemma 25.8): a perfect matching in the equality
  graph of a feasible potential is an optimal assignment

Current gaps:

- The constructive existence of an optimal assignment via the full Hungarian
  algorithm (potential adjustment + augmentation loop) is not yet formalized;
  it will appear in a follow-up module.

Notation conventions used in this section:

- `P` : assignment problem
- `G` : the underlying complete bipartite graph
- `w` : the weight function on edges
- `y` : a potential (dual variable)
- `M` : a matching
- `L` / `R` : the two equal-sized partitions of `G`
-/

namespace CLRS

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Chapter26

namespace Matching

/-- A matching is *perfect* when it covers every vertex; in a balanced
bipartite graph this is exactly having `G.L.card` edges. -/
def Perfect {G : BipartiteGraph V} (M : Matching V G) : Prop :=
  M.size = G.L.card

end Matching

end Chapter26

namespace AssignmentProblem

open Chapter26

/-- An instance of the assignment problem: a complete bipartite graph with
equal-sized partitions `L` and `R`, together with a real weight `w l r` on
every edge.  (CLRS §25.3.) -/
structure Problem (V : Type*) [Fintype V] [DecidableEq V] where
  G : BipartiteGraph V
  w : V → V → ℝ
  h_complete : ∀ l ∈ G.L, ∀ r ∈ G.R, (l, r) ∈ G.E
  h_eq_card : G.L.card = G.R.card

namespace Problem

/-- The total weight (cost) of a matching, summed over its edges. -/
def cost (P : Problem V) (M : Matching V P.G) : ℝ :=
  M.edges.sum fun e => P.w e.1 e.2

/-- A matching is an *optimal assignment* when it is perfect and no perfect
matching has strictly lower cost. -/
def Optimal (P : Problem V) (M : Matching V P.G) : Prop :=
  M.Perfect ∧ ∀ M' : Matching V P.G, M'.Perfect → P.cost M ≤ P.cost M'

/-- A *potential* is feasible when on every edge the sum of the endpoint
potentials is at most the edge weight.  (CLRS §25.3.) -/
def Feasible (P : Problem V) (y : V → ℝ) : Prop :=
  ∀ l ∈ P.G.L, ∀ r ∈ P.G.R, y l + y r ≤ P.w l r

/-- A tight edge with respect to a potential: feasibility is attained. -/
def Tight (P : Problem V) (y : V → ℝ) (l r : V) : Prop :=
  l ∈ P.G.L ∧ r ∈ P.G.R ∧ y l + y r = P.w l r

/-- A matching lies in the *equality graph* of a potential when every one of
its edges is tight. -/
def IsTightMatching (P : Problem V) (y : V → ℝ) (M : Matching V P.G) : Prop :=
  ∀ e ∈ M.edges, y e.1 + y e.2 = P.w e.1 e.2

end Problem

/-- Summing a function over the left endpoints of a matching equals summing it
over the matching edges, because left endpoints are distinct. -/
lemma sum_fst_image (M : Matching V G) (y : V → ℝ) :
    M.matchedLeft.sum y = M.edges.sum fun e => y e.1 := by
  unfold Matching.matchedLeft
  rw [Finset.sum_image]
  intro e₁ he₁ e₂ he₂ h
  exact Prod.ext h (M.h_unique_left e₁.1 e₁.2 e₂.2 he₁ (by simpa [h] using he₂))

/-- Summing a function over the right endpoints of a matching equals summing it
over the matching edges, because right endpoints are distinct. -/
lemma sum_snd_image (M : Matching V G) (y : V → ℝ) :
    M.matchedRight.sum y = M.edges.sum fun e => y e.2 := by
  unfold Matching.matchedRight
  rw [Finset.sum_image]
  intro e₁ he₁ e₂ he₂ h
  exact Prod.ext (M.h_unique_right e₁.1 e₂.1 e₁.2 he₁ (by simpa [h] using he₂)) h

/-- A perfect matching matches every left vertex. -/
lemma perfect_matchedLeft_eq (M : Matching V G) (hP : M.Perfect) :
    M.matchedLeft = G.L := by
  apply Finset.eq_of_subset_of_card_le
  · intro l hl
    rw [M.mem_matchedLeft_iff l] at hl
    exact M.mem_L_of_isMatchedLeft hl
  · change M.size = G.L.card at hP
    rw [← hP, M.matchedLeft_card]

/-- In a balanced bipartite graph, a perfect matching matches every right
vertex. -/
lemma perfect_matchedRight_eq (P : Problem V) (M : Matching V P.G) (hP : M.Perfect) :
    M.matchedRight = P.G.R := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [M.mem_matchedRight_iff r] at hr
    exact M.mem_R_of_isMatchedRight hr
  · change M.size = P.G.L.card at hP
    rw [M.matchedRight_card, hP, P.h_eq_card]

/-- For a perfect matching, the sum of endpoint potentials over its edges
splits into the sum over `L` plus the sum over `R`. -/
lemma perfect_potential_sum_eq (P : Problem V) (M : Matching V P.G) (hP : M.Perfect)
    (y : V → ℝ) :
    M.edges.sum (fun e => y e.1 + y e.2) = (P.G.L.sum y) + (P.G.R.sum y) := by
  rw [Finset.sum_add_distrib]
  rw [← sum_fst_image, ← sum_snd_image]
  rw [perfect_matchedLeft_eq M hP, perfect_matchedRight_eq P M hP]

/-- The cost of any perfect matching is at least the sum of a feasible
potential over all vertices. -/
lemma feasible_cost_lower_bound (P : Problem V) {y : V → ℝ} (hy : P.Feasible y)
    (M : Matching V P.G) (hP : M.Perfect) :
    (P.G.L.sum y) + (P.G.R.sum y) ≤ P.cost M := by
  calc
    (P.G.L.sum y) + (P.G.R.sum y) = M.edges.sum (fun e => y e.1 + y e.2) := by
      exact (perfect_potential_sum_eq P M hP y).symm
    _ ≤ M.edges.sum (fun e => P.w e.1 e.2) := by
      apply Finset.sum_le_sum
      intro e he
      exact hy e.1 (M.left_mem_L (by simpa using he)) e.2 (M.right_mem_R (by simpa using he))
    _ = P.cost M := by rfl

/--
**Theorem (dual optimality, CLRS Lemma 25.8).**  Let `y` be a feasible
potential.  If `M` is a perfect matching that lies entirely in the equality
graph of `y`, then `M` is an optimal assignment.
-/
theorem perfect_tight_optimal (P : Problem V) {y : V → ℝ} (hy : P.Feasible y)
    (M : Matching V P.G) (hP : M.Perfect) (hT : P.IsTightMatching y M) :
    P.Optimal M := by
  exact ⟨hP, by
    intro M' hM'
    have hsum : (P.G.L.sum y) + (P.G.R.sum y) = P.cost M := by
      calc
        (P.G.L.sum y) + (P.G.R.sum y) = M.edges.sum (fun e => y e.1 + y e.2) := by
          exact (perfect_potential_sum_eq P M hP y).symm
        _ = M.edges.sum (fun e => P.w e.1 e.2) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hT e he
        _ = P.cost M := by rfl
    have hlow : (P.G.L.sum y) + (P.G.R.sum y) ≤ P.cost M' :=
      feasible_cost_lower_bound P hy M' hM'
    simpa [hsum] using hlow⟩

end AssignmentProblem

end CLRS
