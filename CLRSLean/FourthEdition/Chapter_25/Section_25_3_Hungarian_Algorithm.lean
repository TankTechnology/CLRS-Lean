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

/-- The *slack* of an edge with respect to a potential: how far the edge is
from being tight.  All slacks are nonnegative exactly when the potential is
feasible. -/
def slack (P : Problem V) (y : V → ℝ) (l r : V) : ℝ :=
  P.w l r - (y l + y r)

/-- The Hungarian potential adjustment: raise the potential on `S` by `δ` and
lower it on `T` by `δ`.  (CLRS §25.3.) -/
def adjustPotential (P : Problem V) (y : V → ℝ) (δ : ℝ) (S T : Finset V) : V → ℝ :=
  fun v => if v ∈ S then y v + δ else if v ∈ T then y v - δ else y v

/-- A right vertex cannot lie in `S` when `S` stays inside the left partition. -/
lemma not_mem_S_of_mem_R (P : Problem V) {S : Finset V} (hS : S ⊆ P.G.L) {r : V}
    (hr : r ∈ P.G.R) : r ∉ S := by
  intro hrS
  have hrL : r ∈ P.G.L := hS hrS
  have hboth : r ∈ P.G.L ∩ P.G.R := Finset.mem_inter.mpr ⟨hrL, hr⟩
  simpa [P.G.h_disjoint] using hboth

/-- A left vertex cannot lie in `T` when `T` stays inside the right partition. -/
lemma not_mem_T_of_mem_L (P : Problem V) {T : Finset V} (hT : T ⊆ P.G.R) {l : V}
    (hl : l ∈ P.G.L) : l ∉ T := by
  intro hlT
  have hrR : l ∈ P.G.R := hT hlT
  have hboth : l ∈ P.G.L ∩ P.G.R := Finset.mem_inter.mpr ⟨hl, hrR⟩
  simpa [P.G.h_disjoint] using hboth

/-- Raising potentials on `S` and lowering them on `T` by a nonnegative `δ`
that is no larger than the slack of every edge from `S` to outside `T`
preserves feasibility of the potential.  (CLRS §25.3, potential step.) -/
lemma adjust_preserves_feasible (P : Problem V) {y : V → ℝ} {δ : ℝ} {S T : Finset V}
    (hy : P.Feasible y) (hδ_nonneg : 0 ≤ δ) (hS : S ⊆ P.G.L) (hT : T ⊆ P.G.R)
    (hδ : ∀ l ∈ S, ∀ r, r ∈ P.G.R → r ∉ T → δ ≤ P.slack y l r) :
    P.Feasible (P.adjustPotential y δ S T) := by
  intro l hl r hr
  have hrS : r ∉ S := P.not_mem_S_of_mem_R hS hr
  have hlT : l ∉ T := P.not_mem_T_of_mem_L hT hl
  by_cases hlS : l ∈ S
  · by_cases hrT : r ∈ T
    · simp [adjustPotential, hlS, hrT, hrS]
      linarith [hy l hl r hr]
    · have hδ' : δ ≤ P.w l r - (y l + y r) := hδ l hlS r hr hrT
      simp [adjustPotential, hlS, hrT, hrS]
      linarith
  · by_cases hrT : r ∈ T
    · simp [adjustPotential, hlS, hrT, hlT, hrS]
      linarith [hy l hl r hr, hδ_nonneg]
    · simp [adjustPotential, hlS, hrT, hlT, hrS]
      exact hy l hl r hr

/-- An edge of a matching whose endpoints are adjusted in lockstep (an endpoint
lies in `S` iff the other lies in `T`) stays tight under the adjusted
potential, so the matching remains in the equality graph. -/
lemma adjust_preserves_tight_of_matching (P : Problem V) {y : V → ℝ} {δ : ℝ} {S T : Finset V}
    {M : Matching V P.G} (hTight : P.IsTightMatching y M)
    (hS : S ⊆ P.G.L) (hT : T ⊆ P.G.R)
    (hlock : ∀ e ∈ M.edges, (e.1 ∈ S ↔ e.2 ∈ T)) :
    P.IsTightMatching (P.adjustPotential y δ S T) M := by
  intro e he
  have heq : y e.1 + y e.2 = P.w e.1 e.2 := hTight e he
  rw [← heq]
  have hlock' : e.1 ∈ S ↔ e.2 ∈ T := hlock e he
  have he1_notT : e.1 ∉ T := P.not_mem_T_of_mem_L hT (M.left_mem_L he)
  have he2_notS : e.2 ∉ S := P.not_mem_S_of_mem_R hS (M.right_mem_R he)
  by_cases heS : e.1 ∈ S
  · have heT : e.2 ∈ T := hlock'.mp heS
    simp [adjustPotential, heS, heT, he2_notS]
  · have heT' : e.2 ∉ T := by
      intro hT2
      exact heS (hlock'.mpr hT2)
    simp [adjustPotential, heS, heT', he1_notT, he2_notS]

/-- If `δ` is attained as the slack of an edge from `S` to outside `T`, then
that edge becomes tight under the adjusted potential: the equality graph gains
an edge. -/
lemma adjust_creates_tight_edge (P : Problem V) {y : V → ℝ} {δ : ℝ} {S T : Finset V}
    (hS : S ⊆ P.G.L) (hT : T ⊆ P.G.R)
    (hδ_att : ∃ l ∈ S, ∃ r, r ∈ P.G.R ∧ r ∉ T ∧ P.slack y l r = δ) :
    ∃ l ∈ S, ∃ r, r ∈ P.G.R ∧ r ∉ T ∧ P.Tight (P.adjustPotential y δ S T) l r := by
  rcases hδ_att with ⟨l, hlS, r, hrR, hrT, hslack⟩
  have hl : l ∈ P.G.L := hS hlS
  refine ⟨l, hlS, r, hrR, hrT, ⟨hl, hrR, ?_⟩⟩
  have hrS : r ∉ S := P.not_mem_S_of_mem_R hS hrR
  simp [adjustPotential, hlS, hrT, hrS]
  unfold slack at hslack
  linarith

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
