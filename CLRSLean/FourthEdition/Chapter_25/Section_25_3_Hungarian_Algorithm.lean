import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S2_Alternating_Paths

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

namespace Matchings

/-- Appending two vertices to an odd-length nonempty vertex list adds one
forward edge `(last, a)` and one backward edge `(b, a)`. -/
lemma altEdges_append_pair (p : List V) (hp : Odd p.length) (hne : p ≠ []) {a b : V} :
    (altEdges (p ++ [a, b])).1 = (altEdges p).1 ++ [(p.getLast hne, a)] ∧
    (altEdges (p ++ [a, b])).2 = (altEdges p).2 ++ [(b, a)] := by
  induction p using altEdges.induct with
  | case1 =>
      exact False.elim (hne rfl)
  | case2 x =>
      constructor <;> simp [altEdges]
  | case3 x y rest ih =>
      cases rest with
      | nil =>
          have hp' : Odd (2 : ℕ) := by simpa using hp
          norm_num at hp'
      | cons z zs =>
          have hrest_ne : z :: zs ≠ [] := by simp
          have hrest_odd : Odd (z :: zs).length := by
            rw [show (x :: y :: z :: zs).length = 2 + (z :: zs).length by simp; omega] at hp
            rcases hp with ⟨k, hk⟩
            refine ⟨k - 1, ?_⟩
            omega
          have ih' := ih hrest_odd hrest_ne
          have hgl : (x :: y :: z :: zs).getLast hne = (z :: zs).getLast hrest_ne := by
            simp [List.getLast_cons]
          constructor
          · change (x, y) :: (altEdges (z :: zs ++ [a, b])).1 =
              (x, y) :: ((altEdges (z :: zs)).1 ++ [((x :: y :: z :: zs).getLast hne, a)])
            rw [ih'.1, hgl]
          · change (z, y) :: (altEdges (z :: zs ++ [a, b])).2 =
              (z, y) :: ((altEdges (z :: zs)).2 ++ [(b, a)])
            rw [ih'.2]

/-- Appending a single vertex to an odd-length nonempty vertex list adds one
forward edge `(last, r)` and no backward edge. -/
lemma altEdges_append_single (p : List V) (hp : Odd p.length) (hne : p ≠ []) {r : V} :
    (altEdges (p ++ [r])).1 = (altEdges p).1 ++ [(p.getLast hne, r)] ∧
    (altEdges (p ++ [r])).2 = (altEdges p).2 := by
  induction p using altEdges.induct with
  | case1 =>
      exact False.elim (hne rfl)
  | case2 x =>
      constructor <;> simp [altEdges]
  | case3 x y rest ih =>
      cases rest with
      | nil =>
          have hp' : Odd (2 : ℕ) := by simpa using hp
          norm_num at hp'
      | cons z zs =>
          have hrest_ne : z :: zs ≠ [] := by simp
          have hrest_odd : Odd (z :: zs).length := by
            rw [show (x :: y :: z :: zs).length = 2 + (z :: zs).length by simp; omega] at hp
            rcases hp with ⟨k, hk⟩
            refine ⟨k - 1, ?_⟩
            omega
          have ih' := ih hrest_odd hrest_ne
          have hgl : (x :: y :: z :: zs).getLast hne = (z :: zs).getLast hrest_ne := by
            simp [List.getLast_cons]
          constructor
          · change (x, y) :: (altEdges (z :: zs ++ [r])).1 =
              (x, y) :: ((altEdges (z :: zs)).1 ++ [((x :: y :: z :: zs).getLast hne, r)])
            rw [ih'.1, hgl]
          · change (z, y) :: (altEdges (z :: zs ++ [r])).2 =
              (z, y) :: ((altEdges (z :: zs)).2)
            rw [ih'.2]

end Matchings

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

namespace Problem

/-- The type of matchings of a finite bipartite graph is finite, because a
matching is determined by its edge set. -/
noncomputable instance instFintypeMatching (P : Problem V) : Fintype (Matching V P.G) := by
  classical
  exact Fintype.ofInjective Matching.edges (by
    intro M N h
    cases M
    cases N
    simp [Matching.edges] at h
    subst h
    congr)

/-- Since `L` and `R` have equal cardinality, there is a bijection between
them.  This is the pairing that makes a perfect matching explicit. -/
noncomputable def L_eq_R (P : Problem V) : {x : V // x ∈ P.G.L} ≃ {x : V // x ∈ P.G.R} := by
  classical
  let eL := Fintype.equivFin (α := {x : V // x ∈ P.G.L})
  let eR := Fintype.equivFin (α := {x : V // x ∈ P.G.R})
  let hc : Fintype.card {x : V // x ∈ P.G.L} = Fintype.card {x : V // x ∈ P.G.R} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rw [show (Finset.univ.filter (fun x : V => x ∈ P.G.L)) = P.G.L by ext x; simp]
    rw [show (Finset.univ.filter (fun x : V => x ∈ P.G.R)) = P.G.R by ext x; simp]
    exact P.h_eq_card
  exact (eL.trans (Equiv.cast (congrArg Fin hc))).trans eR.symm

/-- A perfect matching obtained by pairing the elements of `L` with the
elements of `R` through the bijection `L_eq_R`.  Existence of a perfect
matching in a complete balanced bipartite graph. -/
noncomputable def perfectMatching (P : Problem V) : Matching V P.G where
  edges := Finset.univ.image (fun l : {x : V // x ∈ P.G.L} => (l.1, (P.L_eq_R l).1))
  h_subset := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨l, hl, rfl⟩
    exact P.h_complete l.1 l.2 (P.L_eq_R l).1 (P.L_eq_R l).2
  h_unique_left := by
    intro l r₁ r₂ h₁ h₂
    rw [Finset.mem_image] at h₁ h₂
    rcases h₁ with ⟨a₁, ha₁, hf₁⟩
    rcases h₂ with ⟨a₂, ha₂, hf₂⟩
    have ha1 : a₁.1 = l := by simpa using (congrArg Prod.fst hf₁)
    have ha2 : a₂.1 = l := by simpa using (congrArg Prod.fst hf₂)
    have heq : a₁ = a₂ := Subtype.ext (ha1.trans ha2.symm)
    have hs1 : (P.L_eq_R a₁).1 = r₁ := by simpa using (congrArg Prod.snd hf₁)
    have hs2 : (P.L_eq_R a₂).1 = r₂ := by simpa using (congrArg Prod.snd hf₂)
    rw [← hs1, ← hs2]
    rw [heq]
  h_unique_right := by
    intro l₁ l₂ r h₁ h₂
    rw [Finset.mem_image] at h₁ h₂
    rcases h₁ with ⟨a₁, ha₁, hf₁⟩
    rcases h₂ with ⟨a₂, ha₂, hf₂⟩
    have hl1 : a₁.1 = l₁ := by simpa using (congrArg Prod.fst hf₁)
    have hl2 : a₂.1 = l₂ := by simpa using (congrArg Prod.fst hf₂)
    have hs1 : (P.L_eq_R a₁).1 = r := by simpa using (congrArg Prod.snd hf₁)
    have hs2 : (P.L_eq_R a₂).1 = r := by simpa using (congrArg Prod.snd hf₂)
    have hRval : (P.L_eq_R a₁).1 = (P.L_eq_R a₂).1 := by
      rw [hs1, hs2]
    have hRsub : P.L_eq_R a₁ = P.L_eq_R a₂ := Subtype.ext hRval
    have haeq : a₁ = a₂ := (Equiv.injective (P.L_eq_R)) hRsub
    rw [← hl1, ← hl2]
    exact congrArg Subtype.val haeq

/-- The constructed matching is perfect. -/
theorem perfectMatching_perfect (P : Problem V) : (P.perfectMatching).Perfect := by
  classical
  simp [Matching.Perfect, Matching.size, perfectMatching]
  have hinj : Function.Injective (fun l : {x : V // x ∈ P.G.L} => (l.1, (P.L_eq_R l).1)) := by
    intro a b h
    exact Subtype.ext (by simpa using (congrArg Prod.fst h))
  rw [Finset.card_image_of_injective (s := P.G.L.attach)
    (f := fun l : {x : V // x ∈ P.G.L} => (l.1, (P.L_eq_R l).1)) hinj]
  simp

/-- A perfect matching exists in a complete balanced bipartite graph. -/
theorem exists_perfect_matching (P : Problem V) : ∃ M : Matching V P.G, M.Perfect :=
  ⟨P.perfectMatching, P.perfectMatching_perfect⟩

/-- An optimal assignment exists.  The finite set of perfect matchings is
nonempty, and the cost function attains its minimum on it. -/
theorem exists_optimal_assignment (P : Problem V) : ∃ M : Matching V P.G, P.Optimal M := by
  classical
  let ms : Finset (Matching V P.G) := Finset.univ.filter (fun M => M.Perfect)
  have hne : ms.Nonempty := by
    refine ⟨P.perfectMatching, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.perfectMatching_perfect⟩
  let costs : Finset ℝ := ms.image (fun M => P.cost M)
  have hcosts_ne : costs.Nonempty := Finset.image_nonempty.mpr hne
  let c : ℝ := costs.min' hcosts_ne
  have hc_mem : c ∈ costs := Finset.min'_mem costs hcosts_ne
  rcases Finset.mem_image.mp hc_mem with ⟨M, hM, hcost⟩
  refine ⟨M, ?_⟩
  have hMperf : M.Perfect := (Finset.mem_filter.mp hM).2
  refine ⟨hMperf, ?_⟩
  intro M' hM'perf
  have hM'mem : M' ∈ ms := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM'perf⟩
  have hM'cost : P.cost M' ∈ costs := Finset.mem_image.mpr ⟨M', hM'mem, rfl⟩
  have hle : c ≤ P.cost M' := by
    simpa [c] using (Finset.min'_le costs (P.cost M') hM'cost)
  rw [← hcost] at hle
  exact hle

/-! ## The Hungarian algorithm -/

/--
The **alternating tree** of the Hungarian algorithm (CLRS §25.3): the sets
`S ⊆ L` and `T ⊆ R` reachable from a free root `u` through alternating paths
in the equality graph of a feasible potential `y`, together with the tree
edge that reaches each right vertex.

The matching restricts to a bijection between `T` and `S∖{u}`: every right
vertex of the tree is matched to a left vertex in `S`, and every non-root
left vertex is matched to a right vertex in `T`.  `treeParent r` is the left
vertex whose tight edge `(treeParent r, r)` introduced `r` into the tree;
`rank` strictly decreases toward the root along tree edges, which makes the
augmenting path and the termination arguments well-founded.
-/
structure HungarianTree (P : Problem V) (y : V → ℝ) (M : Matching V P.G) where
  u : V
  S : Finset V
  T : Finset V
  /-- `S` stays inside the left partition. -/
  hS_subset : S ⊆ P.G.L
  /-- `T` stays inside the right partition. -/
  hT_subset : T ⊆ P.G.R
  /-- The root `u` lies in `S`. -/
  hu_mem : u ∈ S
  /-- The root `u` is unmatched by `M`. -/
  hu_free : M.IsUnmatchedLeft u
  /-- Every right vertex of the tree is matched. -/
  hT_matched : ∀ r ∈ T, r ∈ M.matchedRight
  /-- The matched partner of a right tree vertex lies in `S`, off the root. -/
  hpartner_in_S : ∀ r ∈ T, ∀ l, (l, r) ∈ M.edges → l ∈ S ∧ l ≠ u
  /-- Every non-root left vertex of the tree is matched. -/
  hleft_matched : ∀ l ∈ S, l ≠ u → l ∈ M.matchedLeft
  /-- The matched partner of a non-root left vertex lies in `T`. -/
  hpartner_in_T : ∀ l ∈ S, l ≠ u → ∀ r, (l, r) ∈ M.edges → r ∈ T
  /-- The tight non-matching tree edge that reaches each right vertex. -/
  treeParent : V → V
  /-- `treeParent r` lies in `S`. -/
  htree_parent_mem : ∀ r ∈ T, treeParent r ∈ S
  /-- The tree edge reaching `r` is tight. -/
  htree_tight : ∀ r ∈ T, P.Tight y (treeParent r) r
  /-- Tree edges are not matching edges. -/
  htree_not_matching : ∀ r ∈ T, (treeParent r, r) ∉ M.edges
  /-- `rank` measures the distance from `u`. -/
  rank : V → ℕ
  /-- The root has rank `0`. -/
  hrank_u : rank u = 0
  /-- Ranks strictly decrease toward the root along tree edges. -/
  hrank_lt : ∀ r ∈ T, rank (treeParent r) < rank r
  /-- A right vertex and its matched partner share a rank. -/
  hrank_match : ∀ r ∈ T, ∀ l, (l, r) ∈ M.edges → rank l = rank r

/-- The left set of a tree is nonempty (it contains the root). -/
lemma tree_S_nonempty {P : Problem V} {y : V → ℝ} {M : Matching V P.G}
    (tree : HungarianTree P y M) : tree.S.Nonempty :=
  ⟨tree.u, tree.hu_mem⟩

/-- The matched partner of a matched right vertex. -/
noncomputable def matchedPartner {P : Problem V} (M : Matching V P.G) {r : V}
    (hr : r ∈ M.matchedRight) : V :=
  Classical.choose ((M.mem_matchedRight_iff r).mp hr)

/-- The matched partner is indeed matched to the right vertex. -/
lemma matchedPartner_mem {P : Problem V} (M : Matching V P.G) {r : V}
    (hr : r ∈ M.matchedRight) : (matchedPartner M hr, r) ∈ M.edges :=
  Classical.choose_spec ((M.mem_matchedRight_iff r).mp hr)

/-- A tight edge from `S` to a right vertex outside `T` is never a matching
edge: every matching edge leaving `S` ends inside `T`. -/
lemma tight_edge_not_matching {P : Problem V} {y : V → ℝ} {M : Matching V P.G}
    (tree : HungarianTree P y M) {l r : V}
    (hl : l ∈ tree.S) (hrR : r ∈ P.G.R) (hnotT : r ∉ tree.T) (ht : P.Tight y l r) :
    (l, r) ∉ M.edges := by
  intro hlr
  by_cases hlu : l = tree.u
  · subst l
    exact tree.hu_free r hlr
  · have hlmat : l ∈ M.matchedLeft := tree.hleft_matched l hl hlu
    rcases (M.mem_matchedLeft_iff l).mp hlmat with ⟨r', hlr'⟩
    have hr'T : r' ∈ tree.T := tree.hpartner_in_T l hl hlu r' hlr'
    have : r = r' := M.h_unique_left l r r' hlr hlr'
    exact hnotT (this ▸ hr'T)

/-- A tight edge whose left endpoint is raised and whose right endpoint is
lowered by the same amount stays tight: the sum `y_l + y_r` is unchanged. -/
lemma adjust_preserves_tight_of_Tree (P : Problem V) {y : V → ℝ} {δ : ℝ} {S T : Finset V}
    (hS : S ⊆ P.G.L) (hT : T ⊆ P.G.R) {l r : V} (hl : l ∈ S) (hr : r ∈ T)
    (ht : P.Tight y l r) : P.Tight (P.adjustPotential y δ S T) l r := by
  have hlT : l ∉ T := P.not_mem_T_of_mem_L hT (hS hl)
  have hrS : r ∉ S := P.not_mem_S_of_mem_R hS (hT hr)
  rcases ht with ⟨hlL, hrR, htight⟩
  refine ⟨hlL, hrR, ?_⟩
  simp [adjustPotential, hl, hr, hrS]
  linarith

/-- The matching is injective from `T` into `S∖{u}`, so `T` has at most
`|S| − 1` elements. -/
lemma tree_T_le {P : Problem V} {y : V → ℝ} {M : Matching V P.G}
    (tree : HungarianTree P y M) : tree.T.card ≤ tree.S.card - 1 := by
  let f : {x : V // x ∈ tree.T} → V :=
    fun r => matchedPartner M (tree.hT_matched r.1 r.2)
  have hinj : Function.Injective f := by
    intro r₁ r₂ h
    have h₁ : (matchedPartner M (tree.hT_matched r₁.1 r₁.2), r₁.1) ∈ M.edges :=
      matchedPartner_mem M (tree.hT_matched r₁.1 r₁.2)
    have h₂ : (matchedPartner M (tree.hT_matched r₂.1 r₂.2), r₂.1) ∈ M.edges :=
      matchedPartner_mem M (tree.hT_matched r₂.1 r₂.2)
    have hlt : r₁.1 = r₂.1 := by
      -- `h` identifies the two matched partners; rewrite the partner of `r₂`
      -- to that of `r₁` in the second edge, then use left-uniqueness.
      unfold f at h
      rw [h.symm] at h₂
      exact M.h_unique_left (matchedPartner M (tree.hT_matched r₁.1 r₁.2)) r₁.1 r₂.1 h₁ h₂
    exact Subtype.ext hlt
  have himg : tree.T.attach.image f ⊆ tree.S.erase tree.u := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨r, hr, hfr⟩
    have hpart : f r ∈ tree.S ∧ f r ≠ tree.u :=
      tree.hpartner_in_S r.1 r.2 (matchedPartner M (tree.hT_matched r.1 r.2))
        (matchedPartner_mem M (tree.hT_matched r.1 r.2))
    rw [hfr] at hpart
    exact Finset.mem_erase.mpr ⟨hpart.2, hpart.1⟩
  have hcard : tree.T.attach.card ≤ (tree.S.erase tree.u).card := by
    calc
      tree.T.attach.card = (tree.T.attach.image f).card := by
        exact (Finset.card_image_of_injective tree.T.attach hinj).symm
      _ ≤ (tree.S.erase tree.u).card := Finset.card_le_card himg
  rwa [Finset.card_attach, Finset.card_erase_of_mem tree.hu_mem] at hcard

/-- Some right vertex lies outside the tree, so the slack minimum is taken
over a nonempty set of edges. -/
lemma tree_R_diff_T_nonempty {P : Problem V} {y : V → ℝ} {M : Matching V P.G}
    (tree : HungarianTree P y M) : (P.G.R \ tree.T).Nonempty := by
  have huL : tree.u ∈ P.G.L := tree.hS_subset tree.hu_mem
  have hRpos : 0 < P.G.R.card := by
    rw [← P.h_eq_card]
    exact Finset.card_pos.mpr ⟨tree.u, huL⟩
  have hT : tree.T.card < P.G.R.card := by
    have h1 : tree.T.card ≤ tree.S.card - 1 := tree_T_le tree
    have h2 : tree.S.card - 1 ≤ P.G.L.card - 1 := by
      have hSL : tree.S.card ≤ P.G.L.card := Finset.card_le_card tree.hS_subset
      omega
    have h3 : P.G.L.card - 1 ≤ P.G.R.card - 1 := by rw [P.h_eq_card]
    omega
  have hsub : tree.T ⊆ P.G.R := tree.hT_subset
  have hpos : 0 < (P.G.R \ tree.T).card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  exact Finset.card_pos.mp hpos

/-- The minimum slack over the edges from `S` to `R \ T`.  This is the
potential adjustment `δ` of the Hungarian algorithm (CLRS §25.3). -/
noncomputable def slackMin (P : Problem V) (y : V → ℝ) (S T : Finset V)
    (hS : S.Nonempty) (hT : (P.G.R \ T).Nonempty) : ℝ :=
  ((S.product (P.G.R \ T)).image (fun e : V × V => P.slack y e.1 e.2)).min' (by
    exact Finset.image_nonempty.mpr (Finset.Nonempty.product hS hT))

/-- The minimum slack over `S × (R \ T)` is attained by some edge. -/
lemma slackMin_mem (P : Problem V) (y : V → ℝ) (S T : Finset V)
    (hS : S.Nonempty) (hT : (P.G.R \ T).Nonempty) :
    ∃ e ∈ S.product (P.G.R \ T), P.slack y e.1 e.2 = P.slackMin y S T hS hT := by
  unfold slackMin
  exact Finset.mem_image.mp (Finset.min'_mem _ _)

/-- The minimum slack over `S × (R \ T)` is nonnegative when the potential is
feasible: every slack is nonnegative. -/
lemma slackMin_nonneg (P : Problem V) {y : V → ℝ} (hy : P.Feasible y)
    (S T : Finset V) (hSL : S ⊆ P.G.L) (hTR : T ⊆ P.G.R)
    (hS : S.Nonempty) (hT : (P.G.R \ T).Nonempty) :
    0 ≤ P.slackMin y S T hS hT := by
  rcases P.slackMin_mem y S T hS hT with ⟨e, he, hmin⟩
  have heS : e.1 ∈ S := (Finset.mem_product.mp he).1
  have heRT : e.2 ∈ P.G.R \ T := (Finset.mem_product.mp he).2
  have heR : e.2 ∈ P.G.R := (Finset.mem_sdiff.mp heRT).1
  have heL : e.1 ∈ P.G.L := hSL heS
  have hle : y e.1 + y e.2 ≤ P.w e.1 e.2 := hy e.1 heL e.2 heR
  have h : 0 ≤ P.slack y e.1 e.2 := by
    unfold slack
    linarith
  rwa [← hmin]

/-- The potential-adjustment step of the Hungarian algorithm: with `δ` the
minimum slack over the edges from `S` to `R \ T`, raising `S` and lowering `T`
by `δ` keeps the potential feasible and makes at least one edge from `S` to
`R \ T` tight, so the equality graph gains an edge.  (CLRS §25.3, potential
step.) -/
lemma potential_step (P : Problem V) {y : V → ℝ} {M : Matching V P.G}
    (tree : HungarianTree P y M) (hy : P.Feasible y) :
    let δ := P.slackMin y tree.S tree.T (tree_S_nonempty tree) (tree_R_diff_T_nonempty tree)
    P.Feasible (P.adjustPotential y δ tree.S tree.T) ∧
    ∃ l ∈ tree.S, ∃ r, r ∈ P.G.R ∧ r ∉ tree.T ∧
      P.Tight (P.adjustPotential y δ tree.S tree.T) l r := by
  let δ := P.slackMin y tree.S tree.T (tree_S_nonempty tree) (tree_R_diff_T_nonempty tree)
  have hδ_nonneg : 0 ≤ δ :=
    P.slackMin_nonneg hy tree.S tree.T tree.hS_subset tree.hT_subset
      (tree_S_nonempty tree) (tree_R_diff_T_nonempty tree)
  have hδ_le : ∀ l ∈ tree.S, ∀ r, r ∈ P.G.R → r ∉ tree.T → δ ≤ P.slack y l r := by
    intro l hl r hrR hrT
    have hmem : P.slack y l r ∈
        (tree.S.product (P.G.R \ tree.T)).image (fun e : V × V => P.slack y e.1 e.2) := by
      exact Finset.mem_image.mpr
        ⟨(l, r), Finset.mem_product.mpr ⟨hl, Finset.mem_sdiff.mpr ⟨hrR, hrT⟩⟩, rfl⟩
    change P.slackMin y tree.S tree.T (tree_S_nonempty tree) (tree_R_diff_T_nonempty tree) ≤
      P.slack y l r
    exact Finset.min'_le _ _ hmem
  have hfeas : P.Feasible (P.adjustPotential y δ tree.S tree.T) :=
    P.adjust_preserves_feasible hy hδ_nonneg tree.hS_subset tree.hT_subset hδ_le
  rcases P.slackMin_mem y tree.S tree.T (tree_S_nonempty tree) (tree_R_diff_T_nonempty tree)
    with ⟨e, he, hmin⟩
  have heS : e.1 ∈ tree.S := (Finset.mem_product.mp he).1
  have heRT : e.2 ∈ P.G.R \ tree.T := (Finset.mem_product.mp he).2
  have heR : e.2 ∈ P.G.R := (Finset.mem_sdiff.mp heRT).1
  have heNotT : e.2 ∉ tree.T := (Finset.mem_sdiff.mp heRT).2
  have hslack : P.slack y e.1 e.2 = δ := by
    simpa [δ] using hmin
  exact ⟨hfeas, P.adjust_creates_tight_edge tree.hS_subset tree.hT_subset
    ⟨e.1, heS, e.2, heR, heNotT, hslack⟩⟩

end Problem

end AssignmentProblem

end CLRS
