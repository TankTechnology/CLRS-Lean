import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 24.4. Difference constraints and shortest paths

This section formalizes the connection between systems of difference constraints
and shortest paths (CLRS §24.4).  A *difference constraint* is an inequality of
the form `x_j ≤ x_i + b`.  The system is **feasible** if there exists a real
assignment `x` satisfying every constraint.

The key insight is to build the **constraint graph**: one vertex per variable,
plus a fresh source `s` with a zero-weight edge to every variable vertex, and
an edge `(i, j)` of weight `b` for each constraint `x_j ≤ x_i + b`.  Then

* **Theorem 24.9**: the system is feasible `↔` the constraint graph has no
  negative-weight cycle (`NoNegCycle`).  The forward direction uses a
  potential function; the reverse direction builds an explicit feasible
  assignment from the Bellman-Ford shortest-path distances `δ(s, ·)`.

The section reuses the Chapter 24.1 weighted-graph model wholesale: the
`WeightedGraph` structure, `NoNegCycle`, `IsShortestDist`,
`relaxDist`, and the correctness theorem
`relaxDist_isShortestDist` (CLRS Theorem 24.4).

Main results:

- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem`: a finite set of
  difference constraints `x_j ≤ x_i + b`.
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.IsFeasible`:
  an assignment satisfies every constraint.
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.constraintGraph`:
  the constraint graph built from the system.
- `CLRS.Chapter24.WeightedGraph.le_add_walkWeight_of_potential`: a general
  potential-function lemma used in the forward direction.
- `CLRS.Chapter24.WeightedGraph.relaxDist_respects_edge`: after
  `|V| - 1` rounds, Bellman-Ford estimates satisfy the triangle inequality
  `δ(s, v) ≤ δ(s, u) + w(u, v)`.
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.le_add_walkWeight_some`:
  potential lemma for constraint edges.
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.noNegCycle_of_feasible`:
  feasible assignment `⇒` no negative-weight cycle (Theorem 24.9, forward).
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.feasible_of_noNegCycle`:
  no negative-weight cycle `⇒` feasible assignment via Bellman-Ford
  (Theorem 24.9, reverse).
- `CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.diffConstraint_feasible_iff_noNegCycle`:
  **CLRS Theorem 24.9** — the full equivalence, with explicit Bellman-Ford solution.

Notation conventions used in this section:

- `I` : the variable index type
- `sys` : a `DiffConstraintSystem I`
- `x` : an assignment `I → ℝ`
- `s` (or `none`) : the source vertex of the constraint graph
- `δ` : the single-source shortest-path distance
-/

namespace CLRS
namespace Chapter24

open Finset

namespace WeightedGraph

/-! ## Difference constraint systems -/

/-- A system of difference constraints over variables indexed by `I`.
Each recorded constraint `(i, j) ∈ constraints` demands
`x_j ≤ x_i + b i j`. -/
structure DiffConstraintSystem (I : Type*) [Fintype I] [DecidableEq I] where
  /-- The variable pairs that have a constraint. -/
  constraints : Finset (I × I)
  /-- The bound for each pair: `x_j ≤ x_i + b i j`. -/
  b : I → I → ℝ

namespace DiffConstraintSystem

variable {I : Type*} [Fintype I] [DecidableEq I] (sys : DiffConstraintSystem I)

/-- An assignment `x : I → ℝ` **satisfies** every constraint in the system. -/
def IsFeasible (x : I → ℝ) : Prop :=
  ∀ i j, (i, j) ∈ sys.constraints → x j ≤ x i + sys.b i j

/-- The **constraint graph** of `sys`.  Vertices are `Option I`; the source
`none` has a zero-weight edge to each variable vertex, and each constraint
`(i, j)` contributes a directed edge `(some i) → (some j)` of weight
`sys.b i j`. -/
def constraintGraph : WeightedGraph (Option I) :=
  { edges := (Finset.univ.image fun (i : I) => (none, some i)) ∪
             (sys.constraints.image fun (ij : I × I) => (some ij.1, some ij.2))
  , w := fun u v =>
      match u, v with
      | none, some i => 0
      | some i, some j => if (i, j) ∈ sys.constraints then sys.b i j else 0
      | _, _ => 0
  }

@[simp] theorem mem_edges_source (i : I) : (none, some i) ∈ sys.constraintGraph.edges := by
  dsimp [constraintGraph]
  simp

@[simp] theorem mem_edges_constraint {i j : I} :
    (some i, some j) ∈ sys.constraintGraph.edges ↔ (i, j) ∈ sys.constraints := by
  dsimp [constraintGraph]
  simp

theorem constraintGraph_w_source (i : I) : sys.constraintGraph.w none (some i) = 0 := rfl

theorem constraintGraph_w_constraint (i j : I) :
    sys.constraintGraph.w (some i) (some j) = if (i, j) ∈ sys.constraints then sys.b i j else 0 := rfl

/-- The source vertex `none` has no incoming edges in the constraint graph. -/
lemma no_incoming_to_none (u : Option I) : (u, none) ∉ sys.constraintGraph.edges := by
  dsimp [constraintGraph]
  simp

/-- For a feasible assignment, every constraint edge respects the potential. -/
lemma constraint_edge_potential (hx : sys.IsFeasible x) (i j : I) (hmem : (i, j) ∈ sys.constraints) :
    x j ≤ x i + sys.constraintGraph.w (some i) (some j) := by
  have hx_ij := hx i j hmem
  simp [constraintGraph_w_constraint, hmem]
  exact hx_ij

end DiffConstraintSystem

/-! ## Potential-function lemma -/

/-- **Potential-function lemma.**  Let `f : V → ℝ` be a potential such that
`f v ≤ f u + w u v` for every edge `(u, v)`.  Then for any walk from
`a` to `b`, we have `f b ≤ f a + walkWeight G.w p`. -/
theorem le_add_walkWeight_of_potential {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (f : V → ℝ) (h_edge : ∀ u v, (u, v) ∈ G.edges → f v ≤ f u + G.w u v) (a b : V) (p : List V)
    (hp : G.IsWalkFrom a b p) : f b ≤ f a + walkWeight G.w p := by
  induction p generalizing a b with
  | nil => exfalso; apply hp.ne_nil; rfl
  | cons x xs ih =>
    have ha_x : a = x := by
      have hhead := hp.head
      simp at hhead
      exact hhead.symm
    subst ha_x
    match xs with
    | [] =>
      have hb_a : b = a := by
        have hlast := hp.last
        simp at hlast
        exact hlast.symm
      subst hb_a
      simp
    | y :: ys =>
      have htail_walk : G.IsWalkFrom y b (y :: ys) := by
        have hchain : List.IsChain G.Adj (a :: y :: ys) := hp.chain
        have hchain_tail : List.IsChain G.Adj (y :: ys) := by
          cases hchain with
          | cons_cons _ htail => exact htail
        refine ⟨hchain_tail, by simp, hp.last⟩
      have h_adj : G.Adj a y := by
        have hchain : List.IsChain G.Adj (a :: y :: ys) := hp.chain
        cases hchain with
        | cons_cons h _ => exact h
      have hedge : (a, y) ∈ G.edges := h_adj
      have h_edge_ay := h_edge a y hedge
      have ih_ty := ih y b htail_walk
      calc
        f b ≤ f y + walkWeight G.w (y :: ys) := ih_ty
        _ ≤ (f a + G.w a y) + walkWeight G.w (y :: ys) := by gcongr
        _ = f a + (G.w a y + walkWeight G.w (y :: ys)) := by ring
        _ = f a + walkWeight G.w (a :: y :: ys) := by simp

/-! ## Triangle inequality for Bellman-Ford -/

/-- After `|V| - 1` rounds, the Bellman-Ford shortest-path estimates respect
every edge: `δ(s, v) ≤ δ(s, u) + w(u, v)` (the triangle inequality). -/
theorem relaxDist_respects_edge {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hNC : G.NoNegCycle) (s u v : V) (h_edge : (u, v) ∈ G.edges) :
    G.relaxDist s (Fintype.card V - 1) v ≤
    G.relaxDist s (Fintype.card V - 1) u + (G.w u v : WithTop ℝ) := by
  have hdist_u : G.IsShortestDist s u (G.relaxDist s (Fintype.card V - 1) u) :=
    G.relaxDist_isShortestDist hNC s u
  have hdist_v : G.IsShortestDist s v (G.relaxDist s (Fintype.card V - 1) v) :=
    G.relaxDist_isShortestDist hNC s v
  rcases hdist_u.2 with (hu_top | ⟨p, hp, hpw⟩)
  · -- δ(s, u) = ⊤, so RHS = ⊤, trivial
    simp [hu_top]
  · have hp_ne : p ≠ [] := hp.ne_nil
    have hpv_walk : G.IsWalkFrom s v (p ++ [v]) := by
      refine ⟨?_, ?_, by simp⟩
      · refine List.IsChain.append hp.chain (List.isChain_singleton v) ?_
        intro x hx y hy
        have hx_u : x = u := by
          rw [Option.mem_def, hp.last] at hx
          exact (Option.some.inj hx).symm
        have hy_v : y = v := Eq.symm (by simpa using hy)
        subst hx_u; subst hy_v
        exact h_edge
      · rw [List.head?_append_of_ne_nil _ hp_ne]
        exact hp.head
    have h_walk_weight' : (walkWeight G.w (p ++ [v]) : WithTop ℝ) =
        G.relaxDist s (Fintype.card V - 1) u + (G.w u v : WithTop ℝ) := by
      have h_last : p.getLast hp_ne = u := by
        have hlast := hp.last
        rw [List.getLast?_eq_some_getLast hp_ne] at hlast
        exact Option.some.inj hlast
      have h_ℝ : walkWeight G.w (p ++ [v]) = walkWeight G.w p + G.w u v := by
        rw [walkWeight_append_singleton G.w p hp_ne v, h_last]
      calc
        (walkWeight G.w (p ++ [v]) : WithTop ℝ) = (walkWeight G.w p : WithTop ℝ) + (G.w u v : WithTop ℝ) := by
          simp [h_ℝ]
        _ = G.relaxDist s (Fintype.card V - 1) u + (G.w u v : WithTop ℝ) := by rw [hpw]
    have hle : G.relaxDist s (Fintype.card V - 1) v ≤
        (walkWeight G.w (p ++ [v]) : WithTop ℝ) := hdist_v.1 _ hpv_walk
    calc
      G.relaxDist s (Fintype.card V - 1) v ≤ (walkWeight G.w (p ++ [v]) : WithTop ℝ) := hle
      _ = G.relaxDist s (Fintype.card V - 1) u + (G.w u v : WithTop ℝ) := h_walk_weight'

namespace DiffConstraintSystem

variable {I : Type*} [Fintype I] [DecidableEq I] (sys : DiffConstraintSystem I)

/-- **Potential lemma for constraint edges.** For any walk from `some a` to `some b`
in the constraint graph, we have `x b ≤ x a + walkWeight CG.w c`. -/
lemma le_add_walkWeight_some (hx : sys.IsFeasible x) (a b : I) (c : List (Option I))
    (hp : (sys.constraintGraph).IsWalkFrom (some a) (some b) c) :
    x b ≤ x a + walkWeight (sys.constraintGraph).w c := by
  induction c generalizing a b with
  | nil => exfalso; apply hp.ne_nil; rfl
  | cons z zs ih =>
    have hz_some : z = some a := by simpa using hp.head
    subst hz_some
    match zs with
    | [] =>
      have hb_a : b = a := by
        have hl := hp.last
        simp at hl
        have h_some_inj : some a = some b := by simpa using hl
        injection h_some_inj with h_eq
        exact h_eq.symm
      subst hb_a; simp
    | y :: ys =>
      -- Show y = some j for some j
      have hy_some : ∃ j : I, y = some j := by
        have h_adj : (sys.constraintGraph).Adj (some a) y := by
          have hchain : List.IsChain (sys.constraintGraph).Adj ((some a) :: y :: ys) := hp.chain
          cases hchain with
          | cons_cons hadj _ => exact hadj
        rcases y with (y | y)
        · exfalso
          -- y = none, but there's no edge from some a to none by constraint graph construction
          dsimp [Adj] at h_adj
          apply sys.no_incoming_to_none (some a)
          exact h_adj
        · exact ⟨y, rfl⟩
      rcases hy_some with ⟨j, hyj⟩
      subst hyj
      have hedge : ((some a, some j) : Option I × Option I) ∈ (sys.constraintGraph).edges := by
        have h_adj : (sys.constraintGraph).Adj (some a) (some j) := by
          have hchain : List.IsChain (sys.constraintGraph).Adj ((some a) :: (some j) :: ys) := hp.chain
          cases hchain with
          | cons_cons hadj _ => exact hadj
        exact h_adj
      have hm : (a, j) ∈ sys.constraints := by
        dsimp [constraintGraph] at hedge; simpa using hedge
      have hx_ineq : x j ≤ x a + sys.b a j := hx a j hm
      have htail_walk : (sys.constraintGraph).IsWalkFrom (some j) (some b) ((some j) :: ys) := by
        have htail_chain : List.IsChain (sys.constraintGraph).Adj ((some j) :: ys) := by
          have hchain : List.IsChain (sys.constraintGraph).Adj ((some a) :: (some j) :: ys) := hp.chain
          cases hchain with
          | cons_cons _ htail => exact htail
        refine ⟨htail_chain, by simp, ?_⟩
        simpa using hp.last
      have ih_tail : x b ≤ x j + walkWeight (sys.constraintGraph).w ((some j) :: ys) :=
        ih j b htail_walk
      have hw_constraint : (sys.constraintGraph).w (some a) (some j) = sys.b a j := by
        simp [constraintGraph_w_constraint, hm]
      calc
        x b ≤ x j + walkWeight (sys.constraintGraph).w ((some j) :: ys) := ih_tail
        _ ≤ (x a + sys.b a j) + walkWeight (sys.constraintGraph).w ((some j) :: ys) := by gcongr
        _ = x a + (sys.b a j + walkWeight (sys.constraintGraph).w ((some j) :: ys)) := by ring
        _ = x a + walkWeight (sys.constraintGraph).w ((some a) :: (some j) :: ys) := by
          simp [hw_constraint]

/-- **Feasible → no negative cycle.**  If the system has a feasible assignment,
then the constraint graph has no negative-weight cycle (Theorem 24.9, forward). -/
theorem noNegCycle_of_feasible (hx : sys.IsFeasible x) :
    sys.constraintGraph.NoNegCycle := by
  set CG := sys.constraintGraph with hCG
  intro v c hwalk
  rcases v with (v | v)
  · -- v = none: the only closed walk from none is [none] (weight 0)
    -- because there are no edges entering none
    have hc_singleton : c = [none] := by
      by_contra! h
      -- h : c ≠ [none]
      have hne : c ≠ [] := hwalk.ne_nil
      -- Determine length: if length = 1 then c = [none]; if length ≥ 2 then impossible
      by_cases hlen1 : c.length = 1
      · -- c.length = 1, so c = [c.head ...] = [none]
        have hhead_val : c.head hne = none := by
          have hh := hwalk.head
          -- hh : c.head? = some none  →  ∃ ys, c = none :: ys
          rcases List.head?_eq_some_iff.mp hh with ⟨ys, hc_eq⟩
          simp [hc_eq]
        rcases c with (_ | ⟨x, xs⟩)
        · exact hne rfl
        · have hxs_empty : xs = [] := by
            cases xs with
            | nil => rfl
            | cons y ys =>
              have : (x :: y :: ys).length ≥ 2 := by simp
              have hlen1' : (x :: y :: ys).length = 1 := hlen1
              omega
          subst hxs_empty
          have hx : x = none := hhead_val
          subst hx; exfalso; exact h rfl
      · -- c.length ≠ 1, so c.length ≥ 2 (since c ≠ [])
        have hlen_gt_1 : c.length ≥ 2 := by
          have hpos : c.length ≥ 1 := by
            have hpos' : c.length > 0 := by
              apply Nat.pos_of_ne_zero
              intro hzero
              apply hne
              simpa using hzero
            omega
          have hneq1 : c.length ≠ 1 := hlen1
          omega
        -- Since c has at least 2 elements, destruct it
        rcases c with (_ | ⟨a, r⟩)
        · exact hne rfl
        · rcases r with (_ | ⟨b, tl⟩)
          · -- c = [a]; with length ≥ 2, impossible
            have : (a :: []).length ≥ 2 := hlen_gt_1
            simp at this
          · -- c = a :: b :: tl
            have ha_none : a = none := by
              have hh := hwalk.head
              simpa using hh
            subst ha_none
            -- c = none :: b :: tl, ends with none
            have hne_nbtl : (none :: b :: tl) ≠ [] := by simp
            have hlast_val : List.getLast (none :: b :: tl) hne_nbtl = none := by
              have hlast' := hwalk.last
              rw [List.getLast?_eq_some_getLast hne_nbtl] at hlast'
              exact Option.some.inj hlast'
            have hsplit : (none :: b :: tl) = ((none :: b :: tl).dropLast) ++ [none] := by
              conv_lhs => rw [← List.dropLast_append_getLast hne_nbtl, hlast_val]
            have hchain' : List.IsChain CG.Adj (((none :: b :: tl).dropLast) ++ [none]) := by
              rw [← hsplit]; exact hwalk.chain
            have happ := List.isChain_append.1 hchain'
            have hlen_gt_1' : (none :: b :: tl).length ≥ 2 := by
              simp
            have hdrop_ne : (none :: b :: tl).dropLast ≠ [] := by
              intro hdrop
              have hlen1 : (none :: b :: tl).length = 1 := by
                have hlen_eq : (none :: b :: tl).length = ((none :: b :: tl).dropLast).length + 1 := by
                  rw [hsplit]; simp
                rw [hlen_eq, hdrop]; simp
              omega
            have hu_mem : List.getLast ((none :: b :: tl).dropLast) hdrop_ne ∈ ((none :: b :: tl).dropLast).getLast? := by
              rw [List.getLast?_eq_some_getLast hdrop_ne]
              simp
            have h_penultimate_edge : CG.Adj (List.getLast ((none :: b :: tl).dropLast) hdrop_ne) none :=
              happ.2.2 (List.getLast ((none :: b :: tl).dropLast) hdrop_ne) hu_mem none (by simp)
            have h_edge : (List.getLast ((none :: b :: tl).dropLast) hdrop_ne, none) ∈ CG.edges := h_penultimate_edge
            exact sys.no_incoming_to_none (List.getLast ((none :: b :: tl).dropLast) hdrop_ne) h_edge
    subst hc_singleton; simp
  · -- v = some i: apply the potential lemma for constraint edges
    have := sys.le_add_walkWeight_some hx v v c hwalk
    linarith

/-- **No negative cycle → feasible.**  If the constraint graph has no negative
cycle, then the Bellman-Ford shortest-path distances `δ(none, some i)` give
an explicit feasible assignment (Theorem 24.9, reverse). -/
theorem feasible_of_noNegCycle (hNC : sys.constraintGraph.NoNegCycle) :
    ∃ x : I → ℝ, sys.IsFeasible x := by
  set CG := sys.constraintGraph with hCG
  have hcard : 1 ≤ Fintype.card (Option I) :=
    Fintype.card_pos_iff.mpr ⟨none⟩
  -- Bellman-Ford shortest distances from the source
  let d : Option I → WithTop ℝ := CG.relaxDist none (Fintype.card (Option I) - 1)
  have hdist : ∀ (v : Option I), CG.IsShortestDist none v (d v) :=
    fun v => CG.relaxDist_isShortestDist hNC none v

  -- Each d (some i) is finite because there is a zero-weight walk from none to some i
  have hfinite (i : I) : d (some i) ≠ ⊤ := by
    have hzero_walk : CG.IsWalkFrom none (some i) [none, some i] := by
      have hadj : CG.Adj none (some i) := by
        dsimp [CG, constraintGraph, Adj]; simp
      have hchain : List.IsChain CG.Adj [none, some i] :=
        List.IsChain.cons (List.isChain_singleton (some i)) (by
          intro y hy
          have hy_eq : some i = y := by simpa using hy
          rw [← hy_eq]
          exact hadj)
      refine ⟨hchain, by simp, by simp⟩
    have hle : d (some i) ≤ (0 : WithTop ℝ) := by
      have := (hdist (some i)).1 _ hzero_walk
      have hweight : walkWeight CG.w [none, some i] = 0 := by
        calc
          walkWeight CG.w [none, some i] = CG.w none (some i) := by simp
          _ = 0 := sys.constraintGraph_w_source i
      simpa [hweight] using this
    intro htop
    have : (⊤ : WithTop ℝ) ≤ (0 : WithTop ℝ) := by rw [← htop]; exact hle
    simp at this

  have hfinite' (i : I) : ∃ r : ℝ, d (some i) = (r : WithTop ℝ) := by
    have hi : d (some i) ≠ (none : Option ℝ) := hfinite i
    rcases (Option.ne_none_iff_exists.mp hi) with ⟨r, hr⟩
    exact ⟨r, hr.symm⟩
  choose x hx using hfinite'

  refine ⟨x, ?_⟩
  intro i j hij
  have hedge : (some i, some j) ∈ CG.edges := by
    dsimp [CG, constraintGraph]
    simp [hij]
  have htri : d (some j) ≤ d (some i) + (CG.w (some i) (some j) : WithTop ℝ) :=
    CG.relaxDist_respects_edge hNC none (some i) (some j) hedge
  have hw : CG.w (some i) (some j) = sys.b i j := by
    dsimp [CG, constraintGraph]
    simp [hij]
  rw [hw] at htri
  rw [hx i, hx j] at htri
  -- htri: (x j : WithTop ℝ) ≤ (x i : WithTop ℝ) + (sys.b i j : WithTop ℝ)
  have htri' : (x j : WithTop ℝ) ≤ (x i + sys.b i j : WithTop ℝ) := by
    simpa [WithTop.coe_add] using htri
  exact WithTop.coe_le_coe.mp htri'

/-- **CLRS Theorem 24.9 (difference constraints and shortest paths).**
A system of difference constraints is feasible iff its constraint graph has no
negative-weight cycle.  When feasible, the Bellman-Ford shortest-path distances
from the source give an explicit solution `x i = δ(s, i)`. -/
theorem diffConstraint_feasible_iff_noNegCycle :
    (∃ x : I → ℝ, sys.IsFeasible x) ↔ sys.constraintGraph.NoNegCycle := by
  constructor
  · rintro ⟨x, hx⟩
    exact sys.noNegCycle_of_feasible hx
  · intro hNC
    rcases sys.feasible_of_noNegCycle hNC with ⟨x, hx⟩
    exact ⟨x, hx⟩

end DiffConstraintSystem
end WeightedGraph
end Chapter24
end CLRS
