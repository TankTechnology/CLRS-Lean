import Mathlib

/-!
# 35.2 The Traveling-Salesperson Problem

This section formalizes the traveling-salesperson problem and the factor-two
approximation algorithm **APPROX-TSP-TOUR** from CLRS §35.2.  Given a complete
undirected graph on a vertex set `V` with a nonnegative weight function `w`
satisfying the triangle inequality, a *tour* is a Hamiltonian cycle — a cyclic
permutation visiting every vertex exactly once — and the problem is to find a
tour of minimum total weight.  Computing an optimal tour is NP-hard, but
APPROX-TSP-TOUR always finds a tour within a factor of two of the optimum by
building a minimum spanning tree, walking it depth-first, and shortcutting the
walk to a cycle.

We model the MST as a rooted tree given by a total parent map `p : V → V` with
root `r` (every vertex reaches `r` by iterating `p`), matching the total-function
convention of the repository.  A tour is a cyclic permutation `σ : V → V` (a
bijection whose iterates reach every vertex).

Main results:

- Definition `TreeOn`: a rooted tree as a parent map together with its root.
- Definition `treeCost`: the total weight of a rooted tree's edges.
- Definition `IsMinimumSpanningTreeOn`: a rooted tree of minimum cost.
- Definition `Tour`: a tour as a cyclic permutation of the vertices.
- Definition `TourCost`: the total weight of a tour.
- Definition `subtree`, `children`, `subtreeCost`: the tree substructure used by
  the depth-first walk.
- Definition `dfsWalk`: the depth-first walk of a rooted tree, which traverses
  every tree edge exactly twice.
- Definition `dfsTour`: the preorder (depth-first) ordering of the vertices.
- Lemma `mst_le_tour` (Lemma 35.3): a minimum spanning tree costs no more than
  any tour, because deleting one edge from a tour leaves a spanning tree.
- Lemma `dfsWalk_cost` (Lemma 35.2): the depth-first walk of a rooted tree has
  cost exactly twice the tree's cost.
- Lemma `dfsTour_bound`: the tour obtained by shortcutting the depth-first walk
  costs no more than the walk itself (triangle inequality).
- Lemma `dfsTour_isTour`: the depth-first ordering of a spanning tree visits
  every vertex exactly once, so it is a tour.
- Theorem `tsp_two_approx` (Theorem 35.2): APPROX-TSP-TOUR returns a tour of
  cost at most twice the cost of any tour — in particular, of an optimal one.

Notation conventions used in this section:

- `V` : the vertex type
- `w` : a weight function `V → V → Nat` on the complete graph
- `p` : a parent map (total function) giving a rooted tree
- `r` : the root of a rooted tree
- `σ` : a tour, a cyclic permutation of the vertices
- `v₀` : the vertex whose tour edge is deleted to obtain a spanning tree
- `c` : a child of `v` (a vertex with `p c = v` and `c ≠ r`)
-/

noncomputable section

namespace CLRS

namespace TSP

variable {V : Type} [DecidableEq V] [Fintype V]

/--
A **weighted complete graph** on the vertex type `V`: a weight for every
(ordered) pair of vertices.  This is the CLRS §35.2 model, where the underlying
graph is complete and only the weight function is specified.  We use `Nat`
weights (as in the repository's minimum-spanning-tree sections); the triangle
inequality and the vanishing of loop weights are hypotheses of the theorems
that need them.
-/
abbrev Graph (V : Type) := V → V → Nat

/--
The cost of the *path* through the vertex list `π`: the sum of the weights of
consecutive pairs.
-/
def pathCost (w : Graph V) (π : List V) : Nat :=
  ((π.zip π.tail).map (fun e : V × V => w e.1 e.2)).sum

/-- The cost of the walk given by the vertex list `π`.  Synonymous with
`pathCost`; kept as a separate name because the depth-first walk is the primary
object of study here. -/
def walkCost (w : Graph V) (π : List V) : Nat :=
  pathCost w π

/--
The cost of the tour obtained by traversing the path `π` and then returning
from its last vertex to `target`.  For a Hamiltonian path `π` of the whole
vertex set with `target` equal to `π`'s first vertex, this is the cost of the
corresponding Hamiltonian cycle.
-/
def tourCostTo (w : Graph V) (target : V) (π : List V) : Nat :=
  pathCost w π + (if h : π = [] then 0 else w (π.getLast h) target)

/--
A **rooted tree** on the vertex type: a parent map `p : V → V` together with a
root `r` fixed by `p`, such that every vertex reaches the root by iterating `p`.
The edge set of the tree is `{(v, p v) | v ≠ r}`.  This total-function model is
acyclic by construction: a non-root vertex on a cycle of `p` could never reach
the root.  CLRS §35.2's APPROX-TSP-TOUR uses a minimum spanning tree of the
complete graph; we model any such tree this way.
-/
structure TreeOn (p : V → V) (r : V) : Prop where
  root_fixed : p r = r
  reaches_root : ∀ v : V, ∃ n : Nat, p^[n] v = r

/--
The **tree cost** of a rooted tree: the sum of the weights `w v (p v)` of the
edges from non-root vertices to their parents.  The edge into the root has no
parent-edge and is not counted.
-/
def treeCost (w : Graph V) (p : V → V) (r : V) : Nat :=
  (Finset.univ.erase r).sum (fun v : V => w v (p v))

/--
A **minimum spanning tree** of the complete graph: a rooted tree whose cost is
no larger than that of any other rooted tree.
-/
def IsMinimumSpanningTreeOn (w : Graph V) (p : V → V) (r : V) : Prop :=
  TreeOn p r ∧ ∀ (p' : V → V) (r' : V), TreeOn p' r' → treeCost w p r ≤ treeCost w p' r'

/--
A **tour**: a cyclic permutation of the vertices — a bijection `σ` whose
iterates reach every vertex, so `σ` is a single cycle visiting all of `V`.
This is the Hamiltonian cycle model of CLRS §35.2.
-/
structure Tour (σ : V → V) : Prop where
  bijective : Function.Bijective σ
  reachable : ∀ u v : V, ∃ n : Nat, σ^[n] u = v

/--
The **cost of a tour** `σ`: the sum over `v` of the weight of the edge from
`v` to `σ v`.  For a cyclic permutation on `V`, this counts each of the `|V|`
tour edges exactly once.
-/
def TourCost (w : Graph V) (σ : V → V) : Nat :=
  (Finset.univ.sum fun v : V => w v (σ v))

namespace TreeOn

variable {p : V → V} {r : V}

/--
The **depth** of `v` in a rooted tree: the least `n` with `p^[n] v = r` (and `0`
if `v` never reaches `r`, a junk value under the total-function convention).
-/
noncomputable def depth (p : V → V) (r : V) (v : V) : Nat := by
  classical
  exact if h : ∃ n : Nat, p^[n] v = r then Nat.find h else 0

lemma depth_spec (hT : TreeOn p r) (v : V) : p^[depth p r v] v = r := by
  classical
  unfold depth
  rw [dif_pos (hT.reaches_root v)]
  exact Nat.find_spec (hT.reaches_root v)

lemma depth_min (hT : TreeOn p r) (v : V) {m : Nat} (hm : m < depth p r v) : p^[m] v ≠ r := by
  classical
  unfold depth at hm
  rw [dif_pos (hT.reaches_root v)] at hm
  exact Nat.find_min (hT.reaches_root v) hm

lemma depth_le_of_iterate (hT : TreeOn p r) (v : V) {m : Nat} (hm : p^[m] v = r) :
    depth p r v ≤ m := by
  by_contra h
  exact hT.depth_min v (Nat.lt_of_not_ge h) hm

/-- Iterating `p` at the root stays at the root. -/
lemma iterate_root (hT : TreeOn p r) (k : Nat) : p^[k] r = r := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply, ih, hT.root_fixed]

/-- The distinct iterates of `v` before it reaches the root: `p^[i] v ≠ p^[j] v`
whenever `i < j ≤ depth`. -/
lemma iterates_ne_of_lt (hT : TreeOn p r) (v : V) {i j : Nat} (hij : i < j)
    (hj : j ≤ depth p r v) : p^[i] v ≠ p^[j] v := by
  intro heq
  have hmod : p^[depth p r v - j + i] v = r := by
    calc
      p^[depth p r v - j + i] v = p^[depth p r v - j] (p^[i] v) := by
        rw [show depth p r v = (depth p r v - j) + j by omega]
        simpa [Function.iterate_add]
      _ = p^[depth p r v - j] (p^[j] v) := by rw [heq]
      _ = p^[depth p r v] v := by
        calc
          p^[depth p r v - j] (p^[j] v) = p^[(depth p r v - j) + j] v := by
            simpa [Function.iterate_add]
          _ = p^[depth p r v] v := by
            congr 1
            omega
      _ = r := hT.depth_spec v
  have hlt : depth p r v - j + i < depth p r v := by omega
  exact hT.depth_min v hlt hmod

/-- `depth` is bounded by the number of vertices, since the iterates up to the
root are all distinct. -/
lemma depth_le_card (hT : TreeOn p r) (v : V) : depth p r v ≤ Fintype.card V := by
  classical
  have hinj : Function.Injective (fun k : Fin (depth p r v + 1) => p^[k.1] v) := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    have h : a.1 < b.1 ∨ b.1 < a.1 := lt_or_gt_of_ne hne
    rcases h with hlt | hlt
    · exact False.elim (hT.iterates_ne_of_lt v hlt (Nat.le_of_lt_succ (Fin.isLt b)) hab)
    · exact False.elim (hT.iterates_ne_of_lt v hlt (Nat.le_of_lt_succ (Fin.isLt a)) hab.symm)
  have hcard : Fintype.card (Fin (depth p r v + 1)) ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun k : Fin (depth p r v + 1) => p^[k.1] v) hinj
  have hcard' : depth p r v + 1 ≤ Fintype.card V := by simpa using hcard
  omega

lemma depth_ne_zero (hT : TreeOn p r) (v : V) (hv : v ≠ r) : depth p r v ≠ 0 := by
  intro h0
  have hs := hT.depth_spec v
  have : v = r := by simpa [h0] using hs
  exact hv this

/-- Moving from `v` to its parent decreases the depth by one. -/
lemma depth_succ (hT : TreeOn p r) (v : V) (hv : v ≠ r) : depth p r (p v) + 1 = depth p r v := by
  have hd : depth p r v ≠ 0 := hT.depth_ne_zero v hv
  apply Nat.le_antisymm
  · have h1 : p^[depth p r v - 1] (p v) = r := by
      have hd' := hT.depth_spec v
      rw [show depth p r v = (depth p r v - 1) + 1 by omega] at hd'
      simpa [Function.iterate_add] using hd'
    have hle : depth p r (p v) ≤ depth p r v - 1 := hT.depth_le_of_iterate (p v) h1
    omega
  · have h2 : p^[depth p r (p v) + 1] v = r := by
      have hd' := hT.depth_spec (p v)
      simpa [Function.iterate_add] using hd'
    exact hT.depth_le_of_iterate v h2

/-- A child lies exactly one level below its parent. -/
lemma depth_child_succ (hT : TreeOn p r) {c v : V} (hpc : p c = v) (hcne : c ≠ r) :
    depth p r c = depth p r v + 1 := by
  calc
    depth p r c = depth p r (p c) + 1 := (hT.depth_succ c hcne).symm
    _ = depth p r v + 1 := by rw [hpc]

/-- Applying `p` `k` times (at most `depth`) lowers the depth by `k`. -/
lemma depth_iterate (hT : TreeOn p r) (v : V) : ∀ k : Nat, k ≤ depth p r v →
    depth p r (p^[k] v) = depth p r v - k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ depth p r v := by omega
      have hkd := ih hk'
      have hne : p^[k] v ≠ r := hT.depth_min v (by omega)
      have hs : depth p r (p (p^[k] v)) + 1 = depth p r (p^[k] v) := hT.depth_succ (p^[k] v) hne
      calc
        depth p r (p^[k + 1] v) = depth p r (p (p^[k] v)) := by
          rw [Function.iterate_succ_apply']
        _ = depth p r (p^[k] v) - 1 := by
          have hne0 : depth p r (p^[k] v) ≠ 0 := hT.depth_ne_zero (p^[k] v) hne
          omega
        _ = (depth p r v - k) - 1 := by rw [hkd]
        _ = depth p r v - (k + 1) := by omega

/-- If the `i`-th iterate of `u` is a non-root vertex, then `i` does not pass
`u`'s depth. -/
lemma iterate_le_depth_of_ne_root (hT : TreeOn p r) {u : V} {i : Nat} {x : V}
    (hu : p^[i] u = x) (hx : x ≠ r) : i ≤ depth p r u := by
  by_contra h
  have hgt : depth p r u < i := Nat.lt_of_not_ge h
  have hcalc : p^[i] u = r := by
    calc
      p^[i] u = p^[i - depth p r u] (p^[depth p r u] u) := by
        calc
          p^[i] u = p^[(i - depth p r u) + depth p r u] u := by
            congr 1
            omega
          _ = p^[i - depth p r u] (p^[depth p r u] u) := by
            simpa [Function.iterate_add]
      _ = p^[i - depth p r u] r := by rw [hT.depth_spec u]
      _ = r := hT.iterate_root (i - depth p r u)
  rw [hu] at hcalc
  exact hx hcalc

end TreeOn

end TSP

end CLRS
