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
def pathCost (w : Graph V) : List V → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => w a b + pathCost w (b :: rest)

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

/-- `getLast` is proof-irrelevant: the last element of a nonempty list does not
depend on the nonemptiness proof. -/
lemma getLast_irrel {l : List V} (h1 : l ≠ []) (h2 : l ≠ []) : l.getLast h1 = l.getLast h2 := by
  cases l with
  | nil => simp at h1
  | cons a t =>
      cases t with
      | nil => rfl
      | cons b t' => rfl

/-- The last element of `a :: l` is the last element of `l` (any proof works). -/
lemma getLast_cons_any {a : V} {l : List V} (h : l ≠ []) (h' : a :: l ≠ []) :
    (a :: l).getLast h' = l.getLast h := by
  cases l with
  | nil => simp at h
  | cons b t =>
      cases t with
      | nil => rfl
      | cons c t' => rfl

/-- The last element of `l₁ ++ l₂` (both nonempty) is the last element of `l₂`. -/
lemma getLast_append_of_right_ne_nil' (l1 l2 : List V) (hne : l1 ++ l2 ≠ []) (h2 : l2 ≠ []) :
    (l1 ++ l2).getLast hne = l2.getLast h2 := by
  induction l1 with
  | nil => rfl
  | cons a t ih =>
      by_cases htl : t ++ l2 = []
      · have ht : t = [] := by simpa using (List.append_eq_nil_iff.mp htl).1
        have hl2 : l2 = [] := by simpa using (List.append_eq_nil_iff.mp htl).2
        subst ht
        subst hl2
        simp at h2
      · change (a :: (t ++ l2)).getLast hne = l2.getLast h2
        have hcons : (a :: (t ++ l2)).getLast hne = (t ++ l2).getLast htl :=
          getLast_cons_any htl hne
        rw [hcons]
        exact ih htl

/-- The last element of `l ++ [a]` is `a`. -/
lemma getLast_append_singleton' {a : V} (l : List V) (h : l ++ [a] ≠ []) :
    (l ++ [a]).getLast h = a := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      by_cases htl : t ++ [a] = []
      · simp at htl
      · change (b :: (t ++ [a])).getLast h = a
        have hcons : (b :: (t ++ [a])).getLast h = (t ++ [a]).getLast htl :=
          getLast_cons_any htl h
        rw [hcons]
        exact ih htl

/-- `head` through an equality of the lists (proof args differ). -/
lemma head_eq_of_eq {l l' : List V} (hl : l = l') (hne : l ≠ []) (hne' : l' ≠ []) :
    l.head hne = l'.head hne' := by
  cases l' with
  | nil => simp at hne'
  | cons b t =>
      subst l
      rfl

/-- `getLast` through an equality of the lists (proof args differ). -/
lemma getLast_eq_of_eq {l l' : List V} (hl : l = l') (hne : l ≠ []) (hne' : l' ≠ []) :
    l.getLast hne = l'.getLast hne' := by
  cases l' with
  | nil => simp at hne'
  | cons b t =>
      subst l
      cases t with
      | nil => rfl
      | cons c t' => rfl

/-- The head of `l ++ l₂` with `l` nonempty is the head of `l`. -/
lemma head_append_of_left_ne_nil' {l l2 : List V} (h : l ≠ []) (h' : l ++ l2 ≠ []) :
    (l ++ l2).head h' = l.head h := by
  cases l with
  | nil => simp at h
  | cons b t => rfl

/-- The cost of the empty path is zero. -/
lemma pathCost_nil (w : Graph V) : pathCost w [] = 0 := by
  rfl

/-- The cost of a path starting with `v` decomposes as the first edge plus the
rest of the path. -/
lemma pathCost_cons_nonempty (w : Graph V) (v : V) {cs : List V} (h : cs ≠ []) :
    pathCost w (v :: cs) = w v (cs.head h) + pathCost w cs := by
  cases cs with
  | nil => simp at h
  | cons a rest => rfl

/-- The cost of a concatenation of two nonempty paths: the sum of the parts plus
the edge joining them. -/
lemma pathCost_append_nonempty (w : Graph V) {l1 l2 : List V} (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    pathCost w (l1 ++ l2) = pathCost w l1 + pathCost w l2 + w (l1.getLast h1) (l2.head h2) := by
  induction l1 with
  | nil => simp at h1
  | cons v t ih =>
      cases t with
      | nil =>
          change pathCost w (v :: l2) = pathCost w [v] + pathCost w l2 + w ([v].getLast h1) (l2.head h2)
          rw [pathCost_cons_nonempty w v h2]
          simp
          ac_rfl
      | cons a t' =>
          have ht : a :: t' ≠ [] := by simp
          have hrest : (a :: t') ++ l2 ≠ [] := by simp [ht]
          rw [List.cons_append]
          rw [pathCost_cons_nonempty w v hrest]
          rw [pathCost_cons_nonempty w v ht]
          rw [ih ht]
          have hhead : ((a :: t') ++ l2).head hrest = (a :: t').head ht := by
            simp
          rw [hhead]
          rw [getLast_cons_any ht h1]
          omega

/-- A Finset sum equals the sum over its `toList`. -/
lemma finset_sum_toList {α : Type} (s : Finset α) (f : α → Nat) :
    (s.toList.map f).sum = s.sum f := by
  simp

/-- A Finset sum equals the sum over the list of its attached elements. -/
lemma finset_sum_attach_toList {α : Type} [DecidableEq α] (s : Finset α) (f : α → Nat) :
    (s.attach.toList.map (fun x : {a : α // a ∈ s} => f x.1)).sum = s.sum f := by
  calc
    (s.attach.toList.map (fun x : {a : α // a ∈ s} => f x.1)).sum
      = s.attach.sum (fun x : {a : α // a ∈ s} => f x.1) := by
        exact finset_sum_toList s.attach (fun x : {a : α // a ∈ s} => f x.1)
    _ = s.sum f := by rw [Finset.sum_attach]

/-- Congruence for list sums of `Nat`-valued functions. -/
lemma sum_map_congr {α : Type} {f g : α → Nat} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have hda : f a = g a := h a (by simp)
      have ih' : (t.map f).sum = (t.map g).sum := ih (fun b hb => h b (by simp [hb]))
      simp [List.sum_cons, hda, ih']

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

/-- The **children** of `v` in the rooted tree: the non-root vertices whose
parent is `v`. -/
def children (p : V → V) (r : V) (v : V) : Finset V :=
  Finset.univ.filter (fun c => c ≠ r ∧ p c = v)

/-- The **subtree** rooted at `v`: every vertex whose parent chain passes through
`v` (equivalently, that reaches `v` by iterating `p`). -/
def subtree (p : V → V) (r : V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ k : Nat, p^[k] x = v)

/-- The cost of the subtree rooted at `v`: the sum of the weights of the tree
edges with both endpoints in the subtree (each non-root vertex's edge to its
parent). -/
def subtreeCost (w : Graph V) (p : V → V) (r : V) (v : V) : Nat :=
  (subtree p r v).sum (fun x => w x (p x))

/--
The spanning tree obtained by deleting the edge `(r, σ r)` from a tour `σ`: the
root `r` is fixed, and every other vertex points to its tour successor.  Because
`σ` is a single cycle through all of `V`, iterating this parent map from any
vertex reaches `r`.
-/
def deleteTourEdge (σ : V → V) (r : V) (v : V) : V :=
  if v = r then r else σ v

/-- Deleting one edge from a tour leaves a spanning tree: `deleteTourEdge σ r`
is a rooted tree on `V`. -/
theorem deleteTourEdge_tree {σ : V → V} {r : V} (hT : Tour σ) :
    TreeOn (deleteTourEdge σ r) r := by
  refine ⟨?root_fixed, ?reaches_root⟩
  · simp [deleteTourEdge]
  · intro x
    by_cases hxr : x = r
    · subst hxr
      exact ⟨0, rfl⟩
    · let m := Nat.find (hT.reachable x r)
      have hmspec : σ^[m] x = r := Nat.find_spec (hT.reachable x r)
      have hmin : ∀ k : Nat, k < m → σ^[k] x ≠ r :=
        fun k hk => Nat.find_min (hT.reachable x r) hk
      have hiter : ∀ k : Nat, k ≤ m → (deleteTourEdge σ r)^[k] x = σ^[k] x := by
        intro k
        induction k with
        | zero => intro hk; simp
        | succ k ih =>
            intro hks
            have hk_lt : k < m := by omega
            have hne : σ^[k] x ≠ r := hmin k hk_lt
            have ih' : (deleteTourEdge σ r)^[k] x = σ^[k] x := ih (by omega)
            calc
              (deleteTourEdge σ r)^[k + 1] x = deleteTourEdge σ r ((deleteTourEdge σ r)^[k] x) := by
                rw [Function.iterate_succ_apply']
              _ = deleteTourEdge σ r (σ^[k] x) := by rw [ih']
              _ = σ (σ^[k] x) := by
                simp [deleteTourEdge, hne]
              _ = σ^[k + 1] x := by
                rw [Function.iterate_succ_apply']
      exact ⟨m, by rw [hiter m (le_rfl)]; exact hmspec⟩

/--
**Lemma 35.3.**  A minimum spanning tree costs no more than any tour.

Indeed, deleting one edge from a tour leaves a spanning tree whose cost is at
most the tour's (the deleted edge contributes a nonnegative amount), and the
MST is minimal among all spanning trees.
-/
theorem mst_le_tour {w : Graph V} {p : V → V} {r : V}
    (hMST : IsMinimumSpanningTreeOn w p r) {σ : V → V} (hT : Tour σ) :
    treeCost w p r ≤ TourCost w σ := by
  let d : V → V := deleteTourEdge σ r
  have hTree : TreeOn d r := deleteTourEdge_tree hT
  have hle : treeCost w d r ≤ TourCost w σ := by
    unfold treeCost TourCost
    rw [show (Finset.univ.erase r).sum (fun x : V => w x (d x)) =
        (Finset.univ.erase r).sum (fun x : V => w x (σ x)) by
      apply Finset.sum_congr
      · simp
      · intro x hx
        have hxne : x ≠ r := (Finset.mem_erase.mp hx).1
        simp [d, deleteTourEdge, hxne]]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; exact Finset.mem_univ x)
      (by intro x hx1 hx2; exact Nat.zero_le _)
  exact le_trans (hMST.2 d r hTree) hle

namespace TreeOn

variable {p : V → V} {r : V}

/-- A child lies strictly deeper than its parent, so the "remaining budget"
`card V - depth` strictly decreases when recursing from a parent to a child.
This is the termination measure for the depth-first walk and preorder
definitions. -/
lemma children_depth_lt (hT : TreeOn p r) {c v : V} (hc : c ∈ children p r v) :
    Fintype.card V - depth p r c < Fintype.card V - depth p r v := by
  classical
  rcases Finset.mem_filter.mp hc with ⟨_, hcpc⟩
  rcases hcpc with ⟨hcne, hpc⟩
  have hdepth : depth p r c = depth p r v + 1 := hT.depth_child_succ hpc hcne
  have hlt_card : depth p r v < Fintype.card V := by
    by_contra h
    have hge : Fintype.card V ≤ depth p r v := Nat.le_of_not_gt h
    have heq : depth p r v = Fintype.card V := le_antisymm (hT.depth_le_card v) hge
    have hc_card : depth p r c ≤ Fintype.card V := hT.depth_le_card c
    omega
  omega

/--
The **depth-first walk** of the tree starting and ending at `v`, covering the
subtree rooted at `v`: `v`, then for each child `c` the walk of `c`'s subtree
followed by the return edge to `v`.  Every tree edge in the subtree is
traversed exactly twice (once down, once up).

The recursion is carried out with `WellFounded.fix` on the measure
`card V - depth`, threading each child's membership proof through the
`attach`ed children so the well-founded induction hypothesis is applicable.
-/
noncomputable def dfsWalkFrom (hT : TreeOn p r) : (v : V) → List V := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  exact hwf.fix (C := fun _ => List V) (fun v ih =>
    [v] ++ ((children p r v).attach.toList.flatMap (fun xc => ih xc.1 (children_depth_lt hT xc.2) ++ [v])))

/-- The depth-first walk of the whole tree, starting and ending at the root. -/
noncomputable def dfsWalk (hT : TreeOn p r) : List V :=
  dfsWalkFrom hT r

/--
The **preorder** list of the subtree rooted at `v`: each vertex visited before
its children's vertices, in the order of the children.
-/
noncomputable def preorder (hT : TreeOn p r) : (v : V) → List V := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  exact hwf.fix (C := fun _ => List V) (fun v ih =>
    v :: ((children p r v).attach.toList.flatMap (fun xc => ih xc.1 (children_depth_lt hT xc.2))))

/-- The **tour** returned by APPROX-TSP-TOUR: the vertices of the whole tree in
depth-first preorder, interpreted as a Hamiltonian cycle in `dfsTour_isTour`. -/
noncomputable def dfsTour (hT : TreeOn p r) : List V :=
  preorder hT r

-- Walk and cost machinery for Lemma 35.2 ---------------------------------

/-- The recursion equation for `dfsWalkFrom`: the walk from `v` visits `v`, then
walks each child's subtree and returns to `v`. -/
lemma dfsWalkFrom_fix (hT : TreeOn p r) (v : V) :
    dfsWalkFrom hT v =
      [v] ++ ((children p r v).attach.toList.flatMap
        (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])) := by
  classical
  unfold dfsWalkFrom
  dsimp only
  rw [WellFounded.fix_eq]

/-- The walk from any vertex is nonempty. -/
lemma dfsWalkFrom_ne_nil (hT : TreeOn p r) (v : V) : dfsWalkFrom hT v ≠ [] := by
  rw [dfsWalkFrom_fix hT v]
  simp

/-- The walk from `v` starts at `v`. -/
lemma dfsWalkFrom_head (hT : TreeOn p r) (v : V) :
    (dfsWalkFrom hT v).head (dfsWalkFrom_ne_nil hT v) = v := by
  calc
    (dfsWalkFrom hT v).head (dfsWalkFrom_ne_nil hT v)
      = ([v] ++ (children p r v).attach.toList.flatMap
          (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).head (by simp) := by
        exact head_eq_of_eq (dfsWalkFrom_fix hT v) (dfsWalkFrom_ne_nil hT v) (by simp)
    _ = v := by simp

/-- If every `g a` is nonempty, then `l.flatMap g` is nonempty whenever `l` is. -/
lemma flatMap_append_ne_nil {α β : Type} {g : α → List β} (hg : ∀ a, g a ≠ []) :
    ∀ l : List α, l ≠ [] → l.flatMap g ≠ [] := by
  intro l
  cases l with
  | nil => simp
  | cons a t =>
      rw [List.flatMap_cons]
      intro _
      intro h
      exact hg a (List.append_eq_nil_iff.mp h).1

/-- Every segment of the walk (`dfsWalkFrom c ++ [v]`) ends in `v`, so the
concatenated children list ends in `v`. -/
lemma flatMap_last_v (hT : TreeOn p r) {v : V} :
    ∀ cs : List {c : V // c ∈ children p r v},
      (hne : cs.flatMap (fun xc => dfsWalkFrom hT xc.1 ++ [v]) ≠ []) →
        (cs.flatMap (fun xc => dfsWalkFrom hT xc.1 ++ [v])).getLast hne = v := by
  intro cs
  induction cs with
  | nil => intro hne; simp at hne
  | cons xc rest ih =>
      intro hne
      by_cases hre : rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) = []
      · have hrest_nil : rest = [] := by
          by_contra hrn
          have hne' : rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) ≠ [] :=
            flatMap_append_ne_nil (fun xc => by simp [dfsWalkFrom_ne_nil hT xc.1]) rest hrn
          exact hne' hre
        subst hrest_nil
        have hflat : (xc :: []).flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) = dfsWalkFrom hT xc.1 ++ [v] := by
          simp
        have hne1 : dfsWalkFrom hT xc.1 ++ [v] ≠ [] := by simp [dfsWalkFrom_ne_nil hT xc.1]
        calc
          ((xc :: []).flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hne
            = (dfsWalkFrom hT xc.1 ++ [v]).getLast hne1 := getLast_eq_of_eq hflat hne hne1
          _ = v := getLast_append_singleton' (dfsWalkFrom hT xc.1) hne1
      · have hflat : (xc :: rest).flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])
          = (dfsWalkFrom hT xc.1 ++ [v]) ++ rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) := by
          rw [List.flatMap_cons]
        have hne1 : (dfsWalkFrom hT xc.1 ++ [v]) ++ rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) ≠ [] := by
          simp [hre]
        calc
          ((xc :: rest).flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hne
            = ((dfsWalkFrom hT xc.1 ++ [v]) ++ rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hne1 := getLast_eq_of_eq hflat hne hne1
          _ = (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hre :=
            getLast_append_of_right_ne_nil' (dfsWalkFrom hT xc.1 ++ [v])
              (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])) hne1 hre
          _ = v := ih hre

/-- The walk from `v` returns to `v`. -/
lemma dfsWalkFrom_last (hT : TreeOn p r) (v : V) :
    (dfsWalkFrom hT v).getLast (dfsWalkFrom_ne_nil hT v) = v := by
  let cs := (children p r v).attach.toList
  have hfix : dfsWalkFrom hT v = [v] ++ cs.flatMap
      (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) := dfsWalkFrom_fix hT v
  have hneFix : [v] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) ≠ [] := by simp
  have hlast : ([v] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hneFix = v := by
    by_cases hre : cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) = []
    · have hlist : [v] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) = [v] := by
        rw [hre]
        simp
      calc
        ([v] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hneFix
          = [v].getLast (by simp) := getLast_eq_of_eq hlist hneFix (by simp)
        _ = v := rfl
    · have htail : (cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hre = v :=
        flatMap_last_v hT cs hre
      exact (getLast_append_of_right_ne_nil' [v]
        (cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])) hneFix hre) ▸ htail
  calc
    (dfsWalkFrom hT v).getLast (dfsWalkFrom_ne_nil hT v)
      = ([v] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).getLast hneFix :=
        getLast_eq_of_eq hfix (dfsWalkFrom_ne_nil hT v) hneFix
    _ = v := hlast

/-- The cost of a child's walk plus the return edge to `v` telescopes to the
walk cost plus the child edge. -/
lemma pathCost_dfsWalkFrom_append_singleton (hT : TreeOn p r) (w : Graph V) (v : V) (c : V) :
    pathCost w (dfsWalkFrom hT c ++ [v]) = walkCost w (dfsWalkFrom hT c) + w c v := by
  rw [pathCost_append_nonempty w (dfsWalkFrom_ne_nil hT c) (by simp)]
  rw [dfsWalkFrom_last hT c]
  simp [walkCost, pathCost]

/-- The walk `[v] ++ flatMap (fun c => dfsWalkFrom c ++ [v])` decomposes into a
sum over the children: for each child `c`, the edge `v → c` plus the child's
segment. -/
lemma pathCost_walk_segments (w : Graph V) (hT : TreeOn p r) {v : V}
    (cs : List {c : V // c ∈ children p r v}) :
    pathCost w ([v] ++ (cs.flatMap (fun xc => dfsWalkFrom hT xc.1 ++ [v])))
      = (cs.map (fun xc : {c : V // c ∈ children p r v} => w v xc.1 + pathCost w (dfsWalkFrom hT xc.1 ++ [v]))).sum := by
  induction cs with
  | nil => simp [pathCost]
  | cons xc rest ih =>
      rw [List.flatMap_cons]
      have hg : dfsWalkFrom hT xc.1 ++ [v] ≠ [] := by simp [dfsWalkFrom_ne_nil hT xc.1]
      have hlead : [v] ≠ [] := by simp
      have hSeg : pathCost w ([v] ++ (dfsWalkFrom hT xc.1 ++ [v])) =
          pathCost w (dfsWalkFrom hT xc.1 ++ [v]) + w v xc.1 := by
        rw [pathCost_append_nonempty w hlead hg]
        simp [List.getLast_singleton]
        have hhead : (dfsWalkFrom hT xc.1 ++ [v]).head hg = xc.1 := by
          rw [head_append_of_left_ne_nil' (dfsWalkFrom_ne_nil hT xc.1) hg]
          exact dfsWalkFrom_head hT xc.1
        rw [hhead]
        ac_rfl
      by_cases hre : rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) = []
      · have hrest_nil : rest = [] := by
          by_contra hrn
          have hne' : rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]) ≠ [] :=
            flatMap_append_ne_nil (fun xc => by simp [dfsWalkFrom_ne_nil hT xc.1]) rest hrn
          exact hne' hre
        subst hrest_nil
        simp
        rw [pathCost_cons_nonempty w v hg]
        have hhead : (dfsWalkFrom hT xc.1 ++ [v]).head hg = xc.1 := by
          rw [head_append_of_left_ne_nil' (dfsWalkFrom_ne_nil hT xc.1) hg]
          exact dfsWalkFrom_head hT xc.1
        rw [hhead]
      · rw [← List.append_assoc]
        have hApp : pathCost w (([v] ++ (dfsWalkFrom hT xc.1 ++ [v])) ++ rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])) =
            pathCost w ([v] ++ (dfsWalkFrom hT xc.1 ++ [v]))
              + pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]))
              + w v ((rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).head hre) := by
          have hne1 : [v] ++ (dfsWalkFrom hT xc.1 ++ [v]) ≠ [] := by simp
          rw [pathCost_append_nonempty w hne1 hre]
          have hlast : ([v] ++ (dfsWalkFrom hT xc.1 ++ [v])).getLast hne1 = v := by
            rw [getLast_append_of_right_ne_nil' [v] (dfsWalkFrom hT xc.1 ++ [v]) hne1 hg]
            exact getLast_append_singleton' (dfsWalkFrom hT xc.1) hg
          rw [hlast]
        rw [hApp]
        rw [hSeg]
        have hRest : pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]))
              + w v ((rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).head hre)
            = pathCost w ([v] ++ rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])) := by
          rw [pathCost_append_nonempty w hlead hre]
          simp [List.getLast_singleton]
          ac_rfl
        have hcomb : pathCost w (dfsWalkFrom hT xc.1 ++ [v]) + w v xc.1 +
            (pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]))
              + w v ((rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).head hre))
            = (pathCost w (dfsWalkFrom hT xc.1 ++ [v]) + w v xc.1) + pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]))
              + w v ((rest.flatMap (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v])).head hre) := by
          ac_rfl
        rw [← hcomb]
        rw [hRest]
        rw [ih]
        simp
        ac_rfl

/-- The walk cost from `v` is the sum over the children of (child walk cost plus
the two edges joining them). -/
lemma dfsWalkFrom_cost_rec (hT : TreeOn p r) (w : Graph V) (v : V) :
    walkCost w (dfsWalkFrom hT v)
      = ((children p r v).attach.toList.map
          (fun xc : {c : V // c ∈ children p r v} =>
            walkCost w (dfsWalkFrom hT xc.1) + w xc.1 v + w v xc.1)).sum := by
  rw [dfsWalkFrom_fix hT v]
  change pathCost w ([v] ++ (children p r v).attach.toList.flatMap
      (fun xc : {c : V // c ∈ children p r v} => dfsWalkFrom hT xc.1 ++ [v]))
    = ((children p r v).attach.toList.map
        (fun xc : {c : V // c ∈ children p r v} => walkCost w (dfsWalkFrom hT xc.1) + w xc.1 v + w v xc.1)).sum
  rw [pathCost_walk_segments w hT (children p r v).attach.toList]
  apply sum_map_congr
  intro xc hxc
  rw [pathCost_dfsWalkFrom_append_singleton hT w v xc.1]
  ac_rfl

/-- Same as `dfsWalkFrom_cost_rec`, with the sum over the children Finset. -/
lemma dfsWalkFrom_cost_rec_finset (hT : TreeOn p r) (w : Graph V) (v : V) :
    walkCost w (dfsWalkFrom hT v)
      = (children p r v).sum (fun c => walkCost w (dfsWalkFrom hT c) + w c v + w v c) := by
  rw [dfsWalkFrom_cost_rec hT w v]
  exact finset_sum_attach_toList (children p r v) (fun c => walkCost w (dfsWalkFrom hT c) + w c v + w v c)

-- Subtree decomposition -------------------------------------------------

/-- Membership in a subtree: `x` lies in `subtree v` iff `x = v` or `x` lies in
the subtree of a child of `v`. -/
lemma subtree_mem_iff (hT : TreeOn p r) (x v : V) :
    x ∈ subtree p r v ↔ x = v ∨ ∃ c : V, c ∈ children p r v ∧ x ∈ subtree p r c := by
  classical
  rw [subtree]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      have hexists : ∃ n : Nat, p^[n] x = v := ⟨k, hk⟩
      let k0 := Nat.find hexists
      have hk0 : p^[k0] x = v := Nat.find_spec hexists
      have hk0min : ∀ n : Nat, n < k0 → p^[n] x ≠ v := fun n hn => Nat.find_min hexists hn
      have hk0pos : 0 < k0 := by
        by_contra hz
        have hk0zero : k0 = 0 := by omega
        have : x = v := by simpa [hk0zero] using hk0
        exact hxv this
      refine ⟨p^[k0 - 1] x, ?memc, ?subc⟩
      · rw [children]
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ (p^[k0 - 1] x)
        · constructor
          · intro hcr
            have hpr : p^[k0] x = r := by
              calc
                p^[k0] x = p (p^[k0 - 1] x) := by
                  conv_lhs =>
                    rw [show k0 = (k0 - 1) + 1 by omega]
                  rw [Function.iterate_succ_apply']
                _ = r := by
                  rw [hcr]
                  exact hT.root_fixed
            have hv : v = r := hk0.symm.trans hpr
            apply hk0min (k0 - 1) (by omega)
            calc
              p^[k0 - 1] x = r := hcr
              _ = v := hv.symm
          · change p (p^[k0 - 1] x) = v
            calc
              p (p^[k0 - 1] x) = p^[k0] x := by
                conv_rhs =>
                  rw [show k0 = (k0 - 1) + 1 by omega]
                rw [Function.iterate_succ_apply']
              _ = v := hk0
      · rw [subtree]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, ⟨k0 - 1, rfl⟩⟩
  · intro h
    rcases h with hxv | ⟨c, hc, hsub⟩
    · subst x
      exact ⟨0, rfl⟩
    · rw [subtree] at hsub
      simp at hsub
      have hpc : p c = v := (Finset.mem_filter.mp hc).2.2
      rcases hsub with ⟨k, hk⟩
      exact ⟨k + 1, by
        calc
          p^[k + 1] x = p (p^[k] x) := by
            rw [Function.iterate_succ_apply']
          _ = p c := by rw [hk]
          _ = v := hpc⟩

/-- Two children of `v` whose iterates of `x` reach them must coincide. -/
lemma child_subtree_depth (hT : TreeOn p r) (v : V) {c1 c2 : V} {i j : Nat}
    (hc1 : c1 ∈ children p r v) (hc2 : c2 ∈ children p r v) (hij : i ≤ j)
    {x : V} (hi : p^[i] x = c1) (hj : p^[j] x = c2) : c1 = c2 := by
  classical
  have hstep : p^[j - i] c1 = c2 := by
    calc
      p^[j - i] c1 = p^[j - i] (p^[i] x) := by rw [hi]
      _ = p^[j] x := by
        rw [show j = (j - i) + i by omega]
        simp [Function.iterate_add]
      _ = c2 := hj
  by_cases hji0 : j - i = 0
  · simpa [hji0] using hstep
  · have hji_pos : 0 < j - i := Nat.pos_of_ne_zero hji0
    rcases Finset.mem_filter.mp hc1 with ⟨_, hc1p⟩
    rcases Finset.mem_filter.mp hc2 with ⟨_, hc2p⟩
    rcases hc1p with ⟨hc1ne, hpc1⟩
    rcases hc2p with ⟨hc2ne, hpc2⟩
    have hd1 : depth p r c1 = depth p r v + 1 := hT.depth_child_succ hpc1 hc1ne
    have hd2 : depth p r c2 = depth p r v + 1 := hT.depth_child_succ hpc2 hc2ne
    have hle : j - i ≤ depth p r c1 :=
      iterate_le_depth_of_ne_root hT (u := c1) (i := j - i) (x := c2) hstep hc2ne
    have hiter := hT.depth_iterate c1 (j - i) hle
    have hdep : depth p r c2 = depth p r c1 - (j - i) := by
      rw [hstep] at hiter
      exact hiter
    have hlt : (depth p r v + 1) - (j - i) < depth p r v + 1 := by omega
    have hfalse : depth p r v + 1 < depth p r v + 1 := by
      calc
        depth p r v + 1 = depth p r c2 := hd2.symm
        _ = depth p r c1 - (j - i) := hdep
        _ = (depth p r v + 1) - (j - i) := by rw [hd1]
        _ < depth p r v + 1 := hlt
    omega

/-- The subtrees of distinct children of `v` are pairwise disjoint. -/
lemma children_subtree_disjoint (hT : TreeOn p r) (v : V) :
    (children p r v : Set V).PairwiseDisjoint (fun c => subtree p r c) := by
  classical
  intro c1 hc1 c2 hc2 hne
  change Disjoint (subtree p r c1) (subtree p r c2)
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [subtree] at hx1 hx2
  rcases Finset.mem_filter.mp hx1 with ⟨_, ⟨i, hi⟩⟩
  rcases Finset.mem_filter.mp hx2 with ⟨_, ⟨j, hj⟩⟩
  by_cases hij : i ≤ j
  · exact hne (child_subtree_depth hT v hc1 hc2 hij hi hj)
  · have hji : j ≤ i := by omega
    have : c2 = c1 := child_subtree_depth hT v hc2 hc1 hji hj hi
    exact hne this.symm

/-- A vertex does not lie in the subtree of its own child. -/
lemma v_not_mem_child_subtree (hT : TreeOn p r) {c v : V} (hc : c ∈ children p r v) :
    v ∉ subtree p r c := by
  classical
  rw [subtree]
  intro hv
  rcases Finset.mem_filter.mp hv with ⟨_, ⟨k, hk⟩⟩
  rcases Finset.mem_filter.mp hc with ⟨_, hcp⟩
  rcases hcp with ⟨hcne, hpc⟩
  have hd : depth p r c = depth p r v + 1 := hT.depth_child_succ hpc hcne
  have hle : k ≤ depth p r v := iterate_le_depth_of_ne_root hT (u := v) (i := k) (x := c) hk hcne
  have hiter := hT.depth_iterate v k hle
  have hdep : depth p r c = depth p r v - k := by
    rw [hk] at hiter
    exact hiter
  have hlt : depth p r v - k < depth p r v + 1 := by omega
  have hfalse : depth p r v + 1 < depth p r v + 1 := by
    calc
      depth p r v + 1 = depth p r c := hd.symm
      _ = depth p r v - k := hdep
      _ < depth p r v + 1 := hlt
  omega

/-- The subtree of `v` is `v` together with the disjoint union of its children's
subtrees. -/
lemma subtree_eq_insert_disjiUnion (hT : TreeOn p r) (v : V) :
    subtree p r v = insert v (Finset.disjiUnion (children p r v) (fun c => subtree p r c) (children_subtree_disjoint hT v)) := by
  classical
  ext x
  rw [Finset.mem_insert, Finset.mem_disjiUnion]
  exact subtree_mem_iff hT x v

/-- The subtree cost decomposes as the vertex's own edge plus the sum of its
children's subtree costs (as a list sum over the attached children). -/
lemma subtreeCost_rec (hT : TreeOn p r) (w : Graph V) (v : V) :
    subtreeCost w p r v = w v (p v) + ((children p r v).attach.toList.map (fun xc : {c : V // c ∈ children p r v} => subtreeCost w p r xc.1)).sum := by
  classical
  unfold subtreeCost
  rw [subtree_eq_insert_disjiUnion hT v]
  have hvnotin : v ∉ Finset.disjiUnion (children p r v) (fun c => subtree p r c) (children_subtree_disjoint hT v) := by
    rw [Finset.mem_disjiUnion]
    intro h
    rcases h with ⟨c, hc, hvc⟩
    exact v_not_mem_child_subtree hT hc hvc
  rw [Finset.sum_insert hvnotin]
  congr 1
  rw [Finset.sum_disjiUnion]
  exact (finset_sum_attach_toList (children p r v) (fun c => subtreeCost w p r c)).symm

/-- Same as `subtreeCost_rec`, with the sum over the children Finset. -/
lemma subtreeCost_rec_finset (hT : TreeOn p r) (w : Graph V) (v : V) :
    subtreeCost w p r v = w v (p v) + (children p r v).sum (fun c => subtreeCost w p r c) := by
  rw [subtreeCost_rec hT w v]
  congr 1
  exact finset_sum_attach_toList (children p r v) (fun c => subtreeCost w p r c)

-- Lemma 35.2 ------------------------------------------------------------

/--
**Lemma (walk cost).**  The depth-first walk from `v` over its subtree costs
twice the subtree cost, excluding `v`'s own parent edge.  This is the recursive
statement used to prove Lemma 35.2 at the root.
-/
lemma dfsWalkFrom_cost (hT : TreeOn p r) (w : Graph V) (hSymm : ∀ x y : V, w x y = w y x) (v : V) :
    walkCost w (dfsWalkFrom hT v) = 2 * (subtreeCost w p r v - w v (p v)) := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  refine hwf.induction (C := fun u : V =>
    walkCost w (dfsWalkFrom hT u) = 2 * (subtreeCost w p r u - w u (p u))) v ?_
  intro u hrec
  have hchild : ∀ c ∈ children p r u,
      walkCost w (dfsWalkFrom hT c) + w c u + w u c = 2 * subtreeCost w p r c := by
    intro c hc
    have hrec' := hrec c (children_depth_lt hT hc)
    rw [hrec']
    rcases Finset.mem_filter.mp hc with ⟨_, hcprops⟩
    rcases hcprops with ⟨hcne, hpc⟩
    have hw1 : w c (p c) = w c u := by rw [hpc]
    have hw2 : w u c = w c u := hSymm u c
    have hcsub : c ∈ subtree p r c := by
      rw [subtree]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ c, ⟨0, rfl⟩⟩
    have hle : w c (p c) ≤ subtreeCost w p r c := by
      unfold subtreeCost
      exact Finset.single_le_sum (fun x _ => Nat.zero_le (w x (p x))) hcsub
    have hle' : w c u ≤ subtreeCost w p r c := by simpa [hw1] using hle
    rw [hw1, hw2]
    omega
  rw [dfsWalkFrom_cost_rec_finset hT w u]
  rw [subtreeCost_rec_finset hT w u]
  have hsum : (children p r u).sum (fun c => walkCost w (dfsWalkFrom hT c) + w c u + w u c)
      = (children p r u).sum (fun c => 2 * subtreeCost w p r c) := by
    apply Finset.sum_congr
    · rfl
    · intro c hc
      exact hchild c hc
  rw [hsum]
  have hcancel : w u (p u) + (children p r u).sum (fun c => subtreeCost w p r c) - w u (p u)
      = (children p r u).sum (fun c => subtreeCost w p r c) := by
    omega
  rw [hcancel]
  rw [Nat.mul_comm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr
  · rfl
  · intro c hc
    rw [Nat.mul_comm]

/--
**Lemma 35.2.**  The depth-first walk of a rooted tree traverses every tree edge
exactly twice, so its cost is exactly twice the tree's cost.

Under a symmetric weight function `w`, the full walk `dfsWalk hT` (from and back
to the root) costs `2 * treeCost w p r`.
-/
lemma dfsWalk_cost (hT : TreeOn p r) (w : Graph V) (hSymm : ∀ x y : V, w x y = w y x) :
    walkCost w (dfsWalk hT) = 2 * treeCost w p r := by
  change walkCost w (dfsWalkFrom hT r) = 2 * treeCost w p r
  rw [dfsWalkFrom_cost hT w hSymm r]
  have hroot : subtreeCost w p r r - w r (p r) = treeCost w p r := by
    have hsub : subtreeCost w p r r = treeCost w p r + w r (p r) := by
      unfold subtreeCost treeCost
      have huniv : subtree p r r = Finset.univ := by
        ext x
        simp [subtree, hT.reaches_root x]
      rw [huniv]
      have hsplit : Finset.univ.sum (fun x => w x (p x)) = w r (p r) + (Finset.univ.erase r).sum (fun x => w x (p x)) := by
        calc
          Finset.univ.sum (fun x => w x (p x)) = (insert r (Finset.univ.erase r)).sum (fun x => w x (p x)) := by
            conv_lhs =>
              rw [← Finset.insert_erase (Finset.mem_univ r)]
          _ = w r (p r) + (Finset.univ.erase r).sum (fun x => w x (p x)) := by
            rw [Finset.sum_insert (by simp)]
      rw [hsplit]
      omega
    rw [hsub]
    exact Nat.add_sub_cancel (treeCost w p r) (w r (p r))
  rw [hroot]

-- Preorder: dfsTour visits every vertex ---------------------------------

/-- The recursion equation for `preorder`: the preorder from `v` visits `v`,
then the preorders of each child's subtree. -/
lemma preorder_fix (hT : TreeOn p r) (v : V) :
    preorder hT v = v :: ((children p r v).attach.toList.flatMap
      (fun xc : {c : V // c ∈ children p r v} => preorder hT xc.1)) := by
  classical
  unfold preorder
  dsimp only
  rw [WellFounded.fix_eq]

/-- A vertex is in the preorder of `v` iff it lies in the subtree of `v`. -/
lemma preorder_mem_subtree (hT : TreeOn p r) (v : V) :
    ∀ x : V, x ∈ preorder hT v ↔ x ∈ subtree p r v := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  refine hwf.induction (C := fun u : V => ∀ x : V, x ∈ preorder hT u ↔ x ∈ subtree p r u) v ?_
  intro u hrec
  intro x
  constructor
  · intro hx
    rw [preorder_fix hT u] at hx
    rcases List.mem_cons.mp hx with hxv | hxmem
    · subst x
      exact (subtree_mem_iff hT u u).2 (Or.inl rfl)
    · rw [List.mem_flatMap] at hxmem
      rcases hxmem with ⟨yc, hyc_mem, hxpre⟩
      have hxsub : x ∈ subtree p r yc.1 := (hrec yc.1 (children_depth_lt hT yc.2) x).1 hxpre
      exact (subtree_mem_iff hT x u).2 (Or.inr ⟨yc.1, yc.2, hxsub⟩)
  · intro hx
    rw [preorder_fix hT u]
    rcases (subtree_mem_iff hT x u).1 hx with hxv | ⟨c, hc, hxsub⟩
    · subst x
      exact List.mem_cons_self
    · have hxpre : x ∈ preorder hT c := (hrec c (children_depth_lt hT hc) x).2 hxsub
      have hc_mem : (⟨c, hc⟩ : {c : V // c ∈ children p r u}) ∈ (children p r u).attach.toList := by
        rw [Finset.mem_toList]
        exact (Finset.mem_attach (s := children p r u) ⟨c, hc⟩)
      exact List.mem_cons_of_mem u (List.mem_flatMap_of_mem hc_mem hxpre)

/-- The preorder tour visits every vertex exactly once in the sense that every
vertex appears in it (the absence of duplicates is `dfsTour_nodup` below). -/
lemma dfsTour_mem (hT : TreeOn p r) (x : V) : x ∈ dfsTour hT := by
  classical
  change x ∈ preorder hT r
  have hx : x ∈ subtree p r r := by
    rw [subtree]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, hT.reaches_root x⟩
  exact (preorder_mem_subtree hT r x).2 hx

/-- The preorders of two distinct children of `u` are disjoint lists. -/
lemma preorder_disjoint_of_ne (hT : TreeOn p r) {u c1 c2 : V}
    (hc1 : c1 ∈ children p r u) (hc2 : c2 ∈ children p r u) (hne : c1 ≠ c2) :
    List.Disjoint (preorder hT c1) (preorder hT c2) := by
  classical
  rw [List.disjoint_left]
  intro x hx1 hx2
  have hxsub1 : x ∈ subtree p r c1 := (preorder_mem_subtree hT c1 x).1 hx1
  have hxsub2 : x ∈ subtree p r c2 := (preorder_mem_subtree hT c2 x).1 hx2
  have hdisj := children_subtree_disjoint hT u hc1 hc2 hne
  change Disjoint (subtree p r c1) (subtree p r c2) at hdisj
  rw [Finset.disjoint_left] at hdisj
  exact hdisj hxsub1 hxsub2

/-- A duplicate-free list of children with pairwise-disjoint preorders gives a
`Pairwise (Disjoint on preorder)` relation. -/
lemma pairwise_disjoint_of_nodup (hT : TreeOn p r) (u : V) :
    ∀ cs : List {c : V // c ∈ children p r u},
      List.Nodup cs →
      (∀ xc1 ∈ cs, ∀ xc2 ∈ cs, xc1 ≠ xc2 →
        List.Disjoint (preorder hT xc1.1) (preorder hT xc2.1)) →
      List.Pairwise (fun xc1 xc2 : {c : V // c ∈ children p r u} =>
        List.Disjoint (preorder hT xc1.1) (preorder hT xc2.1)) cs := by
  intro cs
  induction cs with
  | nil => simp
  | cons xc rest ih =>
      intro hnd hdisj
      rw [List.pairwise_cons]
      constructor
      · intro a' ha'
        apply hdisj xc (by simp) a' (List.mem_cons.mpr (Or.inr ha'))
        intro hxc
        have hxc_rest : xc ∈ rest := by simpa [hxc] using ha'
        exact (List.nodup_cons.mp hnd).1 hxc_rest
      · apply ih (List.nodup_cons.mp hnd).2
        intro xc1 h1 xc2 h2 hne
        exact hdisj xc1 (by simp [h1]) xc2 (by simp [h2]) hne

/-- The preorder of any subtree has no duplicate vertices. -/
lemma preorder_nodup (hT : TreeOn p r) (v : V) : List.Nodup (preorder hT v) := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  refine hwf.induction (C := fun u : V => List.Nodup (preorder hT u)) v ?_
  intro u hrec
  rw [preorder_fix hT u]
  rw [List.nodup_cons]
  constructor
  · intro hu
    rw [List.mem_flatMap] at hu
    rcases hu with ⟨yc, hyc, hupre⟩
    have husub : u ∈ subtree p r yc.1 := (preorder_mem_subtree hT yc.1 u).1 hupre
    exact v_not_mem_child_subtree hT yc.2 husub
  · rw [List.nodup_flatMap]
    constructor
    · intro xc hxc
      exact hrec xc.1 (children_depth_lt hT xc.2)
    · have hndlist : List.Nodup ((children p r u).attach.toList) := by
        exact Finset.nodup_toList (children p r u).attach
      have hdisj : ∀ xc1 ∈ (children p r u).attach.toList, ∀ xc2 ∈ (children p r u).attach.toList,
          xc1 ≠ xc2 → List.Disjoint (preorder hT xc1.1) (preorder hT xc2.1) := by
        intro xc1 h1 xc2 h2 hne
        have hne' : xc1.1 ≠ xc2.1 := by
          intro hval
          exact hne (Subtype.ext hval)
        exact preorder_disjoint_of_ne hT xc1.2 xc2.2 hne'
      exact pairwise_disjoint_of_nodup hT u ((children p r u).attach.toList) hndlist hdisj

/-- The preorder tour has no repeated vertices. -/
lemma dfsTour_nodup (hT : TreeOn p r) : List.Nodup (dfsTour hT) := by
  change List.Nodup (preorder hT r)
  exact preorder_nodup hT r

/--
**Lemma (isTour).**  The preorder tour visits every vertex exactly once: it has
no duplicates and every vertex appears in it.
-/
lemma dfsTour_isTour (hT : TreeOn p r) :
    List.Nodup (dfsTour hT) ∧ ∀ x : V, x ∈ dfsTour hT := by
  exact ⟨dfsTour_nodup hT, dfsTour_mem hT⟩

/-- The preorder of any subtree is nonempty. -/
lemma preorder_ne_nil (hT : TreeOn p r) (v : V) : preorder hT v ≠ [] := by
  rw [preorder_fix hT v]
  simp

/-- The last vertex of the preorder of `v`. -/
noncomputable def preorderLast (hT : TreeOn p r) (v : V) : V :=
  (preorder hT v).getLast (preorder_ne_nil hT v)

/-- The preorder of `v` starts at `v`. -/
lemma preorder_head (hT : TreeOn p r) (v : V) :
    (preorder hT v).head (preorder_ne_nil hT v) = v := by
  let L := (children p r v).attach.toList.flatMap (fun xc : {c : V // c ∈ children p r v} => preorder hT xc.1)
  have hfix : preorder hT v = v :: L := preorder_fix hT v
  have hneL : v :: L ≠ [] := by simp
  calc
    (preorder hT v).head (preorder_ne_nil hT v) = (v :: L).head hneL := head_eq_of_eq hfix (preorder_ne_nil hT v) hneL
    _ = v := rfl

/-- The last vertex of the concatenation of the children preorders, or `u` if
there are no children (equivalently: the last vertex of `[u]` followed by the
children preorders). -/
noncomputable def tailLast (hT : TreeOn p r) (u : V)
    (cs : List {c : V // c ∈ children p r u}) : V :=
  if h : cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) = [] then u
  else (cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast h

/-- The last vertex of the children preorders is unchanged when prepending a child (a nonempty tail still determines the last vertex). -/
lemma tailLast_cons (hT : TreeOn p r) {u : V} (xc : {c : V // c ∈ children p r u})
    (rest : List {c : V // c ∈ children p r u}) (hrest : rest ≠ []) :
    tailLast hT u (xc :: rest) = tailLast hT u rest := by
  unfold tailLast
  have hne : (xc :: rest).flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] := by
    intro h
    exact (preorder_ne_nil hT xc.1) (by simpa using (List.append_eq_nil_iff.mp h).1)
  have hneRest : rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] :=
    flatMap_append_ne_nil (fun xc => preorder_ne_nil hT xc.1) rest hrest
  rw [dif_neg hne, dif_neg hneRest]
  have heq : (xc :: rest).flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)
      = preorder hT xc.1 ++ rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) := by
    rfl
  have hne' : preorder hT xc.1 ++ rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] := by
    intro h
    exact (preorder_ne_nil hT xc.1) (by simpa using (List.append_eq_nil_iff.mp h).1)
  calc
    ((xc :: rest).flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast hne
        = (preorder hT xc.1 ++ rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast hne' :=
          getLast_eq_of_eq heq hne hne'
    _ = (rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast hneRest :=
          getLast_append_of_right_ne_nil' (preorder hT xc.1)
              (rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) hne' hneRest

/-- The cost of a path starting with `u` decomposes into the cost of the tail plus the first edge. -/
lemma pathCost_singleton_append (w : Graph V) (u : V) {l : List V} (h : l ≠ []) :
    pathCost w ([u] ++ l) = pathCost w l + w u (l.head h) := by
  rw [pathCost_append_nonempty w (by simp) h]
  simp [pathCost]


/--
**Shortcut (children list).**  The preorder path through a list of children
closed to a target `t` costs no more than the sum over the children of their
preorder costs plus the edges to and from `u`, plus the closing edge `u → t`.
Each inter-child edge is charged to a two-hop path through `u` by the triangle
inequality.
-/
lemma preorder_cycle_aux (hT : TreeOn p r) (w : Graph V)
    (hTri : ∀ a b c : V, w a c ≤ w a b + w b c) {u : V} (t : V)
    (cs : List {c : V // c ∈ children p r u}) :
    pathCost w ([u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) + w (tailLast hT u cs) t
      ≤ (cs.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum + w u t := by
  induction cs with
  | nil =>
      simp [tailLast, pathCost]
  | cons xc rest ih =>
      by_cases hre : rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) = []
      · have hrest_nil : rest = [] := by
          by_contra hrn
          have hne' : rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] :=
            flatMap_append_ne_nil (fun xc => preorder_ne_nil hT xc.1) rest hrn
          exact hne' hre
        subst hrest_nil
        have hc : pathCost w ([u] ++ preorder hT xc.1) = pathCost w (preorder hT xc.1) + w u xc.1 := by
          rw [pathCost_append_nonempty w (by simp) (preorder_ne_nil hT xc.1)]
          simp [pathCost, preorder_head hT xc.1]
        have hflat : [xc].flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) = preorder hT xc.1 := by
          simp
        have htl1 : tailLast hT u [xc] = preorderLast hT xc.1 := by
          unfold tailLast
          rw [hflat]
          rw [dif_neg (preorder_ne_nil hT xc.1)]
          rfl
        rw [hflat]
        rw [hc]
        rw [htl1]
        simp
        have htri := hTri (preorderLast hT xc.1) u t
        omega
      · have hRne : rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] := hre
        have hrest_ne : rest ≠ [] := by
          intro hr
          subst hr
          simp at hre
        have htl : tailLast hT u (xc :: rest) = tailLast hT u rest := tailLast_cons hT xc rest hrest_ne
        rw [List.flatMap_cons]
        rw [htl]
        rw [← List.append_assoc]
        have hne1 : [u] ++ preorder hT xc.1 ≠ [] := by simp
        have hgl : ([u] ++ preorder hT xc.1).getLast hne1 = preorderLast hT xc.1 := by
          unfold preorderLast
          rw [getLast_append_of_right_ne_nil' [u] (preorder hT xc.1) hne1 (preorder_ne_nil hT xc.1)]
        have h1 : pathCost w (([u] ++ preorder hT xc.1) ++ rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1))
            = pathCost w (preorder hT xc.1) + w u xc.1 + pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1))
              + w (preorderLast hT xc.1) ((rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).head hRne) := by
          rw [pathCost_append_nonempty w hne1 hRne]
          rw [pathCost_singleton_append w u (preorder_ne_nil hT xc.1)]
          rw [preorder_head hT xc.1]
          rw [hgl]
        rw [h1]
        rw [List.map_cons, List.sum_cons]
        have htri := hTri (preorderLast hT xc.1) u ((rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).head hRne)
        have h2 : pathCost w (rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1))
            + w u ((rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).head hRne)
            = pathCost w ([u] ++ rest.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) :=
          (pathCost_singleton_append w u hRne).symm
        nlinarith

-- Instantiate preorder_cycle_aux at the full children list: the last vertex of
-- `[u]` followed by all children preorders is `preorderLast u`.
/-- **Shortcut (per vertex).**  The preorder path of `u` closed to `t` costs
no more than the sum over the children of their preorder costs plus the edges
to and from `u`, plus the closing edge `u → t`. -/
lemma preorder_cycle_le_sum (hT : TreeOn p r) (w : Graph V)
    (hTri : ∀ a b c : V, w a c ≤ w a b + w b c) (u : V) (t : V) :
    pathCost w (preorder hT u) + w (preorderLast hT u) t
      ≤ ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum + w u t := by
  let cs := (children p r u).attach.toList
  have haux := preorder_cycle_aux hT w hTri t cs
  have hfix' : preorder hT u = u :: cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) := by
    simpa [cs] using preorder_fix hT u
  have hpath : pathCost w ([u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) = pathCost w (preorder hT u) := by
    rw [hfix']
    rfl
  have htl : tailLast hT u cs = preorderLast hT u := by
    unfold tailLast preorderLast
    by_cases hcs : cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) = []
    · rw [dif_pos hcs]
      have hsingle : preorder hT u = [u] := by
        rw [hfix', hcs]
      have hne1 : [u] ≠ [] := by simp
      symm
      calc
        (preorder hT u).getLast (preorder_ne_nil hT u) = [u].getLast hne1 := getLast_eq_of_eq hsingle (preorder_ne_nil hT u) hne1
        _ = u := rfl
    · rw [dif_neg hcs]
      have heq : preorder hT u = [u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) := by
        rw [hfix']
        rfl
      have hneApp : [u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1) ≠ [] := by simp
      symm
      calc
        (preorder hT u).getLast (preorder_ne_nil hT u)
            = ([u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast hneApp :=
              getLast_eq_of_eq heq (preorder_ne_nil hT u) hneApp
        _ = (cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)).getLast hcs :=
              getLast_append_of_right_ne_nil' [u] (cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) hneApp hcs
  -- assemble
  calc
    pathCost w (preorder hT u) + w (preorderLast hT u) t
        = pathCost w ([u] ++ cs.flatMap (fun xc : {c : V // c ∈ children p r u} => preorder hT xc.1)) + w (tailLast hT u cs) t := by
          rw [hpath, htl]
    _ ≤ (cs.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum + w u t := haux
    _ = ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum + w u t := by simp [cs]

/--
**Shortcut bound (per subtree).**  For every subtree `v` and any target `t`,
the preorder path of `v` closed to `t` costs no more than the walk of `v` plus
the edge `v → t`.  Proved by well-founded induction on the subtree, with the
target universally quantified so that inter-child charging can re-target.
-/
lemma preorder_bound (hT : TreeOn p r) (w : Graph V)
    (hTri : ∀ a b c : V, w a c ≤ w a b + w b c) (t : V) (v : V) :
    pathCost w (preorder hT v) + w (preorderLast hT v) t ≤ pathCost w (dfsWalkFrom hT v) + w v t := by
  classical
  let R : V → V → Prop := fun a b => Fintype.card V - depth p r a < Fintype.card V - depth p r b
  have hwf : WellFounded R := (measure (fun a : V => Fintype.card V - depth p r a)).wf
  have hall : ∀ u : V, ∀ t : V,
      pathCost w (preorder hT u) + w (preorderLast hT u) t ≤ pathCost w (dfsWalkFrom hT u) + w u t := by
    intro u
    refine hwf.induction (C := fun u : V => ∀ t : V,
      pathCost w (preorder hT u) + w (preorderLast hT u) t ≤ pathCost w (dfsWalkFrom hT u) + w u t) u ?_
    intro u hrec t
    have h1 := preorder_cycle_le_sum hT w hTri u t
    have h2 : ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum
        ≤ ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (dfsWalkFrom hT xc.1) + w xc.1 u + w u xc.1)).sum := by
      apply List.sum_le_sum
      intro xc hxc
      have hrec' := hrec xc.1 (children_depth_lt hT xc.2) u
      exact Nat.add_le_add_right hrec' (w u xc.1)
    have h3 : ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
          pathCost w (dfsWalkFrom hT xc.1) + w xc.1 u + w u xc.1)).sum = pathCost w (dfsWalkFrom hT u) := by
      simpa [walkCost] using (dfsWalkFrom_cost_rec hT w u).symm
    calc
      pathCost w (preorder hT u) + w (preorderLast hT u) t
          ≤ ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
              pathCost w (preorder hT xc.1) + w (preorderLast hT xc.1) u + w u xc.1)).sum + w u t := h1
      _ ≤ ((children p r u).attach.toList.map (fun xc : {c : V // c ∈ children p r u} =>
              pathCost w (dfsWalkFrom hT xc.1) + w xc.1 u + w u xc.1)).sum + w u t := Nat.add_le_add_right h2 (w u t)
      _ = pathCost w (dfsWalkFrom hT u) + w u t := by rw [h3]
  exact hall v t

/-- The preorder tour is nonempty. -/
lemma dfsTour_ne_nil (hT : TreeOn p r) : dfsTour hT ≠ [] := by
  change preorder hT r ≠ []
  exact preorder_ne_nil hT r

/-- The preorder tour starts at the root. -/
lemma dfsTour_head (hT : TreeOn p r) : (dfsTour hT).head (dfsTour_ne_nil hT) = r := by
  change (preorder hT r).head (preorder_ne_nil hT r) = r
  exact preorder_head hT r

/-- The last vertex of the preorder tour. -/
lemma dfsTour_last (hT : TreeOn p r) : (dfsTour hT).getLast (dfsTour_ne_nil hT) = preorderLast hT r := by
  change (preorder hT r).getLast (preorder_ne_nil hT r) = preorderLast hT r
  rfl

/--
**Lemma (shortcut).**  The tour obtained by shortcutting the depth-first walk —
the preorder list read as a cycle — costs no more than the walk itself.  This is
the triangle-inequality step of APPROX-TSP-TOUR: every skipped return is charged
to a two-hop path through the tree, and `w v v = 0` closes the leaf-root case.
-/
lemma dfsTour_bound (hT : TreeOn p r) (w : Graph V)
    (hTri : ∀ a b c : V, w a c ≤ w a b + w b c)
    (hLoop : ∀ v : V, w v v = 0) :
    tourCostTo w ((dfsTour hT).head (dfsTour_ne_nil hT)) (dfsTour hT) ≤ walkCost w (dfsWalk hT) := by
  have hG := preorder_bound hT w hTri r r
  unfold tourCostTo
  rw [dfsTour_head hT]
  have hne : dfsTour hT ≠ [] := dfsTour_ne_nil hT
  simp [hne]
  rw [dfsTour_last hT]
  have hG' : pathCost w (dfsTour hT) + w (preorderLast hT r) r ≤ walkCost w (dfsWalk hT) + w r r := by
    simpa [dfsTour, dfsWalk, walkCost] using hG
  have hloop := hLoop r
  calc
    pathCost w (dfsTour hT) + w (preorderLast hT r) r ≤ walkCost w (dfsWalk hT) + w r r := hG'
    _ = walkCost w (dfsWalk hT) := by simp [hloop]

/--
**Theorem 35.2.**  APPROX-TSP-TOUR returns a tour whose cost is at most twice the
cost of any tour — in particular, of an optimal one.

Indeed, the preorder tour costs no more than the depth-first walk (Lemma
`dfsTour_bound`), the walk costs exactly twice the tree (Lemma 35.2,
`dfsWalk_cost`), and a minimum spanning tree costs no more than any tour (Lemma
35.3, `mst_le_tour`).
-/
theorem tsp_two_approx {w : Graph V} {p : V → V} {r : V}
    (hMST : IsMinimumSpanningTreeOn w p r)
    (hSymm : ∀ x y : V, w x y = w y x)
    (hTri : ∀ a b c : V, w a c ≤ w a b + w b c)
    (hLoop : ∀ v : V, w v v = 0)
    {σ : V → V} (hT : Tour σ) :
    tourCostTo w ((dfsTour hMST.1).head (dfsTour_ne_nil hMST.1)) (dfsTour hMST.1) ≤ 2 * TourCost w σ := by
  have h1 := dfsTour_bound hMST.1 w hTri hLoop
  have h2 := dfsWalk_cost hMST.1 w hSymm
  have h3 := mst_le_tour hMST hT
  calc
    tourCostTo w ((dfsTour hMST.1).head (dfsTour_ne_nil hMST.1)) (dfsTour hMST.1) ≤ walkCost w (dfsWalk hMST.1) := h1
    _ = 2 * treeCost w p r := h2
    _ ≤ 2 * TourCost w σ := by exact Nat.mul_le_mul_left 2 h3


end TreeOn

end TSP

end CLRS
