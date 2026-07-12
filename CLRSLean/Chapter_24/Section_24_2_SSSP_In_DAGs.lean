import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 24.2. Single-source shortest paths in directed acyclic graphs

This section formalizes CLRS's {lit}`DAG-SHORTEST-PATHS` algorithm.  On a weighted
**directed acyclic graph** the single-source shortest-path problem is solved in
{lit}`Θ(V + E)` time by a single left-to-right relaxation pass: topologically sort
the vertices, then relax the out-edges of each vertex once, in topological
order.  Because every edge runs from an earlier vertex to a later one, one pass
already produces the exact distances — none of Bellman-Ford's {lit}`|V| - 1` rounds
are needed.

The section reuses the Chapter 24.1 weighted-graph model wholesale: the
{lit}`WeightedGraph` structure, {lit}`walkWeight`, {lit}`IsWalkFrom`, and the
shortest-distance specification {lit}`IsShortestDist`.  Chapter 22.4's topological
order is stated over the unweighted {lit}`Chapter22.Graph`; since Chapter 24 uses
a different structure ({lit}`Chapter24.WeightedGraph`), we **restate** the
topological-order predicate directly over {lit}`WeightedGraph.Adj`.

Main results:

- {lit}`CLRS.Chapter24.WeightedGraph.IsTopoOrder`: a topological order of the
  weighted graph — a duplicate-free list of every vertex in which every directed
  edge runs forward (restatement of {lit}`Chapter22.Graph.IsTopologicalOrder` over
  {lit}`WeightedGraph.Adj`).
- {lit}`CLRS.Chapter24.WeightedGraph.isAcyclic_of_isTopoOrder`: a weighted graph
  admitting a topological order is acyclic (the DAG hypothesis, obtained for
  free from the ordering).
- {lit}`CLRS.Chapter24.WeightedGraph.relaxFrom`: relax all out-edges of a single
  vertex once.
- {lit}`CLRS.Chapter24.WeightedGraph.dagRelax`: fold {lit}`relaxFrom` along a
  topological order, threading the tentative-distance map ({lit}`DAG-SHORTEST-PATHS`).
- {lit}`CLRS.Chapter24.WeightedGraph.dagRelax_respects_edge`: after one pass in
  topological order the distances obey every edge constraint {lit}`d v ≤ d u + w u v`.
- {lit}`CLRS.Chapter24.WeightedGraph.dagRelax_isShortestDist`: **the CLRS §24.2
  correctness statement** — the folded distances are exactly the single-source
  shortest-path distances {lit}`δ(s, ·)`, characterized by {lit}`IsShortestDist`.
- {lit}`CLRS.Chapter24.WeightedGraph.sum_outdegree` and
  {lit}`CLRS.Chapter24.WeightedGraph.dagSSSPWork_eq`: the {lit}`|V| + |E|` = {lit}`Θ(V + E)`
  work bound — one pass touches each vertex once and each edge once.

Notation conventions used in this section:

- {lit}`G` : a {lit}`WeightedGraph`
- {lit}`s` : the source vertex
- {lit}`order` : a topological order of {lit}`G`'s vertices
- {lit}`d v` : the tentative shortest-path estimate at {lit}`v`, valued in {lit}`WithTop ℝ`
- {lit}`⊤` : {lit}`+∞`, i.e. no walk found yet
-/

namespace CLRS
namespace Chapter24

open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Topological order and acyclicity over the weighted graph -/

/-- A topological order of the weighted graph {lit}`G`: a duplicate-free list that
contains every vertex, in which every directed edge {lit}`u → v` runs forward
(the source occurs strictly before the target).  This restates
{lit}`Chapter22.Graph.IsTopologicalOrder` over {name}`CLRS.Chapter24.WeightedGraph.Adj`,
whose vertex set is all of the finite type {lit}`V`. -/
def IsTopoOrder (G : WeightedGraph V) (order : List V) : Prop :=
  order.Nodup ∧ (∀ v : V, v ∈ order) ∧
    (∀ u v : V, G.Adj u v → order.idxOf u < order.idxOf v)

/-- A weighted graph is acyclic when no vertex reaches itself by a nontrivial
directed path.  This mirrors {lit}`Chapter22.Graph.IsDAG`. -/
def IsAcyclic (G : WeightedGraph V) : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The finish-index of an edge strictly increases along a topological order,
hence so does the index along any directed path (transitive closure). -/
theorem idxOf_lt_of_transGen {order : List V} (hlt : ∀ u v : V, G.Adj u v →
    order.idxOf u < order.idxOf v) {a b : V} (h : Relation.TransGen G.Adj a b) :
    order.idxOf a < order.idxOf b := by
  induction h with
  | single hab => exact hlt _ _ hab
  | tail _ hbc ih => exact lt_trans ih (hlt _ _ hbc)

/-- **The DAG hypothesis, for free.**  Any weighted graph that admits a
topological order is acyclic: a directed cycle would force a vertex index to be
strictly less than itself. -/
theorem isAcyclic_of_isTopoOrder {order : List V} (hTopo : G.IsTopoOrder order) :
    G.IsAcyclic := by
  intro v hv
  exact absurd (G.idxOf_lt_of_transGen hTopo.2.2 hv) (lt_irrefl _)

omit [Fintype V] in
/-- A purely combinatorial fact used to prove correctness: in a duplicate-free
list split as {lit}`pre ++ u :: suf`, every vertex of {lit}`suf` occurs strictly after
{lit}`u`. -/
theorem idxOf_lt_of_split {order pre suf : List V} {u x : V}
    (hnd : order.Nodup) (hsplit : order = pre ++ u :: suf) (hx : x ∈ suf) :
    order.idxOf u < order.idxOf x := by
  subst hsplit
  have hdisj : pre.Disjoint (u :: suf) := List.disjoint_of_nodup_append hnd
  have hu_pre : u ∉ pre := fun h => hdisj h (List.mem_cons.2 (Or.inl rfl))
  have hx_pre : x ∉ pre := fun h => hdisj h (List.mem_cons.2 (Or.inr hx))
  have hu_suf : u ∉ suf := (List.nodup_cons.mp (List.Nodup.of_append_right hnd)).1
  have hxu : x ≠ u := fun h => hu_suf (h ▸ hx)
  rw [List.idxOf_append_of_notMem hu_pre, List.idxOf_append_of_notMem hx_pre,
    List.idxOf_cons_self, List.idxOf_cons_ne suf hxu.symm]
  omega

/-! ## Single-vertex out-edge relaxation -/

/-- Relax every out-edge of {lit}`u` once: for each edge {lit}`u → v`, lower the estimate
{lit}`d v` to {lit}`d u + w u v`.  Vertices with no edge from {lit}`u` are left unchanged
(the {lit}`⊤` branch is absorbed by {lit}`min`). -/
def relaxFrom (d : V → WithTop ℝ) (u : V) : V → WithTop ℝ :=
  fun v => min (d v) (if G.Adj u v then d u + (G.w u v : WithTop ℝ) else ⊤)

@[simp] theorem relaxFrom_apply (d : V → WithTop ℝ) (u v : V) :
    G.relaxFrom d u v = min (d v) (if G.Adj u v then d u + (G.w u v : WithTop ℝ) else ⊤) :=
  rfl

/-- One out-edge relaxation never increases an estimate. -/
theorem relaxFrom_le (d : V → WithTop ℝ) (u v : V) : G.relaxFrom d u v ≤ d v := by
  rw [relaxFrom_apply]; exact min_le_left _ _

/-! ## The topological-order relaxation pass -/

/-- {lit}`DAG-SHORTEST-PATHS`: initialize the source to {lit}`0` and every other vertex to
{lit}`⊤`, then fold {lit}`relaxFrom` along the topological order, relaxing the out-edges
of each vertex exactly once. -/
def dagRelax (G : WeightedGraph V) (s : V) (order : List V) : V → WithTop ℝ :=
  order.foldl (fun d u => G.relaxFrom d u) (fun v => if v = s then (0 : WithTop ℝ) else ⊤)

theorem dagRelax_def (s : V) (order : List V) :
    G.dagRelax s order =
      order.foldl (fun d u => G.relaxFrom d u)
        (fun v => if v = s then (0 : WithTop ℝ) else ⊤) := rfl

/-- Folding {lit}`relaxFrom` along any list only lowers estimates. -/
theorem foldl_relaxFrom_le :
    ∀ (l : List V) (d : V → WithTop ℝ) (v : V),
      l.foldl (fun d u => G.relaxFrom d u) d v ≤ d v := by
  intro l
  induction l with
  | nil => intro d v; simp
  | cons u l ih =>
    intro d v
    simp only [List.foldl_cons]
    exact le_trans (ih (G.relaxFrom d u) v) (G.relaxFrom_le d u v)

/-- If no vertex of {lit}`l` has an edge into {lit}`t`, folding {lit}`relaxFrom` along {lit}`l`
leaves the estimate at {lit}`t` unchanged. -/
theorem foldl_relaxFrom_eq_of_no_pred (t : V) :
    ∀ (l : List V) (d : V → WithTop ℝ), (∀ x ∈ l, ¬ G.Adj x t) →
      l.foldl (fun d u => G.relaxFrom d u) d t = d t := by
  intro l
  induction l with
  | nil => intro d _; simp
  | cons u l ih =>
    intro d h
    simp only [List.foldl_cons]
    have hut : ¬ G.Adj u t := h u (List.mem_cons.2 (Or.inl rfl))
    have hstep : G.relaxFrom d u t = d t := by
      rw [relaxFrom_apply, if_neg hut]; exact min_eq_left le_top
    rw [ih (G.relaxFrom d u) (fun x hx => h x (List.mem_cons.2 (Or.inr hx))), hstep]

/-- **Each edge is respected after one pass.**  For a topological order and any
edge {lit}`u → v`, the folded distances satisfy {lit}`d v ≤ d u + w u v`.

The key structural facts: splitting {lit}`order = pre ++ u :: suf`, the estimate at
{lit}`u` is already final when {lit}`u` is processed (no later vertex has an edge into
{lit}`u`), while processing {lit}`u` lowers {lit}`d v` to at most {lit}`d u + w u v`, and later
steps only lower it further. -/
theorem dagRelax_respects_edge (s : V) {order : List V}
    (hTopo : G.IsTopoOrder order) {u v : V} (hedge : G.Adj u v) :
    G.dagRelax s order v ≤ G.dagRelax s order u + (G.w u v : WithTop ℝ) := by
  obtain ⟨hnd, hmem, hlt⟩ := hTopo
  obtain ⟨pre, suf, hsplit⟩ := List.mem_iff_append.mp (hmem u)
  -- no later vertex points back into u, and u has no self-loop
  have hnusuf : ∀ x ∈ suf, ¬ G.Adj x u := by
    intro x hx hadjxu
    have h2 := idxOf_lt_of_split hnd hsplit hx
    have h1 := hlt x u hadjxu
    omega
  have hnuu : ¬ G.Adj u u := fun h => absurd (hlt u u h) (lt_irrefl _)
  -- decompose the fold at u
  have hdecomp : G.dagRelax s order =
      suf.foldl (fun d u => G.relaxFrom d u)
        (G.relaxFrom (pre.foldl (fun d u => G.relaxFrom d u)
          (fun v => if v = s then (0 : WithTop ℝ) else ⊤)) u) := by
    rw [dagRelax_def, hsplit, List.foldl_append, List.foldl_cons]
  set d1 := pre.foldl (fun d u => G.relaxFrom d u)
    (fun v => if v = s then (0 : WithTop ℝ) else ⊤) with hd1def
  -- u's estimate is final: processing suf never touches it
  have hDu : G.dagRelax s order u = d1 u := by
    rw [hdecomp, G.foldl_relaxFrom_eq_of_no_pred u suf (G.relaxFrom d1 u) hnusuf,
      relaxFrom_apply, if_neg hnuu, min_eq_left le_top]
  -- v's estimate was lowered past d1 u + w u v when u was processed
  have hDv : G.dagRelax s order v ≤ d1 u + (G.w u v : WithTop ℝ) := by
    rw [hdecomp]
    refine le_trans (G.foldl_relaxFrom_le suf (G.relaxFrom d1 u) v) ?_
    rw [relaxFrom_apply, if_pos hedge]
    exact min_le_right _ _
  rw [hDu]; exact hDv

/-! ## Correctness: the folded distances are the shortest-path distances -/

/-- **Path-relaxation, telescoped.**  If a distance map respects every edge
({lit}`d v ≤ d u + w u v`), then along any walk {lit}`d` telescopes:
{lit}`d b ≤ d a + walkWeight p`.  This is the abstract core of shortest-path
lower bounds. -/
theorem le_add_walkWeight_of_respects {d : V → WithTop ℝ}
    (hresp : ∀ a b, G.Adj a b → d b ≤ d a + (G.w a b : WithTop ℝ)) :
    ∀ (p : List V) (a b : V), G.IsWalkFrom a b p →
      d b ≤ d a + (walkWeight G.w p : WithTop ℝ) := by
  intro p
  induction p with
  | nil => intro a b hw; exact absurd rfl hw.ne_nil
  | cons x rest ih =>
    intro a b hw
    have hxa : x = a := by simpa using hw.head
    cases rest with
    | nil =>
      have hxb : x = b := by simpa using hw.last
      subst hxa; subst hxb; simp
    | cons y t =>
      subst hxa
      have hedge : G.Adj x y := hw.chain.rel_head
      have hchain' : List.IsChain G.Adj (y :: t) := hw.chain.tail
      have hlast' : (y :: t).getLast? = some b := by
        have h := hw.last; rwa [List.getLast?_cons_cons] at h
      have hw' : G.IsWalkFrom y b (y :: t) := ⟨hchain', rfl, hlast'⟩
      have h1 := ih y b hw'
      have h2 := hresp x y hedge
      have hcast : (walkWeight G.w (x :: y :: t) : WithTop ℝ)
          = (G.w x y : WithTop ℝ) + (walkWeight G.w (y :: t) : WithTop ℝ) := by
        rw [walkWeight_cons_cons, WithTop.coe_add]
      calc d b ≤ d y + (walkWeight G.w (y :: t) : WithTop ℝ) := h1
        _ ≤ (d x + (G.w x y : WithTop ℝ)) + (walkWeight G.w (y :: t) : WithTop ℝ) := by
              gcongr
        _ = d x + ((G.w x y : WithTop ℝ) + (walkWeight G.w (y :: t) : WithTop ℝ)) := by
              rw [add_assoc]
        _ = d x + (walkWeight G.w (x :: y :: t) : WithTop ℝ) := by rw [hcast]

/-- {lit}`d` is realizable from {lit}`s`: every finite estimate is the weight of an
actual walk from {lit}`s`.  This is preserved by relaxation and holds initially. -/
def IsRealizable (G : WeightedGraph V) (s : V) (d : V → WithTop ℝ) : Prop :=
  ∀ v, d v = ⊤ ∨ ∃ p, G.IsWalkFrom s v p ∧ (walkWeight G.w p : WithTop ℝ) = d v

/-- The initial estimate map is realizable: the source is reached by the trivial
walk {lit}`[s]`, everything else is {lit}`⊤`. -/
theorem isRealizable_init (s : V) :
    G.IsRealizable s (fun v => if v = s then (0 : WithTop ℝ) else ⊤) := by
  intro v
  by_cases hv : v = s
  · right
    exact ⟨[v], ⟨List.isChain_singleton v, by simp [hv], by simp⟩, by simp [hv]⟩
  · left; simp [hv]

/-- One out-edge relaxation preserves realizability: a newly lowered estimate at
{lit}`v` comes from a realized estimate at {lit}`u` extended by the edge {lit}`u → v`. -/
theorem relaxFrom_isRealizable (s : V) (d : V → WithTop ℝ) (u : V)
    (hd : G.IsRealizable s d) : G.IsRealizable s (G.relaxFrom d u) := by
  intro v
  rw [relaxFrom_apply]
  rcases min_choice (d v) (if G.Adj u v then d u + (G.w u v : WithTop ℝ) else ⊤) with hm | hm
  · rw [hm]; exact hd v
  · rw [hm]
    by_cases hadj : G.Adj u v
    · rw [if_pos hadj]
      by_cases hdu : d u = ⊤
      · left; rw [hdu, WithTop.top_add]
      · rcases hd u with htop | ⟨q, hq, hqw⟩
        · exact absurd htop hdu
        · right
          have hqne : q ≠ [] := hq.ne_nil
          have hgl : q.getLast hqne = u := by
            have hh := List.getLast?_eq_some_getLast hqne
            rw [hq.last] at hh
            exact (Option.some.inj hh).symm
          refine ⟨q ++ [v], ⟨?_, ?_, ?_⟩, ?_⟩
          · refine List.IsChain.append hq.chain (List.isChain_singleton v) ?_
            intro a ha b hb
            have hau : a = u := by
              rw [Option.mem_def, hq.last] at ha
              exact (Option.some.inj ha).symm
            have hbv : b = v := Eq.symm (by simpa using hb)
            subst hau; subst hbv
            exact hadj
          · rw [List.head?_append_of_ne_nil _ hqne]; exact hq.head
          · simp
          · rw [walkWeight_append_singleton G.w q hqne v, hgl]
            push_cast
            rw [hqw]
    · rw [if_neg hadj]; left; rfl

/-- Realizability is preserved by the whole {lit}`relaxFrom` fold. -/
theorem foldl_relaxFrom_isRealizable (s : V) :
    ∀ (l : List V) (d : V → WithTop ℝ), G.IsRealizable s d →
      G.IsRealizable s (l.foldl (fun d u => G.relaxFrom d u) d) := by
  intro l
  induction l with
  | nil => intro d hd; simpa using hd
  | cons u l ih =>
    intro d hd
    simp only [List.foldl_cons]
    exact ih (G.relaxFrom d u) (G.relaxFrom_isRealizable s d u hd)

/-- The output of {lit}`dagRelax` is realizable from {lit}`s`. -/
theorem dagRelax_isRealizable (s : V) (order : List V) :
    G.IsRealizable s (G.dagRelax s order) := by
  rw [dagRelax_def]
  exact G.foldl_relaxFrom_isRealizable s order _ (G.isRealizable_init s)

/-- The source estimate never exceeds {lit}`0`. -/
theorem dagRelax_source_le (s : V) (order : List V) : G.dagRelax s order s ≤ 0 := by
  have h := G.foldl_relaxFrom_le order (fun v => if v = s then (0 : WithTop ℝ) else ⊤) s
  simpa [dagRelax_def] using h

/-- **CLRS §24.2 correctness (DAG-SHORTEST-PATHS).**  For a topological order of
the (necessarily acyclic) weighted graph, the single relaxation pass computes the
exact single-source shortest-path distances: for every vertex {lit}`v`, the folded
estimate {lit}`dagRelax s order v` satisfies {lit}`IsShortestDist s v`, i.e. it equals
{lit}`δ(s, v)`.

The two halves are the lower bound (the estimate is ≤ every walk weight, via the
per-edge upper-bound property telescoped along the walk) and realizability (the
estimate is attained by an actual walk). -/
theorem dagRelax_isShortestDist (s : V) {order : List V}
    (hTopo : G.IsTopoOrder order) (v : V) :
    G.IsShortestDist s v (G.dagRelax s order v) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hresp : ∀ a b, G.Adj a b →
        G.dagRelax s order b ≤ G.dagRelax s order a + (G.w a b : WithTop ℝ) :=
      fun a b hab => G.dagRelax_respects_edge s hTopo hab
    calc G.dagRelax s order v
        ≤ G.dagRelax s order s + (walkWeight G.w p : WithTop ℝ) :=
          G.le_add_walkWeight_of_respects hresp p s v hp
      _ ≤ 0 + (walkWeight G.w p : WithTop ℝ) := by
          have hsrc := G.dagRelax_source_le s order
          gcongr
      _ = (walkWeight G.w p : WithTop ℝ) := by rw [zero_add]
  · rcases G.dagRelax_isRealizable s order v with htop | ⟨p, hp, hpw⟩
    · left; exact htop
    · right; exact ⟨p, hp, hpw⟩

/-! ## Work bound: {lit}`Θ(V + E)` -/

/-- The out-degree of {lit}`u`: the number of edges leaving {lit}`u`. -/
def outdegree (G : WeightedGraph V) (u : V) : ℕ := (G.edges.filter (fun e => e.1 = u)).card

/-- The out-degrees sum to the number of edges: one relaxation pass touches each
edge exactly once. -/
theorem sum_outdegree (G : WeightedGraph V) :
    (∑ u : V, G.outdegree u) = G.edges.card := by
  simp only [outdegree]
  exact (Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ e.1)).symm

/-- Total {lit}`DAG-SHORTEST-PATHS` work: initialize each of the {lit}`|V|` vertices, then
relax each of the {lit}`|E|` edges once. -/
def dagSSSPWork (G : WeightedGraph V) : ℕ := Fintype.card V + G.edges.card

/-- **{lit}`Θ(V + E)` work.**  The total work decomposes as {lit}`|V|` vertex visits plus
{lit}`∑ outdegree = |E|` edge relaxations — each vertex and each edge is touched
exactly once. -/
theorem dagSSSPWork_eq (G : WeightedGraph V) :
    G.dagSSSPWork = Fintype.card V + ∑ u : V, G.outdegree u := by
  rw [dagSSSPWork, sum_outdegree]

/-- The single pass performs at most {lit}`|V| + |E|` operations. -/
theorem dagSSSPWork_le (G : WeightedGraph V) :
    G.dagSSSPWork ≤ Fintype.card V + G.edges.card := le_refl _

end WeightedGraph
end Chapter24
end CLRS
