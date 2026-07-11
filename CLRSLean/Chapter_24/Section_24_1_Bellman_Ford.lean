import Mathlib

/-!
# 24.1. The Bellman-Ford algorithm

This section opens Chapter 24 (single-source shortest paths).  It defines a
finite weighted directed graph, walks and their weights, the single-source
shortest-path distance {lit}`δ(s, ·)`, and the Bellman-Ford
relaxation dynamic program.  It then proves that the relaxation values are exact
shortest-path distances after {lit}`|V| - 1` rounds when the graph has no
negative-weight cycle, and packages the classic {lit}`O(V·E)` work count.

Main results:

- {lit}`CLRS.Chapter24.WeightedGraph`: a finite weighted directed graph as an edge
  {lit}`Finset` plus a real weight function.
- {lit}`CLRS.Chapter24.WeightedGraph.relaxDist`: the Bellman-Ford relaxation after
  {lit}`k` synchronous rounds, valued in {lit}`WithTop ℝ` ({lit}`⊤` = unreachable).
- {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_le_walkWeight`: relaxation is a lower
  bound for the weight of every walk with at most {lit}`k` edges (the upper-bound
  property).
- {lit}`CLRS.Chapter24.WeightedGraph.exists_walk_of_relaxDist`: every finite
  relaxation value is attained by an actual walk (realizability).
- {lit}`CLRS.Chapter24.WeightedGraph.exists_simple_le`: with no negative-weight
  cycle, any walk shortens to a simple path of no larger weight (cycle removal).
- {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist`: **CLRS
  Theorem 24.4** — with no negative-weight cycle, {lit}`relaxDist (|V|-1)` is the
  single-source shortest-path distance, characterized by {lit}`IsShortestDist`.
- {lit}`CLRS.Chapter24.WeightedGraph.bellmanFordWork_le`: the {lit}`(|V|-1)·|E|` work
  bound ({lit}`O(V·E)`).

Notation conventions used in this section:

- {lit}`G` : a {lit}`WeightedGraph`
- {lit}`s` : the source vertex
- {lit}`w u v` : the weight of edge {lit}`(u, v)`
- {lit}`relaxDist k v` : shortest-path estimate at {lit}`v` after {lit}`k` rounds
- {lit}`⊤` : {lit}`+∞`, i.e. no walk found yet

The relaxation is modelled synchronously: one round relaxes every edge once, in
parallel.  This is the standard "for {lit}`i` in {lit}`1..|V|-1`, relax all edges" model
and is faithful to CLRS at the abstract-cost layer used throughout the graph
track; per-edge ordering and RAM write accounting are a separate refinement.
-/

namespace CLRS
namespace Chapter24

open Finset

/-- A finite weighted directed graph: a finite set of directed edges together
with a real-valued weight function.  Only the weights of actual edges are used;
{lit}`w` is total for convenience (junk values off the edge set are never read). -/
structure WeightedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The directed edges of the graph. -/
  edges : Finset (V × V)
  /-- The weight of a directed edge {lit}`(u, v)`. -/
  w : V → V → ℝ

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-- Directed adjacency: there is an edge from {lit}`u` to {lit}`v`. -/
def Adj (u v : V) : Prop := (u, v) ∈ G.edges

instance : DecidableRel G.Adj := fun u v => by
  unfold WeightedGraph.Adj; infer_instance

/-- The predecessors of {lit}`v`: all {lit}`u` with an edge {lit}`u → v`. -/
def preds (v : V) : Finset V := Finset.univ.filter (fun u => (u, v) ∈ G.edges)

@[simp] theorem mem_preds {u v : V} : u ∈ G.preds v ↔ (u, v) ∈ G.edges := by
  simp [preds]

/-! ## Walks and their weights -/

section
omit [Fintype V] [DecidableEq V]

/-- The weight of a vertex list, i.e. the sum of the edge weights of consecutive
pairs.  A single vertex or the empty list has weight {lit}`0`. -/
def walkWeight (w : V → V → ℝ) : List V → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => w a b + walkWeight w (b :: t)

@[simp] theorem walkWeight_singleton (w : V → V → ℝ) (a : V) :
    walkWeight w [a] = 0 := rfl

@[simp] theorem walkWeight_cons_cons (w : V → V → ℝ) (a b : V) (t : List V) :
    walkWeight w (a :: b :: t) = w a b + walkWeight w (b :: t) := rfl

/-- Weight of a walk that ends with the edge {lit}`(u, v)`: peel off the last edge. -/
theorem walkWeight_concat (w : V → V → ℝ) (q : List V) (u v : V) :
    walkWeight w (q ++ [u, v]) = walkWeight w (q ++ [u]) + w u v := by
  induction q with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.cons_append] at ih ⊢
      rw [walkWeight_cons_cons, walkWeight_cons_cons, ih]
      ring

end

/-- {lit}`p` is a walk from {lit}`s` to {lit}`v` in {lit}`G`: a chain of edges whose head is {lit}`s` and
whose last vertex is {lit}`v`. -/
structure IsWalkFrom (s v : V) (p : List V) : Prop where
  /-- Consecutive vertices are joined by edges. -/
  chain : List.IsChain G.Adj p
  /-- The walk starts at the source {lit}`s`. -/
  head : p.head? = some s
  /-- The walk ends at {lit}`v`. -/
  last : p.getLast? = some v

theorem IsWalkFrom.ne_nil {s v : V} {p : List V} (h : G.IsWalkFrom s v p) : p ≠ [] := by
  rintro rfl
  simpa using h.head

/-! ## The Bellman-Ford relaxation dynamic program -/

/-- One synchronous relaxation round: relax every incoming edge of every vertex.
{lit}`relaxStep d v = min (d v) (min over predecessors u of (d u + w u v))`. -/
def relaxStep (d : V → WithTop ℝ) : V → WithTop ℝ :=
  fun v => min (d v) ((G.preds v).inf (fun u => d u + (G.w u v : WithTop ℝ)))

/-- Bellman-Ford after {lit}`k` rounds from source {lit}`s`.  Round {lit}`0` places {lit}`0` at the
source and {lit}`⊤` elsewhere; each further round applies {lit}`relaxStep`. -/
def relaxDist (G : WeightedGraph V) (s : V) : ℕ → V → WithTop ℝ
  | 0 => fun v => if v = s then (0 : WithTop ℝ) else ⊤
  | (k + 1) => G.relaxStep (G.relaxDist s k)

@[simp] theorem relaxDist_zero_eq (s : V) :
    G.relaxDist s 0 = fun v => if v = s then (0 : WithTop ℝ) else ⊤ := rfl

@[simp] theorem relaxDist_succ_eq (s : V) (k : ℕ) :
    G.relaxDist s (k + 1) = G.relaxStep (G.relaxDist s k) := rfl

theorem relaxDist_zero_apply (s v : V) :
    G.relaxDist s 0 v = if v = s then (0 : WithTop ℝ) else ⊤ := by
  rw [relaxDist_zero_eq]

theorem relaxDist_succ_apply (s : V) (k : ℕ) (v : V) :
    G.relaxDist s (k + 1) v = G.relaxStep (G.relaxDist s k) v := by
  rw [relaxDist_succ_eq]

theorem relaxDist_zero_self (s : V) : G.relaxDist s 0 s = 0 := by
  rw [relaxDist_zero_apply]; simp

/-- One relaxation round never increases an estimate (the upper-bound property
is monotone). -/
theorem relaxStep_le_self (d : V → WithTop ℝ) (v : V) : G.relaxStep d v ≤ d v := by
  simp only [relaxStep]; exact min_le_left _ _

/-- One relaxation round respects every edge: {lit}`relaxStep d v ≤ d u + w u v`. -/
theorem relaxStep_le_pred {d : V → WithTop ℝ} {u v : V} (h : (u, v) ∈ G.edges) :
    G.relaxStep d v ≤ d u + (G.w u v : WithTop ℝ) := by
  simp only [relaxStep]
  exact le_trans (min_le_right _ _) (Finset.inf_le (by simpa [mem_preds] using h))

/-- Bellman-Ford estimates are monotone nonincreasing in the round count. -/
theorem relaxDist_succ_le (s : V) (k : ℕ) (v : V) :
    G.relaxDist s (k + 1) v ≤ G.relaxDist s k v := by
  rw [relaxDist_succ_apply]; exact G.relaxStep_le_self (G.relaxDist s k) v

/-- **Upper-bound property.**  After {lit}`k` rounds the estimate at {lit}`v` is at most
the weight of any walk from {lit}`s` to {lit}`v` using at most {lit}`k` edges. -/
theorem relaxDist_le_walkWeight (s : V) :
    ∀ (k : ℕ) (v : V) (p : List V), G.IsWalkFrom s v p → p.length ≤ k + 1 →
      G.relaxDist s k v ≤ (walkWeight G.w p : WithTop ℝ) := by
  intro k
  induction k with
  | zero =>
    intro v p hp hlen
    have hne := hp.ne_nil
    obtain ⟨x, rfl⟩ : ∃ x, p = [x] := by
      rcases p with _ | ⟨a, _ | ⟨b, tl⟩⟩
      · exact absurd rfl hne
      · exact ⟨a, rfl⟩
      · simp only [List.length_cons] at hlen; omega
    have hxs : x = s := by simpa using hp.head
    have hxv : x = v := by simpa using hp.last
    subst hxs; subst hxv
    simp [relaxDist_zero_apply]
  | succ k ih =>
    intro v p hp hlen
    by_cases hshort : p.length ≤ k + 1
    · exact le_trans (G.relaxDist_succ_le s k v) (ih v p hp hshort)
    · have hlong : k + 1 < p.length := not_le.mp hshort
      have hne : p ≠ [] := hp.ne_nil
      have hlast : p.getLast hne = v := by
        have := hp.last
        rw [List.getLast?_eq_some_getLast hne] at this
        exact Option.some.inj this
      have hsplit : p = p.dropLast ++ [v] := by
        conv_lhs => rw [← List.dropLast_append_getLast hne]
        rw [hlast]
      have hdl_ne : p.dropLast ≠ [] := by
        intro hcontra
        have : p.length ≤ 1 := by rw [hsplit, hcontra]; simp
        omega
      set q := p.dropLast with hq
      obtain ⟨u, hu⟩ : ∃ u, q.getLast? = some u := by
        rw [List.getLast?_eq_some_getLast hdl_ne]; exact ⟨_, rfl⟩
      have hchain : List.IsChain G.Adj (q ++ [v]) := by rw [← hsplit]; exact hp.chain
      have happ := List.isChain_append.1 hchain
      have hedge : G.Adj u v :=
        happ.2.2 u (Option.mem_def.mpr hu) v (Option.mem_def.mpr (by simp))
      have hqhead : q.head? = some s := by
        have hph := hp.head
        rw [hsplit, List.head?_append_of_ne_nil _ hdl_ne] at hph
        exact hph
      have hqchain : List.IsChain G.Adj q := happ.1
      have hqwalk : G.IsWalkFrom s u q := ⟨hqchain, hqhead, hu⟩
      have hqlen : q.length ≤ k + 1 := by
        have hpq : p.length = q.length + 1 := by rw [hsplit]; simp
        omega
      -- reconstruct p = q.dropLast ++ [u, v]
      have hgl : q.getLast hdl_ne = u := by
        have := List.getLast?_eq_some_getLast hdl_ne
        rw [hu] at this
        exact (Option.some.inj this).symm
      have hq_split : q = q.dropLast ++ [u] := by
        conv_lhs => rw [← List.dropLast_append_getLast hdl_ne]
        rw [hgl]
      have hp_uv : p = q.dropLast ++ [u, v] := by
        rw [hsplit]
        conv_lhs => rw [hq_split]
        simp
      have hweight : walkWeight G.w p = walkWeight G.w q + G.w u v := by
        rw [hp_uv, walkWeight_concat, ← hq_split]
      have hIH : G.relaxDist s k u ≤ (walkWeight G.w q : WithTop ℝ) := ih u q hqwalk hqlen
      rw [relaxDist_succ_apply]
      calc G.relaxStep (G.relaxDist s k) v
          ≤ G.relaxDist s k u + (G.w u v : WithTop ℝ) := G.relaxStep_le_pred hedge
        _ ≤ (walkWeight G.w q : WithTop ℝ) + (G.w u v : WithTop ℝ) := by gcongr
        _ = (walkWeight G.w p : WithTop ℝ) := by rw [hweight]; push_cast; ring

omit [Fintype V] [DecidableEq V] in
/-- Weight of a nonempty walk extended by one vertex {lit}`v`. -/
theorem walkWeight_append_singleton (w : V → V → ℝ) (q : List V) (hq : q ≠ []) (v : V) :
    walkWeight w (q ++ [v]) = walkWeight w q + w (q.getLast hq) v := by
  have h1 : q ++ [v] = q.dropLast ++ [q.getLast hq, v] := by
    rw [show ([q.getLast hq, v] : List V) = [q.getLast hq] ++ [v] from rfl, ← List.append_assoc,
      List.dropLast_append_getLast hq]
  rw [h1, walkWeight_concat, List.dropLast_append_getLast hq]

/-- **Realizability.**  Every finite relaxation value after {lit}`k` rounds is the
weight of an actual walk from {lit}`s` using at most {lit}`k` edges. -/
theorem exists_walk_of_relaxDist (s : V) :
    ∀ (k : ℕ) (v : V), G.relaxDist s k v = ⊤ ∨
      ∃ p, G.IsWalkFrom s v p ∧ p.length ≤ k + 1 ∧
        (walkWeight G.w p : WithTop ℝ) = G.relaxDist s k v := by
  intro k
  induction k with
  | zero =>
    intro v
    by_cases hv : v = s
    · subst hv
      right
      exact ⟨[v], ⟨List.isChain_singleton v, by simp, by simp⟩, by simp,
        by simp [relaxDist_zero_apply]⟩
    · left
      rw [relaxDist_zero_apply]; simp [hv]
  | succ k ih =>
    intro v
    have hstep : G.relaxDist s (k + 1) v =
        min (G.relaxDist s k v)
          ((G.preds v).inf (fun u => G.relaxDist s k u + (G.w u v : WithTop ℝ))) := by
      rw [relaxDist_succ_apply]; rfl
    rcases min_choice (G.relaxDist s k v)
        ((G.preds v).inf (fun u => G.relaxDist s k u + (G.w u v : WithTop ℝ))) with hmin | hmin
    · rw [hstep, hmin]
      rcases ih v with htop | ⟨p, hp, hplen, hpw⟩
      · left; exact htop
      · right; exact ⟨p, hp, by omega, hpw⟩
    · rw [hstep, hmin]
      by_cases hBtop :
          (G.preds v).inf (fun u => G.relaxDist s k u + (G.w u v : WithTop ℝ)) = ⊤
      · left; exact hBtop
      · right
        have hne : (G.preds v).Nonempty := by
          rcases (G.preds v).eq_empty_or_nonempty with he | hne
          · rw [he] at hBtop; simp at hBtop
          · exact hne
        obtain ⟨u, hu_mem, hu_eq⟩ := Finset.exists_mem_eq_inf (G.preds v) hne
          (fun u => G.relaxDist s k u + (G.w u v : WithTop ℝ))
        have hedge : (u, v) ∈ G.edges := by simpa [mem_preds] using hu_mem
        have hutop : G.relaxDist s k u ≠ ⊤ := by
          intro h
          apply hBtop
          rw [hu_eq, h, WithTop.top_add]
        rcases ih u with htop | ⟨q, hq, hqlen, hqw⟩
        · exact absurd htop hutop
        · have hqne : q ≠ [] := hq.ne_nil
          have hgl : q.getLast hqne = u := by
            have := List.getLast?_eq_some_getLast hqne
            rw [hq.last] at this
            exact (Option.some.inj this).symm
          refine ⟨q ++ [v], ?_, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · refine List.IsChain.append hq.chain (List.isChain_singleton v) ?_
              intro x hx y hy
              have hxu : x = u := by
                rw [Option.mem_def, hq.last] at hx
                exact (Option.some.inj hx).symm
              have hyv : y = v := Eq.symm (by simpa using hy)
              subst hxu; subst hyv
              exact hedge
            · rw [List.head?_append_of_ne_nil _ hqne]; exact hq.head
            · simp
          · simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · rw [hu_eq, walkWeight_append_singleton G.w q hqne v, hgl]
            push_cast
            rw [hqw]

/-! ## No negative cycles and cycle removal -/

/-- {lit}`G` has no negative-weight cycle: every closed walk has nonnegative weight.
This is CLRS's hypothesis under which shortest paths (and Bellman-Ford) are
well defined; a negative closed walk would contain a negative cycle. -/
def NoNegCycle : Prop := ∀ (x : V) (c : List V), G.IsWalkFrom x x c → 0 ≤ walkWeight G.w c

omit [Fintype V] [DecidableEq V] in
/-- Weight of a walk splits at any interior vertex {lit}`x`. -/
theorem walkWeight_split (w : V → V → ℝ) (l₁ : List V) (x : V) (l₂ : List V) :
    walkWeight w (l₁ ++ x :: l₂) = walkWeight w (l₁ ++ [x]) + walkWeight w (x :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest' =>
      simp only [List.cons_append] at ih ⊢
      rw [walkWeight_cons_cons, walkWeight_cons_cons, ih]
      ring

omit [Fintype V] in
/-- A list that is not {lit}`Nodup` has a vertex appearing twice, exposing the
enclosed cycle. -/
theorem exists_dup_decomp : ∀ {l : List V}, ¬ l.Nodup →
    ∃ (a : V) (l₁ l₂ l₃ : List V), l = l₁ ++ a :: l₂ ++ a :: l₃ := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b t ih =>
    intro h
    by_cases hb : b ∈ t
    · obtain ⟨l₂, l₃, ht⟩ := List.mem_iff_append.mp hb
      exact ⟨b, [], l₂, l₃, by rw [ht]; simp⟩
    · have hnt : ¬ t.Nodup := fun htn => h (List.nodup_cons.mpr ⟨hb, htn⟩)
      obtain ⟨a, l₁, l₂, l₃, ht⟩ := ih hnt
      exact ⟨a, b :: l₁, l₂, l₃, by rw [ht]; simp⟩

/-- **Cycle removal.**  With no negative cycle, every walk from {lit}`s` to {lit}`v` can
be shortened to a simple (repetition-free) path of no larger weight. -/
theorem exists_simple_le (hNC : G.NoNegCycle) (s v : V) :
    ∀ (n : ℕ) (p : List V), p.length ≤ n → G.IsWalkFrom s v p →
      ∃ q, G.IsWalkFrom s v q ∧ q.Nodup ∧ walkWeight G.w q ≤ walkWeight G.w p := by
  intro n
  induction n with
  | zero =>
    intro p hlen hp
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hp.ne_nil
  | succ n ih =>
    intro p hlen hp
    by_cases hnd : p.Nodup
    · exact ⟨p, hp, hnd, le_refl _⟩
    · obtain ⟨x, l₁, l₂, l₃, ht⟩ := exists_dup_decomp hnd
      -- chains of the pieces
      have hc_l1x2 : List.IsChain G.Adj (l₁ ++ (x :: l₂)) :=
        hp.chain.prefix ⟨x :: l₃, ht.symm⟩
      have hc1 : List.IsChain G.Adj l₁ := hc_l1x2.left_of_append
      have hc2 : List.IsChain G.Adj (x :: l₃) :=
        hp.chain.suffix ⟨l₁ ++ (x :: l₂), ht.symm⟩
      have hchain' : List.IsChain G.Adj (l₁ ++ x :: l₃) := by
        refine hc1.append hc2 ?_
        intro a ha b hb
        have hbx : b = x := (show x = b by simpa using hb).symm
        rw [hbx]
        exact (List.isChain_append.1 hc_l1x2).2.2 a ha x (by simp)
      -- head and last of the shortened walk
      have hhead' : (l₁ ++ x :: l₃).head? = some s := by
        have hh : (l₁ ++ x :: l₃).head? = p.head? := by
          rw [ht]; cases l₁ <;> simp
        rw [hh]; exact hp.head
      have hlast' : (l₁ ++ x :: l₃).getLast? = some v := by
        have hxl3 : (x :: l₃).getLast? = some v := by
          have hpe : p = (l₁ ++ x :: l₂) ++ (x :: l₃) := ht
          have hl := hp.last
          rw [hpe, List.getLast?_append_of_ne_nil _ (by simp : (x :: l₃) ≠ [])] at hl
          exact hl
        rw [List.getLast?_append_of_ne_nil _ (by simp : (x :: l₃) ≠ [])]
        exact hxl3
      have hp' : G.IsWalkFrom s v (l₁ ++ x :: l₃) := ⟨hchain', hhead', hlast'⟩
      -- the enclosed cycle from {lit}`x` to {lit}`x`
      have hcyc_walk : G.IsWalkFrom x x ((x :: l₂) ++ [x]) := by
        refine ⟨?_, ?_, ?_⟩
        · refine hp.chain.infix ⟨l₁, l₃, ?_⟩
          rw [ht]; simp [List.append_assoc]
        · rw [List.cons_append]; rfl
        · exact List.getLast?_concat
      have hcyc : (0 : ℝ) ≤ walkWeight G.w ((x :: l₂) ++ [x]) := hNC x _ hcyc_walk
      -- weight decomposition
      have hwp : walkWeight G.w p
          = walkWeight G.w (l₁ ++ [x]) + walkWeight G.w ((x :: l₂) ++ [x])
            + walkWeight G.w (x :: l₃) := by
        have e2 : (l₁ ++ (x :: l₂)) ++ [x] = l₁ ++ x :: (l₂ ++ [x]) := by simp
        have e3 : x :: (l₂ ++ [x]) = (x :: l₂) ++ [x] := by simp
        rw [ht, walkWeight_split G.w (l₁ ++ (x :: l₂)) x l₃, e2,
            walkWeight_split G.w l₁ x (l₂ ++ [x]), e3]
      have hwp' : walkWeight G.w (l₁ ++ x :: l₃)
          = walkWeight G.w (l₁ ++ [x]) + walkWeight G.w (x :: l₃) :=
        walkWeight_split G.w l₁ x l₃
      have hle : walkWeight G.w (l₁ ++ x :: l₃) ≤ walkWeight G.w p := by
        rw [hwp, hwp']; linarith
      -- the shortened walk is strictly shorter, so induction applies
      have hlp : p.length = l₁.length + l₂.length + l₃.length + 2 := by
        rw [ht]; simp only [List.length_append, List.length_cons]; omega
      have hlp' : (l₁ ++ x :: l₃).length = l₁.length + l₃.length + 1 := by
        simp only [List.length_append, List.length_cons]; omega
      have hlen' : (l₁ ++ x :: l₃).length ≤ n := by omega
      obtain ⟨q, hq, hqnd, hqle⟩ := ih (l₁ ++ x :: l₃) hlen' hp'
      exact ⟨q, hq, hqnd, le_trans hqle hle⟩

/-! ## Correctness of Bellman-Ford (CLRS Theorem 24.4) -/

/-- {lit}`d` is the single-source shortest-path distance {lit}`δ(s, v)`: it lower-bounds
every walk weight, and is either {lit}`⊤` (no walk exists) or attained by a walk.
These are exactly CLRS's defining properties of {lit}`δ`. -/
def IsShortestDist (s v : V) (d : WithTop ℝ) : Prop :=
  (∀ p, G.IsWalkFrom s v p → d ≤ (walkWeight G.w p : WithTop ℝ)) ∧
    (d = ⊤ ∨ ∃ p, G.IsWalkFrom s v p ∧ (walkWeight G.w p : WithTop ℝ) = d)

/-- **CLRS Theorem 24.4 (correctness of Bellman-Ford).**  With no
negative-weight cycle, the relaxation values after {lit}`|V| - 1` rounds are exactly
the single-source shortest-path distances {lit}`δ(s, ·)`. -/
theorem relaxDist_isShortestDist (hNC : G.NoNegCycle) (s v : V) :
    G.IsShortestDist s v (G.relaxDist s (Fintype.card V - 1) v) := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, hqnd, hqle⟩ := G.exists_simple_le hNC s v p.length p le_rfl hp
    have hqlen : q.length ≤ Fintype.card V := hqnd.length_le_card
    have hle := G.relaxDist_le_walkWeight s (Fintype.card V - 1) v q hq (by omega)
    calc G.relaxDist s (Fintype.card V - 1) v
        ≤ (walkWeight G.w q : WithTop ℝ) := hle
      _ ≤ (walkWeight G.w p : WithTop ℝ) := by exact_mod_cast hqle
  · rcases G.exists_walk_of_relaxDist s (Fintype.card V - 1) v with htop | ⟨p, hp, _, hpw⟩
    · left; exact htop
    · right; exact ⟨p, hp, hpw⟩

/-- **Convergence.**  With no negative cycle, one more relaxation round after
{lit}`|V| - 1` changes nothing: the estimates have stabilized at {lit}`δ`. -/
theorem relaxDist_stabilizes (hNC : G.NoNegCycle) (s v : V) :
    G.relaxDist s (Fintype.card V) v = G.relaxDist s (Fintype.card V - 1) v := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  refine le_antisymm ?_ ?_
  · have h : Fintype.card V = (Fintype.card V - 1) + 1 := by omega
    rw [h]; exact G.relaxDist_succ_le s (Fintype.card V - 1) v
  · rcases G.exists_walk_of_relaxDist s (Fintype.card V) v with htop | ⟨p, hp, _, hpw⟩
    · rw [htop]; exact le_top
    · rw [← hpw]
      exact (G.relaxDist_isShortestDist hNC s v).1 p hp

/-! ## Work bound: {lit}`O(V·E)` -/

/-- Total Bellman-Ford work: {lit}`|V| - 1` relaxation rounds, each relaxing all
{lit}`|E|` edges once, i.e. {lit}`(|V| - 1) · |E|` edge relaxations. -/
def bellmanFordWork (G : WeightedGraph V) : ℕ := (Fintype.card V - 1) * G.edges.card

/-- **{lit}`O(V·E)` work.**  The {lit}`(|V| - 1) · |E|` edge relaxations are bounded by
{lit}`|V| · |E|`. -/
theorem bellmanFordWork_le : G.bellmanFordWork ≤ Fintype.card V * G.edges.card := by
  unfold bellmanFordWork
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

end WeightedGraph
end Chapter24
end CLRS
