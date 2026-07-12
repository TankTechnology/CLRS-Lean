import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 25.1. All-pairs shortest paths model

This section formalizes the all-pairs shortest-path problem (Ch25) by reusing the
{lit}`WeightedGraph` model from Chapter 24.  We define the all-pairs distance matrix,
the min-plus matrix product (CLRS's {lit}`EXTEND-SHORTEST-PATHS`), and the repeated-squaring
algorithm {lit}`FASTER-APSP`.  We then prove Lemmas 25.1 and 25.2, which together
establish correctness of the repeated-squaring dynamic program.

Main results:

- {lit}`CLRS.Chapter25.AllPairs.minPlusMul`: the min-plus matrix product.
- {lit}`CLRS.Chapter25.AllPairs.extendShortestPaths`: CLRS EXTEND-SHORTEST-PATHS.
- {lit}`CLRS.Chapter25.AllPairs.fasterAPSP`: CLRS FASTER-APSP (repeated squaring).
- {lit}`CLRS.Chapter25.AllPairs.lemma_25_1`: one step of EXTEND-SHORTEST-PATHS
  computes {lit}`L^(m+1)}` from {lit}`L^(m)}`.
- {lit}`CLRS.Chapter25.AllPairs.L_sq_eq_minPlusMul`: the squaring identity
  {lit}`L^(2m) = L^m ◁ L^m` (**Lemma 25.2**).
- {lit}`CLRS.Chapter25.AllPairs.fasterAPSP_eq_shortestDist`:
  {lit}`FASTER-APSP` equals the all-pairs shortest-path distances.

Notation conventions:

- {lit}`G` : a {lit}`WeightedGraph`
- {lit}`w i j` : the weight of edge ({lit}`i`, {lit}`j`)
- {lit}`L m` : matrix of shortest-path weights using at most {lit}`m` edges
- {lit}`⊤` : {lit}`+∞`, i.e. no walk exists

The section follows CLRS §25.1: the basic structure plus EXTEND-SHORTEST-PATHS and
FASTER-APSP at the abstract-cost layer.  Per-edge ordering and RAM cost refinements
are separate.

**Current gaps:**

- Predecessor matrix {lit}`Π` is not yet formalized.
- Negative-cycle detection (CLRS Theorem 25.3 and Floyd-Warshall in §25.2) is deferred.
-/

namespace CLRS
namespace Chapter25

open Finset
open Chapter24
open Chapter24.WeightedGraph

namespace AllPairs

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Min-plus product and EXTEND-SHORTEST-PATHS -/

/-- The edge-weight matrix {lit}`W`: {lit}`W_ij = w(i,j)` if {lit}`(i,j) ∈ E`, {lit}`0` if {lit}`i = j`,
{lit}`∞` otherwise.  This corresponds to {lit}`L^(1)`, the matrix of shortest paths using
at most one edge. -/
def weightMatrix (i j : V) : WithTop ℝ :=
  if i = j then (0 : WithTop ℝ) else if G.Adj i j then (G.w i j : WithTop ℝ) else ⊤

/-- Min-plus matrix product (CLRS EXTEND-SHORTEST-PATHS kernel):
{lit}`(A ◁ B)_ij = min_{k} (A_ik + B_kj)`. -/
def minPlusMul (A B : V → V → WithTop ℝ) (i j : V) : WithTop ℝ :=
  (Finset.univ : Finset V).inf (fun k => A i k + B k j)

/-- CLRS EXTEND-SHORTEST-PATHS: {lit}`L' = L ◁ W` where {lit}`W` is the edge-weight matrix.
Extends the path-length bound by one edge. -/
def extendShortestPaths (L : V → V → WithTop ℝ) (i j : V) : WithTop ℝ :=
  G.minPlusMul L G.weightMatrix i j

/-! ## The distance sequence L^(m) -/

/-- {lit}`L m` — the matrix of shortest-path weights using at most {lit}`m` edges.
Defined inductively: {lit}`L^0` is the identity ({lit}`0` on diagonal, {lit}`⊤` elsewhere),
and {lit}`L^(m+1) = extendShortestPaths(L^m)`. -/
def L : ℕ → V → V → WithTop ℝ
  | 0, i, j => if i = j then (0 : WithTop ℝ) else ⊤
  | m + 1, i, j => G.extendShortestPaths (G.L m) i j

@[simp]
theorem L_zero (i j : V) : G.L 0 i j = if i = j then (0 : WithTop ℝ) else ⊤ := rfl

@[simp]
theorem L_succ (m : ℕ) (i j : V) : G.L (m + 1) i j = G.extendShortestPaths (G.L m) i j := rfl

/-! ## FASTER-APSP -/

/-- Number of repeated-squaring iterations required: {lit}`⌈log₂(|V|-1)⌉`. -/
def numSquarings : ℕ :=
  let x := Fintype.card V - 1
  if x ≤ 1 then 0 else Nat.log2 (x - 1) + 1

/-- CLRS FASTER-APSP: repeatedly square {lit}`L = L ◁ L` for {lit}`numSquarings` iterations,
starting from the edge-weight matrix {lit}`W`.  After {lit}`⌈log₂(n-1)⌉` squarings the bound
reaches {lit}`n-1`, giving the all-pairs shortest-path distances. -/
def fasterAPSP : V → V → WithTop ℝ :=
  (fun L => G.minPlusMul L L)^[numSquarings] G.weightMatrix

/-! ## Basic algebraic properties of min-plus product -/

/-- The identity matrix {lit}`I` for min-plus multiplication. -/
def identityMatrix (i j : V) : WithTop ℝ := if i = j then (0 : WithTop ℝ) else ⊤

@[simp]
theorem identityMatrix_diag (i : V) : G.identityMatrix i i = (0 : WithTop ℝ) := by
  simp [identityMatrix]

@[simp]
theorem identityMatrix_offdiag {i j : V} (h : i ≠ j) : G.identityMatrix i j = ⊤ := by
  simp [identityMatrix, h]

/-- {lit}`I ◁ M = M`: the identity matrix is a left identity for min-plus multiplication. -/
theorem minPlusMul_identity_left (M : V → V → WithTop ℝ) (i j : V) :
    G.minPlusMul G.identityMatrix M i j = M i j := by
  unfold minPlusMul identityMatrix
  apply le_antisymm
  · calc
      (Finset.univ : Finset V).inf (fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) ≤
        ((fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) i) :=
        Finset.inf_le (Finset.mem_univ i)
      _ = (0 : WithTop ℝ) + M i j := by simp
      _ = M i j := by simp
  · refine Finset.le_inf (fun k hk => ?_)
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]

/-- {lit}`M ◁ I = M`: the identity matrix is a right identity for min-plus multiplication. -/
theorem minPlusMul_identity_right (M : V → V → WithTop ℝ) (i j : V) :
    G.minPlusMul M G.identityMatrix i j = M i j := by
  unfold minPlusMul identityMatrix
  apply le_antisymm
  · calc
      (Finset.univ : Finset V).inf (fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) ≤
        ((fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) j) :=
        Finset.inf_le (Finset.mem_univ j)
      _ = M i j + (0 : WithTop ℝ) := by simp
      _ = M i j := by simp
  · refine Finset.le_inf (fun k hk => ?_)
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj]

/-! ## Relating the min-plus product to the Bellman-Ford relaxation -/

/-- The relaxation step can be expressed as the {lit}`Finset.univ` infimum against the
edge-weight matrix, matching the min-plus product. -/
theorem relaxStep_eq_minPlusMul_weightMatrix (d : V → WithTop ℝ) (v : V) :
    G.relaxStep d v = (Finset.univ : Finset V).inf (fun k => d k + G.weightMatrix k v) := by
  unfold relaxStep weightMatrix
  simp [preds]
  -- Now goal: min (d v) ((univ.filter (λ u => (u,v) ∈ edges)).inf (λ u => d u + w u v)) =
  --          (univ).inf (λ k => d k + (if k=v then 0 else if (k,v) ∈ edges then w k v else ⊤))
  apply le_antisymm
  · -- LHS ≤ RHS: for each k, show LHS ≤ RHS term
    refine le_trans ?_ (Finset.le_inf (fun k hk => ?_))
    · exact min_le_left _ _
    by_cases hkv : k = v
    · subst k; simp
    · by_cases hedge : (k, v) ∈ G.edges
      · have hmem : k ∈ (Finset.univ : Finset V).filter (fun u : V => (u, v) ∈ G.edges) := by
          simp [hedge]
        calc
          min (d v) (((Finset.univ : Finset V).filter (fun u : V => (u, v) ∈ G.edges)).inf
            (fun u : V => d u + (G.w u v : WithTop ℝ))) ≤
            ((Finset.univ : Finset V).filter (fun u : V => (u, v) ∈ G.edges)).inf
              (fun u : V => d u + (G.w u v : WithTop ℝ)) :=
            min_le_right _ _
          _ ≤ d k + (G.w k v : WithTop ℝ) := Finset.inf_le hmem
          _ = d k + (if (k, v) ∈ G.edges then (G.w k v : WithTop ℝ) else ⊤) := by simp [hedge]
      · simp [hkv, hedge]
  · -- RHS ≤ LHS
    calc
      (Finset.univ : Finset V).inf (fun k : V => d k + (if k = v then (0 : WithTop ℝ)
          else if (k, v) ∈ G.edges then (G.w k v : WithTop ℝ) else ⊤)) ≤
        (fun k : V => d k + (if k = v then (0 : WithTop ℝ)
          else if (k, v) ∈ G.edges then (G.w k v : WithTop ℝ) else ⊤)) v :=
        Finset.inf_le (Finset.mem_univ v)
      _ = d v + (0 : WithTop ℝ) := by simp
      _ = d v := by simp
      _ ≤ min (d v) (((Finset.univ : Finset V).filter (fun u : V => (u, v) ∈ G.edges)).inf
          (fun u : V => d u + (G.w u v : WithTop ℝ))) := by
        simp

/-- {lit}`L(m,i,j) = relaxDist i m j`: the {lit}`L` matrix equals the single-source relaxation
distance from source {lit}`i` after {lit}`m` rounds. -/
theorem L_eq_relaxDist (m : ℕ) (i j : V) : G.L m i j = G.relaxDist i m j := by
  induction' m with m ih generalizing i j
  · simp [L, relaxDist]
  · rw [L_succ, ih, relaxDist_succ_apply, relaxStep_eq_minPlusMul_weightMatrix, extendShortestPaths, minPlusMul]

/-- {lit}`L` lower-bounds the weight of any walk using at most {lit}`m` edges. -/
theorem L_lowerBound (m : ℕ) (i j : V) (p : List V) (hp : G.IsWalkFrom i j p) (hlen : p.length ≤ m + 1) :
    G.L m i j ≤ (walkWeight G.w p : WithTop ℝ) := by
  rw [L_eq_relaxDist]
  exact G.relaxDist_le_walkWeight i m j p hp hlen

/-- Every finite entry of {lit}`L m` is realised by a walk using at most {lit}`m` edges. -/
theorem L_attainable (m : ℕ) (i j : V) : G.L m i j = ⊤ ∨
    ∃ p, G.IsWalkFrom i j p ∧ p.length ≤ m + 1 ∧ (walkWeight G.w p : WithTop ℝ) = G.L m i j := by
  rw [L_eq_relaxDist]
  exact G.exists_walk_of_relaxDist i m j

/-! ## Distributive properties of inf and addition in `WithTop ℝ` -/

/-- Addition distributes over infimum on the right in {lit}`WithTop ℝ`. -/
lemma add_inf_distrib_right (a b c : WithTop ℝ) : (a ⊓ b) + c = (a + c) ⊓ (b + c) := by
  induction c using WithTop.recTopCoe with
  | top => simp
  | coe c =>
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top => simp
      | coe b => simp [inf_eq_min, min_add_add_right]

/-- `x + (s.inf f) = s.inf (fun y => x + f y)` for nonempty `s`. -/
lemma Finset.inf_add_distrib (s : Finset V) (h : s.Nonempty) (f : V → WithTop ℝ) (c : WithTop ℝ) :
    (s.inf f) + c = s.inf (fun x => f x + c) := by
  induction' s using Finset.induction_on with a s ha ih
  · exact absurd h h.not_nonempty
  · rw [Finset.inf_insert, Finset.inf_insert, add_inf_distrib_right]
    have hsn : s.Nonempty := by
      by_contra! hs
      have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst this; simp at ha
    rw [ih hsn]

/-- The two nested infima can be swapped: `inf_u (inf_k f k u) = inf_k (inf_u f k u)`. -/
lemma Finset.inf_inf_comm (f : V → V → WithTop ℝ) :
    ((Finset.univ : Finset V).inf (fun u => (Finset.univ : Finset V).inf (fun k => f k u))) =
    ((Finset.univ : Finset V).inf (fun k => (Finset.univ : Finset V).inf (fun u => f k u))) := by
  -- Both sides equal the inf over the product set
  calc
    ((Finset.univ : Finset V).inf (fun u => (Finset.univ : Finset V).inf (fun k => f k u))) =
      ((Finset.univ : Finset V) ×ˢ (Finset.univ : Finset V)).inf (fun p : V × V => f p.2 p.1) := by
      simp [Finset.inf_product]
    _ = ((Finset.univ : Finset V).inf (fun k => (Finset.univ : Finset V).inf (fun u => f k u))) := by
      simp [Finset.inf_product]

/-- {lit}`L^0 = I`. -/
theorem L_zero_eq_identity (i j : V) : G.L 0 i j = G.identityMatrix i j := by
  simp [L_zero, identityMatrix]

/-- {lit}`L^1 = W`. -/
theorem L_one_eq_weightMatrix (i j : V) : G.L 1 i j = G.weightMatrix i j := by
  rw [L_succ, extendShortestPaths, L_zero_eq_identity, minPlusMul_identity_left]

/-! ## Associativity of min-plus multiplication -/

/-- Min-plus multiplication is associative: {lit}`(A ◁ B) ◁ C = A ◁ (B ◁ C)`. -/
theorem minPlusMul_assoc (A B C : V → V → WithTop ℝ) (i j : V) :
    G.minPlusMul (G.minPlusMul A B) C i j = G.minPlusMul A (G.minPlusMul B C) i j := by
  unfold minPlusMul
  by_cases huniv_nonempty : (Finset.univ : Finset V).Nonempty
  · calc
      (Finset.univ : Finset V).inf (fun k : V =>
        (Finset.univ : Finset V).inf (fun k' : V => A i k' + B k' k) + C k j) =
        (Finset.univ : Finset V).inf (fun k : V =>
          (Finset.univ : Finset V).inf (fun k' : V => (A i k' + B k' k) + C k j)) := by
        refine Finset.inf_congr rfl (fun k hk => ?_)
        rw [Finset.inf_add_distrib (Finset.univ : Finset V) huniv_nonempty (fun k' => A i k' + B k' k) (C k j)]
      _ = (Finset.univ : Finset V).inf (fun k' : V =>
          (Finset.univ : Finset V).inf (fun k : V => (A i k' + B k' k) + C k j)) := by
        rw [Finset.inf_inf_comm (fun k' k => (A i k' + B k' k) + C k j)]
      _ = (Finset.univ : Finset V).inf (fun k' : V =>
          A i k' + (Finset.univ : Finset V).inf (fun k : V => (B k' k + C k j))) := by
        refine Finset.inf_congr rfl (fun k' hk' => ?_)
        rw [Finset.add_inf_distrib (Finset.univ : Finset V) huniv_nonempty (A i k') (fun k => (B k' k + C k j))]
        simp [add_assoc]
      _ = (Finset.univ : Finset V).inf (fun k' : V =>
          A i k' + (Finset.univ : Finset V).inf (fun k : V => B k' k + C k j)) := by
        refine Finset.inf_congr rfl (fun k' hk' => ?_)
        simp [add_assoc]
      _ = (Finset.univ : Finset V).inf (fun k' : V =>
          A i k' + (Finset.univ : Finset V).inf (fun k : V => B k' k + C k j)) := rfl
  · -- Empty universe: Finset.univ is empty, both sides are ⊤
    have huniv_empty : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp huniv_nonempty
    simp [huniv_empty]

/-- {lit}`L (m + n) = minPlusMul (L m) (L n)`.  The shortest-path matrix using at most
`m + n` edges equals the min-plus product of the matrices using at most `m` and `n` edges. -/
theorem L_add (m n : ℕ) (i j : V) : G.L (m + n) i j = G.minPlusMul (G.L m) (G.L n) i j := by
  induction' n with n ih generalizing i j
  · -- n = 0: L(m+0) = L m = minPlusMul(L m, L 0) = minPlusMul(L m, I) = L m
    simp [L, minPlusMul_identity_right]
  · -- n+1: L(m + n + 1) = extendShortestPaths(L(m+n)) = minPlusMul(L(m+n), W)
    -- By IH: L(m+n) = minPlusMul(L m, L n)
    -- So: L(m+n+1) = minPlusMul(minPlusMul(L m, L n), W)
    -- By associativity: = minPlusMul(L m, minPlusMul(L n, W))
    -- = minPlusMul(L m, L(n+1)) [by definition of L]
    calc
      G.L (m + (n + 1)) i j = G.L ((m + n) + 1) i j := by omega
      _ = G.extendShortestPaths (G.L (m + n)) i j := by rw [L_succ]
      _ = G.minPlusMul (G.L (m + n)) G.weightMatrix i j := rfl
      _ = G.minPlusMul (G.minPlusMul (G.L m) (G.L n)) G.weightMatrix i j := by rw [ih]
      _ = G.minPlusMul (G.L m) (G.minPlusMul (G.L n) G.weightMatrix) i j := by
        rw [G.minPlusMul_assoc (G.L m) (G.L n) G.weightMatrix i j]
      _ = G.minPlusMul (G.L m) (G.L (n + 1)) i j := by
        simp [L_succ, extendShortestPaths]

/-- **Lemma 25.2 (squaring identity).** {lit}`L^(2m) = L^m ◁ L^m`. -/
theorem L_sq_eq_minPlusMul (m : ℕ) (i j : V) :
    G.L (2 * m) i j = G.minPlusMul (G.L m) (G.L m) i j := by
  calc
    G.L (2 * m) i j = G.L (m + m) i j := by ring
    _ = G.minPlusMul (G.L m) (G.L m) i j := by rw [G.L_add m m i j]

/-- **Lemma 25.1 (EXTEND-SHORTEST-PATHS correctness).**
`L^(m+1)_ij = min_k (L^m_ik + w_kj)`. -/
theorem lemma_25_1 (m : ℕ) (i j : V) : G.L (m + 1) i j =
    (Finset.univ : Finset V).inf (fun k => G.L m i k + G.weightMatrix k j) := by
  simp [L_succ, extendShortestPaths, minPlusMul]

/-! ## Stability and FASTER-APSP correctness -/

/-- {lit}`L` is nonincreasing in the round count: {lit}`L^{k+1} ≤ L^k`. -/
theorem L_succ_le (k : ℕ) (i j : V) : G.L (k + 1) i j ≤ G.L k i j := by
  rw [L_succ, extendShortestPaths, minPlusMul]
  calc
    (Finset.univ : Finset V).inf (fun k' : V => G.L k i k' + G.weightMatrix k' j) ≤
      G.L k i j + G.weightMatrix j j := Finset.inf_le (Finset.mem_univ j)
    _ = G.L k i j := by simp [weightMatrix]

/-- {lit}`L` is monotone: for {lit}`k₁ ≤ k₂` we have {lit}`L^{k₂} ≤ L^{k₁}`. -/
theorem L_monotone (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) (i j : V) : G.L k₂ i j ≤ G.L k₁ i j := by
  revert i j
  induction' h with k h IH generalizing i j
  · rfl
  · exact le_trans (L_succ_le k i j) (IH i j)

/-- Under no negative-weight cycles, {lit}`L` stabilizes at {lit}`L^{|V|-1}`:
for any {lit}`m ≥ |V|-1`, {lit}`L^m = L^{|V|-1}`. -/
theorem L_stabilizes_after (hNC : G.NoNegCycle) (i j : V) (m : ℕ) (hm : Fintype.card V - 1 ≤ m) :
    G.L m i j = G.L (Fintype.card V - 1) i j := by
  apply le_antisymm
  · -- L(m) ≤ L(n-1) by monotonicity
    exact G.L_monotone (Fintype.card V - 1) m hm i j
  · -- L(n-1) ≤ L(m) because L(n-1) = δ is the shortest-path distance
    -- and L(m) is always realised by some walk (or is ⊤).
    have h_shortest : G.IsShortestDist i j (G.L (Fintype.card V - 1) i j) := by
      rw [L_eq_relaxDist]
      exact G.relaxDist_isShortestDist hNC i j
    rcases h_shortest with ⟨h_lower, _⟩
    rcases G.L_attainable m i j with htop | ⟨p, hp, _, hpw⟩
    · rw [htop]; exact le_top
    · rw [hpw]; exact h_lower p hp

/-- The number {lit}`numSquarings` ensures {lit}`2^numSquarings ≥ |V| - 1`. -/
theorem numSquarings_pow_two_ge : 2^numSquarings ≥ Fintype.card V - 1 := by
  unfold numSquarings
  set n := Fintype.card V with hn
  by_cases hn1 : n - 1 ≤ 1
  · simp [hn1]
  · have hpos : n - 2 ≥ 1 := by omega
    have hlt : n - 2 < 2 ^ (Nat.log2 (n - 2) + 1) :=
      Nat.lt_two_pow_succ (by omega : n - 2 ≠ 0)
    omega

/-- {lit}`t` iterations of the squaring map starting from the edge-weight matrix
{lit}`W` give {lit}`L(2^t)`. -/
theorem iterate_minPlusMul_sq_eq_L_pow_two (t : ℕ) (i j : V) :
    (fun L => G.minPlusMul L L)^[t] G.weightMatrix i j = G.L (2^t) i j := by
  induction' t with t ih generalizing i j
  · simp [L_one_eq_weightMatrix]
  · rw [Function.iterate_succ', Function.comp_apply, ih]
    rw [G.L_sq_eq_minPlusMul (2^t) i j]
    ring

/-- **FASTER-APSP correctness.**  Under no negative-weight cycles, {lit}`fasterAPSP` equals
the all-pairs shortest-path matrix {lit}`L^{|V|-1} = δ`. -/
theorem fasterAPSP_eq_L (hNC : G.NoNegCycle) (i j : V) :
    G.fasterAPSP i j = G.L (Fintype.card V - 1) i j := by
  unfold fasterAPSP
  rw [G.iterate_minPlusMul_sq_eq_L_pow_two numSquarings i j]
  have h_ge : 2^numSquarings ≥ Fintype.card V - 1 := G.numSquarings_pow_two_ge
  exact G.L_stabilizes_after hNC i j (2^numSquarings) h_ge

/-- **All-pairs shortest-path distance.**  Under no negative-weight cycles,
{lit}`fasterAPSP` gives the exact all-pairs shortest-path distances. -/
theorem fasterAPSP_eq_shortestDist (hNC : G.NoNegCycle) (i j : V) :
    G.fasterAPSP i j = (G.relaxDist i (Fintype.card V - 1) j) := by
  rw [G.fasterAPSP_eq_L hNC i j, L_eq_relaxDist]
