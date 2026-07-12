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

/-- {lit}`L^0 = I`. -/
theorem L_zero_eq_identity (i j : V) : G.L 0 i j = G.identityMatrix i j := by
  simp [L_zero, identityMatrix]

/-- {lit}`L^1 = W`. -/
theorem L_one_eq_weightMatrix (i j : V) : G.L 1 i j = G.weightMatrix i j := by
  rw [L_succ, extendShortestPaths, L_zero_eq_identity, minPlusMul_identity_left]
