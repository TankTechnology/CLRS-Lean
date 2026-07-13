import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 25.1. All-pairs shortest paths model

Definitions and basic properties of the all-pairs shortest-path model:
edge-weight matrix, min-plus product, FASTER-APSP.

Main results:
- {lit}`CLRS.Chapter24.WeightedGraph.minPlusMul`: the min-plus matrix product.
- {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP`: CLRS FASTER-APSP (repeated squaring).

**Current gaps:** Predecessor matrix Pi; Floyd-Warshall; Lemma 25.1/25.2 proofs;
associativity of min-plus product; `numSquarings_pow_two_ge` (requires log2 lemma);
`L_sq_eq_minPlusMul` squaring identity.
-/

namespace CLRS
namespace Chapter24
open Finset
namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-- Edge-weight matrix W. -/
def weightMatrix (i j : V) : WithTop ℝ :=
  if i = j then (0 : WithTop ℝ) else if G.Adj i j then (G.w i j : WithTop ℝ) else ⊤

/-- Min-plus matrix product: (A ◁ B)_ij = min_k (A_ik + B_kj). -/
def minPlusMul (A B : V → V → WithTop ℝ) (i j : V) : WithTop ℝ :=
  (Finset.univ : Finset V).inf (fun k => A i k + B k j)

/-- EXTEND-SHORTEST-PATHS: L' = L ◁ W. -/
def extendShortestPaths (L : V → V → WithTop ℝ) (i j : V) : WithTop ℝ :=
  minPlusMul L G.weightMatrix i j

/-- L m — shortest-path weights using at most m edges. -/
def L (G : WeightedGraph V) : ℕ → V → V → WithTop ℝ
  | 0, i, j => if i = j then (0 : WithTop ℝ) else ⊤
  | m + 1, i, j => G.extendShortestPaths (G.L m) i j

@[simp] theorem L_zero (i j : V) : G.L 0 i j = if i = j then (0 : WithTop ℝ) else ⊤ := rfl
@[simp] theorem L_succ (m : ℕ) (i j : V) : G.L (m + 1) i j = G.extendShortestPaths (G.L m) i j := rfl

/-- Number of squarings: ceil(log2(|V|-1)). -/
def numSquarings [Fintype V] : ℕ :=
  let x := Fintype.card V - 1
  if x ≤ 1 then 0 else Nat.log2 (x - 1) + 1

/-- FASTER-APSP: repeatedly square L = L ◁ L. -/
def fasterAPSP [Fintype V] (G : WeightedGraph V) : V → V → WithTop ℝ :=
  (fun L => minPlusMul L L)^[numSquarings (V := V)] G.weightMatrix

/-- Identity matrix for min-plus multiplication. -/
def identityMatrix (i j : V) : WithTop ℝ := if i = j then (0 : WithTop ℝ) else ⊤

@[simp] theorem identityMatrix_diag (i : V) : identityMatrix i i = (0 : WithTop ℝ) := by
  simp [identityMatrix]
@[simp] theorem identityMatrix_offdiag {i j : V} (h : i ≠ j) : identityMatrix i j = ⊤ := by
  simp [identityMatrix, h]

theorem minPlusMul_identity_left (M : V → V → WithTop ℝ) (i j : V) :
    minPlusMul identityMatrix M i j = M i j := by
  unfold minPlusMul identityMatrix
  have h1 : (Finset.univ : Finset V).inf (fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) ≤ M i j := by
    calc
      (Finset.univ : Finset V).inf (fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) ≤
        ((fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) i) :=
        Finset.inf_le (Finset.mem_univ i)
      _ = M i j := by simp
  have h2 : M i j ≤ (Finset.univ : Finset V).inf (fun k : V => (if i = k then (0 : WithTop ℝ) else ⊤) + M k j) := by
    apply Finset.le_inf
    intro k hk
    by_cases hik : i = k
    · subst k; simp
    · simp [hik]
  exact le_antisymm h1 h2

theorem minPlusMul_identity_right (M : V → V → WithTop ℝ) (i j : V) :
    minPlusMul M identityMatrix i j = M i j := by
  unfold minPlusMul identityMatrix
  have h1 : (Finset.univ : Finset V).inf (fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) ≤ M i j := by
    calc
      (Finset.univ : Finset V).inf (fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) ≤
        ((fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) j) :=
        Finset.inf_le (Finset.mem_univ j)
      _ = M i j := by simp
  have h2 : M i j ≤ (Finset.univ : Finset V).inf (fun k : V => M i k + (if k = j then (0 : WithTop ℝ) else ⊤)) := by
    apply Finset.le_inf
    intro k hk
    by_cases hkj : k = j
    · subst k; simp
    · simp [hkj]
  exact le_antisymm h1 h2

end WeightedGraph
end Chapter24
end CLRS
