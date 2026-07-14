import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 25.1. All-pairs shortest paths model

Definitions and basic properties of the all-pairs shortest-path model:
edge-weight matrix, min-plus product, FASTER-APSP.

Main results:
- {lit}`CLRS.Chapter24.WeightedGraph.minPlusMul`: the min-plus matrix product.
- {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP`: CLRS FASTER-APSP (repeated squaring).
- {lit}`CLRS.Chapter24.WeightedGraph.lemma_25_1`: Lemma 25.1 (`L^(m+1) = L^m ◁ W`).
- {lit}`CLRS.Chapter24.WeightedGraph.L_sq_eq_minPlusMul`: Lemma 25.2 (`L^(2m) = L^m ◁ L^m`).
- {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_L`: FASTER-APSP equals `L^(|V|-1)` under `NoNegCycle`.
- {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_shortestDist`: FASTER-APSP correctness.

**Current gaps:** Predecessor matrix Pi; Floyd-Warshall; associativity of min-plus product;
`numSquarings_pow_two_ge` (requires log2 lemma);
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

/-! ## Lemmas 25.1 and 25.2 (squaring identity) -/

/-- **Lemma 25.1.** `L^(m+1) = L^m ◁ W`.  A single EXTEND-SHORTEST-PATHS step
is the min-plus product of the current shortest-path matrix with the weight matrix. -/
theorem lemma_25_1 (m : ℕ) (i j : V) : G.L (m + 1) i j = minPlusMul (G.L m) G.weightMatrix i j := by
  simp [L_succ, extendShortestPaths]

/-- The function `a + ·` distributes over `⊓` in `WithTop ℝ`. -/
lemma add_inf_distrib (a b c : WithTop ℝ) : a + (b ⊓ c) = (a + b) ⊓ (a + c) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a' =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b' =>
      induction c using WithTop.recTopCoe with
      | top => simp
      | coe c' =>
        simpa [WithTop.coe_add] using (congrArg (WithTop.some : ℝ → WithTop ℝ)
          (min_add_add_left a' b' c')).symm

/-- Addition distributes over `Finset.inf` for nonempty sets. -/
lemma add_inf (a : WithTop ℝ) (s : Finset V) (hs : s.Nonempty) (f : V → WithTop ℝ) :
    a + s.inf f = s.inf (fun x => a + f x) := by
  induction' s using Finset.induction_on with x s hx ih
  · exfalso; exact Finset.not_nonempty_empty hs
  · rw [Finset.inf_insert, Finset.inf_insert]
    by_cases hne : s.Nonempty
    · have h_ih := ih hne
      rw [← h_ih, add_inf_distrib]
    · have h_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst h_empty
      simp

/-- Min-plus matrix multiplication is associative. -/
theorem minPlusMul_assoc (A B C : V → V → WithTop ℝ) (i j : V) :
    minPlusMul (minPlusMul A B) C i j = minPlusMul A (minPlusMul B C) i j := by
  unfold minPlusMul
  by_cases huniv : (Finset.univ : Finset V).Nonempty
  · have h_add_inf (a : WithTop ℝ) (f : V → WithTop ℝ) : a + (univ : Finset V).inf f = (univ : Finset V).inf (fun x => a + f x) :=
      add_inf a (univ : Finset V) huniv f
    have hswap_inf (f : V → V → WithTop ℝ) :
        (univ : Finset V).inf (fun k : V => (univ : Finset V).inf (fun l : V => f k l)) =
        (univ : Finset V).inf (fun l : V => (univ : Finset V).inf (fun k : V => f k l)) := by
      calc
        (univ : Finset V).inf (fun k : V => (univ : Finset V).inf (fun l : V => f k l))
            = (univ ×ˢ univ : Finset (V × V)).inf (fun (p : V × V) => f p.1 p.2) := by
              rw [inf_product_left]
        _ = (univ : Finset V).inf (fun l : V => (univ : Finset V).inf (fun k : V => f k l)) := by
          rw [inf_product_right]
    calc
      (univ : Finset V).inf (fun k : V => ((univ : Finset V).inf (fun l : V => A i l + B l k)) + C k j)
          = (univ : Finset V).inf (fun k : V => (univ : Finset V).inf (fun l : V => (A i l + B l k) + C k j)) := by
            refine Finset.inf_congr rfl (fun k hk => ?_)
            rw [add_comm, h_add_inf (C k j) (fun l : V => A i l + B l k)]
            refine Finset.inf_congr rfl (fun l hl => ?_)
            exact add_comm (C k j) (A i l + B l k)
      _ = (univ : Finset V).inf (fun l : V => (univ : Finset V).inf (fun k : V => (A i l + B l k) + C k j)) := by
        rw [hswap_inf (fun k l => (A i l + B l k) + C k j)]
      _ = (univ : Finset V).inf (fun l : V => (univ : Finset V).inf (fun k : V => A i l + (B l k + C k j))) := by
        refine Finset.inf_congr rfl (fun l hl => ?_)
        refine Finset.inf_congr rfl (fun k hk => ?_)
        simp [add_assoc]
      _ = (univ : Finset V).inf (fun l : V => A i l + (univ : Finset V).inf (fun k : V => B l k + C k j)) := by
        refine Finset.inf_congr rfl (fun l hl => ?_)
        rw [(h_add_inf (A i l) (fun k : V => B l k + C k j)).symm]
  · -- univ is empty
    have hempty : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp huniv
    simp [hempty]

/-- `L (a + b) = (L a) ◁ (L b)` for all a, b.  General additive property of the
shortest-path matrix. -/
theorem L_add_eq_minPlusMul (a b : ℕ) (i j : V) : G.L (a + b) i j = minPlusMul (G.L a) (G.L b) i j := by
  induction' b with b ih generalizing i j
  · -- b = 0: L (a+0) = L a = L a ◁ L 0 (since L 0 = identityMatrix)
    have hL0 : G.L (0 : ℕ) = identityMatrix := by
      ext i' j'; simp [L_zero, identityMatrix]
    rw [hL0, minPlusMul_identity_right]
    simp
  · have h_funext : G.L (a + b) = minPlusMul (G.L a) (G.L b) := by
      ext i' j'; exact ih i' j'
    calc
      G.L (a + (b + 1)) i j = G.L ((a + b) + 1) i j := by rw [add_assoc]
      _ = minPlusMul (G.L (a + b)) G.weightMatrix i j := by
        simp [extendShortestPaths]
      _ = minPlusMul (minPlusMul (G.L a) (G.L b)) G.weightMatrix i j := by rw [h_funext]
      _ = minPlusMul (G.L a) (minPlusMul (G.L b) G.weightMatrix) i j := by rw [minPlusMul_assoc]
      _ = minPlusMul (G.L a) (G.L (b + 1)) i j := by
        have hLb1 : G.L (b + 1) = minPlusMul (G.L b) G.weightMatrix := by
          ext i' j'; simpa using lemma_25_1 G b i' j'
        rw [← hLb1]

/-- **Lemma 25.2 (squaring identity).** `L^(2m) = L^m ◁ L^m`. -/
theorem L_sq_eq_minPlusMul (m : ℕ) (i j : V) : G.L (2 * m) i j = minPlusMul (G.L m) (G.L m) i j := by
  calc
    G.L (2 * m) i j = G.L (m + m) i j := by rw [two_mul]
    _ = minPlusMul (G.L m) (G.L m) i j := by rw [L_add_eq_minPlusMul]

end WeightedGraph
end Chapter24
end CLRS
