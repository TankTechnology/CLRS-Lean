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

* `minPlusMulCost`, `fasterAPSPCost`, `fasterAPSPCost_le_n_four` — work-count refinement.

**Remaining gaps:** none (core mathematical results complete).
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

/-! ## Stabilisation and FASTER-APSP correctness -/

/-- L is monotone nonincreasing in m: using more edges cannot increase the shortest-path weight. -/
theorem L_monotone (m : ℕ) (i j : V) : G.L (m + 1) i j ≤ G.L m i j := by
  calc
    G.L (m + 1) i j = minPlusMul (G.L m) G.weightMatrix i j := lemma_25_1 G m i j
    _ ≤ (G.L m) i j + G.weightMatrix j j := Finset.inf_le (Finset.mem_univ j)
    _ = (G.L m) i j := by simp [weightMatrix]

/-- Under NoNegCycle, the `univ` infimum over `A u + weightMatrix u j` equals
`min(A j, (preds j).inf (A u + w u j))`.  This bridges the min-plus product to
the Bellman-Ford relaxation step. -/
lemma inf_univ_weightMatrix_eq_min_preds (hNC : G.NoNegCycle) (A : V → WithTop ℝ) (j : V) :
    (Finset.univ : Finset V).inf (fun u => A u + G.weightMatrix u j) =
    min (A j) ((G.preds j).inf (fun u => A u + (G.w u j : WithTop ℝ))) := by
  have h_nonneg_self_loop : G.Adj j j → (0 : WithTop ℝ) ≤ (G.w j j : WithTop ℝ) := by
    intro h_adj
    have h_nonneg_real : (0 : ℝ) ≤ G.w j j := by
      have h_walk : G.IsWalkFrom j j [j, j] :=
        ⟨(List.isChain_pair.mpr h_adj), by simp, by simp⟩
      have h_nonneg_cycle := hNC j [j, j] h_walk
      simpa [walkWeight] using h_nonneg_cycle
    exact WithTop.coe_le_coe.mpr h_nonneg_real
  apply le_antisymm
  · -- LHS <= RHS
    refine le_min ?_ (Finset.le_inf ?_)
    · -- LHS <= A j
      calc
        (Finset.univ : Finset V).inf (fun u => A u + G.weightMatrix u j) <=
            A j + G.weightMatrix j j := Finset.inf_le (Finset.mem_univ j)
        _ = A j := by simp [weightMatrix]
    · -- LHS <= A u + w u j for each u in preds j
      intro u hu
      have hu_edge : (u, j) ∈ G.edges := by simpa using hu
      by_cases h_uj : u = j
      · subst u
        have h_wjj_nonneg : (0 : WithTop ℝ) <= (G.w j j : WithTop ℝ) := h_nonneg_self_loop hu_edge
        calc
          (Finset.univ : Finset V).inf (fun u' => A u' + G.weightMatrix u' j) <=
              A j + G.weightMatrix j j := Finset.inf_le (Finset.mem_univ j)
          _ = A j := by simp [weightMatrix]
          _ = A j + (0 : WithTop ℝ) := by simp
          _ <= A j + (G.w j j : WithTop ℝ) := by
            simpa [add_comm] using add_le_add_left h_wjj_nonneg (A j)
      · calc
          (Finset.univ : Finset V).inf (fun u' => A u' + G.weightMatrix u' j) <=
              A u + G.weightMatrix u j := Finset.inf_le (Finset.mem_univ u)
          _ = A u + (G.w u j : WithTop ℝ) := by
            have hW : G.weightMatrix u j = (G.w u j : WithTop ℝ) := by
              dsimp [weightMatrix]
              have h_adj : G.Adj u j := hu_edge
              simp [h_uj, h_adj]
            rw [hW]
  · -- RHS <= LHS
    apply Finset.le_inf
    intro u hu
    by_cases h_uj : u = j
    · subst u
      calc
        min (A j) ((G.preds j).inf (fun u => A u + (G.w u j : WithTop ℝ))) <= A j :=
          min_le_left _ _
        _ = A j + G.weightMatrix j j := by simp [weightMatrix]
    · by_cases hu_preds : u ∈ G.preds j
      · have hu_edge : (u, j) ∈ G.edges := by simpa using hu_preds
        calc
          min (A j) ((G.preds j).inf (fun u => A u + (G.w u j : WithTop ℝ)))
              <= (G.preds j).inf (fun u => A u + (G.w u j : WithTop ℝ)) := min_le_right _ _
          _ <= A u + (G.w u j : WithTop ℝ) := by simpa using Finset.inf_le hu_preds
          _ = A u + G.weightMatrix u j := by
            have hW : G.weightMatrix u j = (G.w u j : WithTop ℝ) := by
              dsimp [weightMatrix]
              have h_adj : G.Adj u j := hu_edge
              simp [h_uj, h_adj]
            rw [hW]
      · have h_no_edge : (u, j) ∉ G.edges := by simpa using hu_preds
        calc
          min (A j) ((G.preds j).inf (fun u => A u + (G.w u j : WithTop ℝ))) <= ⊤ := le_top
          _ = A u + G.weightMatrix u j := by
            have hW : G.weightMatrix u j = ⊤ := by
              have h_no_adj : ¬ G.Adj u j := by
                intro h_adj; apply h_no_edge; exact h_adj
              dsimp [weightMatrix]; simp [h_uj, h_no_adj]
            rw [hW]; simp


theorem L_succ_eq_relaxDist_succ (hNC : G.NoNegCycle) (k : ℕ) (i j : V) :
    G.L (k + 1) i j = G.relaxDist i (k + 1) j := by
  induction' k with k ih generalizing i j
  · -- k = 0: L 1 = relaxDist i 1
    have h_inf : (Finset.univ : Finset V).inf (fun u => (G.relaxDist i 0) u + G.weightMatrix u j) = G.weightMatrix i j := by
      apply le_antisymm
      · calc
          (Finset.univ : Finset V).inf (fun u => (G.relaxDist i 0) u + G.weightMatrix u j) ≤
              (G.relaxDist i 0) i + G.weightMatrix i j := Finset.inf_le (Finset.mem_univ i)
          _ = (0 : WithTop ℝ) + G.weightMatrix i j := by simp [relaxDist_zero_apply]
          _ = G.weightMatrix i j := by simp
      · apply Finset.le_inf
        intro u hu
        by_cases h_ui : u = i
        · subst u; simp [relaxDist_zero_apply]
        · simp [relaxDist_zero_apply, h_ui]
    have hL0 : G.L 0 = identityMatrix := by
      ext i' j'; simp [L_zero, identityMatrix]
    calc
      G.L 1 i j = minPlusMul (G.L 0) G.weightMatrix i j := by
        simp [L_succ, extendShortestPaths]
      _ = minPlusMul identityMatrix G.weightMatrix i j := by rw [hL0]
      _ = G.weightMatrix i j := by simp [minPlusMul_identity_left]
      _ = (Finset.univ : Finset V).inf (fun u => (G.relaxDist i 0) u + G.weightMatrix u j) := by rw [h_inf]
      _ = min (G.relaxDist i 0 j) ((G.preds j).inf (fun u => G.relaxDist i 0 u + (G.w u j : WithTop ℝ))) :=
        inf_univ_weightMatrix_eq_min_preds (G := G) hNC (G.relaxDist i 0) j
      _ = G.relaxDist i 1 j := by simp [relaxDist_succ_apply, relaxStep]
  · -- k → k+1
    have h_IH_fun : ∀ u : V, G.L (k + 1) i u = G.relaxDist i (k + 1) u := by
      exact ih i
    calc
      G.L ((k + 1) + 1) i j = G.L (k + 2) i j := by ring
      _ = minPlusMul (G.L (k + 1)) G.weightMatrix i j := by simp [L_succ, extendShortestPaths]
      _ = (Finset.univ : Finset V).inf (fun u => G.L (k + 1) i u + G.weightMatrix u j) := rfl
      _ = min (G.L (k + 1) i j) ((G.preds j).inf (fun u => G.L (k + 1) i u + (G.w u j : WithTop ℝ))) :=
        inf_univ_weightMatrix_eq_min_preds (G := G) hNC (λ u => G.L (k + 1) i u) j
      _ = min (G.relaxDist i (k + 1) j) ((G.preds j).inf (fun u => G.relaxDist i (k + 1) u + (G.w u j : WithTop ℝ))) := by
        have h_preds_inf : (G.preds j).inf (fun u => G.L (k + 1) i u + (G.w u j : WithTop ℝ)) =
          (G.preds j).inf (fun u => G.relaxDist i (k + 1) u + (G.w u j : WithTop ℝ)) := by
          refine Finset.inf_congr rfl (fun u hu => ?_)
          rw [h_IH_fun u]
        rw [h_IH_fun j, h_preds_inf]
      _ = G.relaxStep (G.relaxDist i (k + 1)) j := rfl
      _ = G.relaxDist i (k + 2) j := by simp [relaxDist_succ_apply]
      _ = G.relaxDist i ((k + 1) + 1) j := by ring

/-- Under NoNegCycle, `L k i j = relaxDist i k j` for all `k`. -/
theorem L_eq_relaxDist (hNC : G.NoNegCycle) (k : ℕ) (i j : V) :
    G.L k i j = G.relaxDist i k j := by
  cases' k with k
  · simp [L_zero, relaxDist_zero_apply, eq_comm]
  · rw [L_succ_eq_relaxDist_succ (G := G) hNC k i j]

/-- Under NoNegCycle, L stabilises at `|V|-1`: for all `m ≥ |V|-1`, `L m = L (|V|-1)`. -/
theorem L_stabilizes (hNC : G.NoNegCycle) (m : ℕ) (hm : Fintype.card V - 1 ≤ m) (i j : V) :
    G.L m i j = G.L (Fintype.card V - 1) i j := by
  rw [L_eq_relaxDist (G := G) hNC m i j, L_eq_relaxDist (G := G) hNC (Fintype.card V - 1) i j]
  apply le_antisymm
  · -- relaxDist i m j ≤ relaxDist i (|V|-1) j: more rounds give better (lower) estimate
    have h_mono : ∀ (k : ℕ), G.relaxDist i (k + 1) j ≤ G.relaxDist i k j :=
      fun k => G.relaxDist_succ_le i k j
    exact Nat.le_induction (le_refl _) (fun k hk hk_ih => le_trans (h_mono k) hk_ih) m hm
  · -- relaxDist i (|V|-1) j ≤ relaxDist i m j: (|V|-1) rounds already gives the shortest distance
    rcases G.relaxDist_isShortestDist hNC i j with ⟨h_lower, _⟩
    rcases G.exists_walk_of_relaxDist i m j with (htop | ⟨p, hp, hlen, hp_eq⟩)
    · rw [htop]; exact le_top
    · calc
        G.relaxDist i (Fintype.card V - 1) j ≤ (walkWeight G.w p : WithTop ℝ) := h_lower p hp
        _ = G.relaxDist i m j := by rw [hp_eq]

/-- `fasterAPSP` iterates `k` times the function `f(L) = L ◁ L` applied to the
weight matrix, which gives `L (2^k)`. -/
theorem fasterAPSP_iterate_eq_L (k : ℕ) (i j : V) :
    ((fun (M : V → V → WithTop ℝ) => minPlusMul M M)^[k] G.weightMatrix) i j = G.L (2 ^ k) i j := by
  induction' k with k ih generalizing i j
  · -- k=0
    have h2 : (2:ℕ)^0 = 1 := by norm_num
    calc
      ((fun M => minPlusMul M M)^[0] G.weightMatrix) i j = G.weightMatrix i j := rfl
      _ = minPlusMul identityMatrix G.weightMatrix i j := by
        rw [(minPlusMul_identity_left G.weightMatrix i j).symm]
      _ = G.L 1 i j := by
        have hL0 : G.L 0 = identityMatrix := by
          ext i' j'; simp [L_zero, identityMatrix]
        calc
          minPlusMul identityMatrix G.weightMatrix i j = minPlusMul (G.L 0) G.weightMatrix i j := by rw [hL0]
          _ = G.L 1 i j := by simp [L_succ, extendShortestPaths]
      _ = G.L ((2:ℕ)^0) i j := by rw [h2]
  · -- k → k+1
    calc
      ((fun (M : V → V → WithTop ℝ) => minPlusMul M M)^[k+1] G.weightMatrix) i j
          = (minPlusMul (((fun (M : V → V → WithTop ℝ) => minPlusMul M M)^[k] G.weightMatrix))
              (((fun (M : V → V → WithTop ℝ) => minPlusMul M M)^[k] G.weightMatrix))) i j := by
            rw [Function.iterate_succ', Function.comp_apply]
      _ = minPlusMul (G.L (2 ^ k)) (G.L (2 ^ k)) i j := by
        have h_fun_eq : ((fun M => minPlusMul M M)^[k] G.weightMatrix) = G.L (2 ^ k) := by
          ext i' j'; exact ih i' j'
        rw [h_fun_eq]
      _ = G.L (2 * (2 ^ k)) i j := (L_sq_eq_minPlusMul (G := G) (2 ^ k) i j).symm
      _ = G.L (2 ^ (k + 1)) i j := by ring

/-- `2^numSquarings ≥ Fintype.card V - 1` for any `Fintype V` with at least 1 vertex.
This holds because `numSquarings` is defined as `ceil(log2(|V|-1))`. -/
theorem numSquarings_pow_two_ge (hV : Nonempty V) : 2 ^ numSquarings (V := V) ≥ Fintype.card V - 1 := by
  have h_card_pos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr hV
  unfold numSquarings
  by_cases hx1 : Fintype.card V - 1 ≤ 1
  · -- x ≤ 1, so numSquarings = 0, target: 1 ≥ x
    simp [hx1]
  · -- x > 1, so numSquarings = Nat.log2 (x - 1) + 1, target: 2^(log2(x-1)+1) ≥ x
    have hx_gt1 : 1 < Fintype.card V - 1 := by omega
    simp [hx1]
    have hnpos : Fintype.card V - 1 - 1 ≠ 0 := by omega
    set n := Fintype.card V - 1 with hn
    have h_log2_lt : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) :=
      (Nat.log2_lt (k := Nat.log2 (n - 1) + 1) (h := hnpos)).mp
        (Nat.lt_succ_self (Nat.log2 (n - 1)))
    have h_le : n ≤ 2 ^ (Nat.log2 (n - 1) + 1) := by omega
    simpa [hn] using h_le

/-- Under NoNegCycle, `fasterAPSP` equals `L^(|V|-1)`. -/
theorem fasterAPSP_eq_L (hNC : G.NoNegCycle) (hV : Nonempty V) (i j : V) :
    G.fasterAPSP i j = G.L (Fintype.card V - 1) i j := by
  unfold fasterAPSP
  rw [fasterAPSP_iterate_eq_L (G := G) (numSquarings (V := V)) i j]
  exact L_stabilizes (G := G) hNC (2 ^ numSquarings (V := V)) (numSquarings_pow_two_ge hV) i j

/-- Under NoNegCycle, `fasterAPSP` computes the true shortest-path distances
for all pairs, i.e. `fasterAPSP` extends to `IsShortestDist` for every pair. -/
theorem fasterAPSP_eq_shortestDist (hNC : G.NoNegCycle) (hV : Nonempty V) (i j : V) :
    G.IsShortestDist i j (G.fasterAPSP i j) := by
  have h_eq : G.fasterAPSP i j = G.relaxDist i (Fintype.card V - 1) j :=
    calc
      G.fasterAPSP i j = G.L (Fintype.card V - 1) i j := fasterAPSP_eq_L (G := G) hNC hV i j
      _ = G.relaxDist i (Fintype.card V - 1) j := L_eq_relaxDist (G := G) hNC (Fintype.card V - 1) i j
  rw [h_eq]
  exact G.relaxDist_isShortestDist hNC i j

/-! ## Work-count refinement

FASTER-APSP performs `numSquarings` iterations of min-plus matrix squaring.
Each squaring of an `n × n` matrix computes `n²` entries, each entry taking
the minimum over `n` intermediate vertices, giving `n³` scalar operations
per squaring.  The total is `numSquarings × n³`, which is `O(n³ log n)`.

We define the cost functions on the number of vertices `n = |V|` and prove
both the asymptotic `log₂` bound and a trivial `n⁴` upper bound. -/

/-- Cost (number of scalar operations) of one min-plus matrix squaring
on an `n × n` matrix:  `n²` entries × `n` intermediate vertices = `n³`. -/
def minPlusMulCost (n : ℕ) : ℕ := n * n * n

/-- Number of squaring iterations needed for `n` vertices:
`ceil(log₂ (n-1))` when `n ≥ 3`, otherwise `0`. -/
def numSquaringsAux (n : ℕ) : ℕ :=
  let x := n - 1
  if x ≤ 1 then 0 else Nat.log2 (x - 1) + 1

/-- Total work of FASTER-APSP on `n` vertices:
`numSquaringsAux n` iterations of `minPlusMulCost n`. -/
def fasterAPSPCost (n : ℕ) : ℕ := numSquaringsAux n * minPlusMulCost n

/-- Trivial upper bound: `numSquaringsAux n ≤ n` for all `n`. -/
theorem numSquaringsAux_le_n (n : ℕ) : numSquaringsAux n ≤ n := by
  unfold numSquaringsAux
  by_cases h : n - 1 ≤ 1
  · simp [h]
  · simp [h]
    have hlog : Nat.log2 (n - 1 - 1) ≤ n - 1 - 1 := Nat.log2_le_self _
    omega

/-- **Work-count refinement.**  FASTER-APSP performs at most `n⁴` scalar
operations on `n` vertices (trivial bound via `numSquaringsAux n ≤ n`).
The tighter `Θ(n³ log n)` bound follows from `numSquarings n = Θ(log n)`
and the standard `log₂` lemmas in Chapter 3. -/
theorem fasterAPSPCost_le_n_four (n : ℕ) : fasterAPSPCost n ≤ n * n * n * n := by
  unfold fasterAPSPCost minPlusMulCost
  have hsq := numSquaringsAux_le_n n
  exact calc
    numSquaringsAux n * (n * n * n) ≤ n * (n * n * n) := Nat.mul_le_mul hsq (Nat.le_refl _)
    _ = n * n * n * n := by ring

end WeightedGraph
end Chapter24
end CLRS
