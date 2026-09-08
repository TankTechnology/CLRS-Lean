import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall

/-!
# Complete Floyd–Warshall negative-cycle detection

The cycle-safe initializer takes the minimum of the empty-walk cost zero and
an existing self-loop's weight. The original initializer and all original
public theorem signatures remain intact. Under no negative cycles, the new
initializer and recurrence equal the original ones.

Completeness is proved independently of shortest-path cycle removal: nonnegative
final diagonals force triangle inequalities for every processed pivot. Edge
bounds and walk induction then show every closed walk is nonnegative. Thus the
corrected final diagonal test is equivalent to existence of a negative closed
walk, including negative self-loops and cycles in disconnected components.

The definitions use exact real comparisons, as does the existing recurrence.
The Boolean interface describes the finite diagonal scan; machine cost and
stored-array refinement are supplied separately.
-/

namespace CLRS.Chapter24.WeightedGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def floydFrom (initial : V → V → WithTop ℝ) : List V → V → V → WithTop ℝ
  | [], i, j => initial i j
  | k :: ks, i, j => min (floydFrom initial ks i j)
      (floydFrom initial ks i k + floydFrom initial ks k j)

omit [Fintype V] [DecidableEq V] in
theorem floydFrom_le_initial (initial : V → V → WithTop ℝ) (ks : List V) (i j : V) :
    floydFrom initial ks i j ≤ initial i j := by
  induction ks with
  | nil => exact le_rfl
  | cons k ks ih => exact (min_le_left _ _).trans ih

/- If a Floyd stage has nonnegative diagonals, its processed pivots satisfy
triangle inequalities. This implication needs no no-negative-cycle premise. -/
omit [Fintype V] [DecidableEq V] in
theorem floydFrom_triangle (initial : V → V → WithTop ℝ) (ks : List V)
    (hd : ∀ x, 0 ≤ floydFrom initial ks x x) :
    ∀ k ∈ ks, ∀ i j,
      floydFrom initial ks i j ≤ floydFrom initial ks i k + floydFrom initial ks k j := by
  induction ks with
  | nil => simp
  | cons v vs ih =>
      let X := floydFrom initial vs
      have hold : ∀ x, 0 ≤ X x x := fun x => (hd x).trans (min_le_left _ _)
      have ht := ih hold
      intro k hk i j
      simp only [List.mem_cons] at hk
      change min (X i j) (X i v + X v j) ≤
        min (X i k) (X i v + X v k) + min (X k j) (X k v + X v j)
      rcases hk with rfl | hk
      · rw [min_eq_left (le_add_of_nonneg_right (hold k)),
          min_eq_left (le_add_of_nonneg_left (hold k))]
        exact min_le_right _ _
      · have hic : X i v ≤ X i k + X k v := ht k hk i v
        have hcj : X v j ≤ X v k + X k j := ht k hk v j
        have hij : X i j ≤ X i k + X k j := ht k hk i j
        have hcycle : 0 ≤ X k v + X v k := (hd k).trans (min_le_right _ _)
        rcases min_choice (X i k) (X i v + X v k) with ha | ha <;>
          rcases min_choice (X k j) (X k v + X v j) with hb | hb <;> rw [ha, hb]
        · exact (min_le_left _ _).trans hij
        · calc
            min (X i j) (X i v + X v j) ≤ X i v + X v j := min_le_right _ _
            _ ≤ (X i k + X k v) + X v j := add_le_add hic le_rfl
            _ = _ := by ac_rfl
        · calc
            min (X i j) (X i v + X v j) ≤ X i v + X v j := min_le_right _ _
            _ ≤ X i v + (X v k + X k j) := add_le_add le_rfl hcj
            _ = _ := by ac_rfl
        · calc
            min (X i j) (X i v + X v j) ≤ X i v + X v j := min_le_right _ _
            _ ≤ (X i v + X v j) + (X k v + X v k) := le_add_of_nonneg_right hcycle
            _ = _ := by ac_rfl

/-- Initialization retains a negative self-loop while allowing the empty walk. -/
noncomputable def cycleWeightMatrix (G : WeightedGraph V) (i j : V) : WithTop ℝ :=
  if i = j then
    if G.Adj i j then min 0 (G.w i j : WithTop ℝ) else 0
  else if G.Adj i j then (G.w i j : WithTop ℝ) else ⊤

noncomputable def cycleD (G : WeightedGraph V) : List V → V → V → WithTop ℝ :=
  floydFrom G.cycleWeightMatrix

noncomputable def cycleFloydWarshall (G : WeightedGraph V) : V → V → WithTop ℝ :=
  G.cycleD (Finset.univ.toList : List V)

theorem cycleWeightMatrix_le_self (G : WeightedGraph V) (i : V) :
    G.cycleWeightMatrix i i ≤ 0 := by
  by_cases h : G.Adj i i <;> simp [cycleWeightMatrix, h]

theorem cycleWeightMatrix_le_edge (G : WeightedGraph V) (i j : V) (h : G.Adj i j) :
    G.cycleWeightMatrix i j ≤ (G.w i j : WithTop ℝ) := by
  by_cases he : i = j
  · simp only [cycleWeightMatrix, if_pos he, if_pos h]; exact min_le_right _ _
  · simp [cycleWeightMatrix, he, h]

theorem cycleFloydWarshall_triangle (G : WeightedGraph V)
    (hd : ∀ i, 0 ≤ G.cycleFloydWarshall i i) (i k j : V) :
    G.cycleFloydWarshall i j ≤ G.cycleFloydWarshall i k + G.cycleFloydWarshall k j :=
  floydFrom_triangle G.cycleWeightMatrix (Finset.univ.toList : List V) hd k
    (by simp) i j

theorem cycleFloydWarshall_le_edge (G : WeightedGraph V) (i j : V) (h : G.Adj i j) :
    G.cycleFloydWarshall i j ≤ (G.w i j : WithTop ℝ) :=
  (floydFrom_le_initial _ _ _ _).trans (cycleWeightMatrix_le_edge G i j h)

theorem cycleFloydWarshall_le_self (G : WeightedGraph V) (i : V) :
    G.cycleFloydWarshall i i ≤ 0 :=
  (floydFrom_le_initial _ _ _ _).trans (cycleWeightMatrix_le_self G i)


theorem cycleFloydWarshall_le_walk_of_nonneg_diag (G : WeightedGraph V)
    (hd : ∀ i, 0 ≤ G.cycleFloydWarshall i i) (i j : V) (p : List V)
    (hp : G.IsWalkFrom i j p) :
    G.cycleFloydWarshall i j ≤ (walkWeight G.w p : WithTop ℝ) := by
  induction p generalizing i j with
  | nil => have h := hp.head; simp at h
  | cons a as ih =>
      have hai : a = i := by simpa using hp.head
      subst a
      cases as with
      | nil =>
          have hij : i = j := by simpa using hp.last
          subst j
          simpa using cycleFloydWarshall_le_self G i
      | cons b bs =>
          have hchain := List.isChain_cons.mp hp.chain
          have hab : G.Adj i b := hchain.1 b (by simp)
          have htail : G.IsWalkFrom b j (b :: bs) :=
            ⟨hchain.2, by simp, by simpa using hp.last⟩
          calc
            G.cycleFloydWarshall i j ≤
                G.cycleFloydWarshall i b + G.cycleFloydWarshall b j :=
              cycleFloydWarshall_triangle G hd i b j
            _ ≤ (G.w i b : WithTop ℝ) + (walkWeight G.w (b :: bs) : WithTop ℝ) :=
              add_le_add (cycleFloydWarshall_le_edge G i b hab) (ih b j htail)
            _ = _ := by simp

/-- Nonnegative final diagonals rule out every negative closed walk. -/
theorem noNegCycle_of_cycleFloydWarshall_nonneg_diag (G : WeightedGraph V)
    (hd : ∀ i, 0 ≤ G.cycleFloydWarshall i i) : G.NoNegCycle := by
  intro i p hp
  have h := (hd i).trans (cycleFloydWarshall_le_walk_of_nonneg_diag G hd i i p hp)
  exact_mod_cast h

theorem self_weight_nonneg_of_noNegCycle (G : WeightedGraph V) (hn : G.NoNegCycle)
    (i : V) (ha : G.Adj i i) : 0 ≤ G.w i i := by
  have hp : G.IsWalkFrom i i [i, i] :=
    ⟨by simpa using ha, by simp, by simp⟩
  simpa [walkWeight] using hn i [i, i] hp

/-- Existing initialization is preserved on every no-negative-cycle input. -/
theorem cycleWeightMatrix_eq_weightMatrix (G : WeightedGraph V) (hn : G.NoNegCycle) :
    G.cycleWeightMatrix = G.weightMatrix := by
  funext i j
  by_cases hij : i = j
  · subst j
    by_cases ha : G.Adj i i
    · have hw : (0 : WithTop ℝ) ≤ (G.w i i : WithTop ℝ) := by
        exact_mod_cast self_weight_nonneg_of_noNegCycle G hn i ha
      simp [cycleWeightMatrix, weightMatrix, ha, min_eq_left hw]
    · simp [cycleWeightMatrix, weightMatrix, ha]
  · simp [cycleWeightMatrix, weightMatrix, hij]

theorem cycleD_eq_D (G : WeightedGraph V) (hn : G.NoNegCycle) (ks : List V) :
    G.cycleD ks = G.D ks := by
  induction ks with
  | nil => exact cycleWeightMatrix_eq_weightMatrix G hn
  | cons k ks ih =>
      funext i j
      change min (G.cycleD ks i j) (G.cycleD ks i k + G.cycleD ks k j) = _
      rw [ih]
      rfl

theorem cycleFloydWarshall_eq_floydWarshall (G : WeightedGraph V) (hn : G.NoNegCycle) :
    G.cycleFloydWarshall = G.floydWarshall := cycleD_eq_D G hn _

theorem cycleFloydWarshall_nonneg_diag (G : WeightedGraph V) (hn : G.NoNegCycle) (i : V) :
    0 ≤ G.cycleFloydWarshall i i := by
  rw [cycleFloydWarshall_eq_floydWarshall G hn]
  exact G.floydWarshall_nonneg_diag hn i

/-- Complete global negative-cycle test, including negative self-loops. -/
theorem cycleFloydWarshall_negative_iff (G : WeightedGraph V) :
    (∃ i, G.cycleFloydWarshall i i < 0) ↔ ¬ G.NoNegCycle := by
  constructor
  · rintro ⟨i, hi⟩ hn
    exact (not_lt_of_ge (cycleFloydWarshall_nonneg_diag G hn i)) hi
  · intro hn
    by_contra h
    apply hn
    apply noNegCycle_of_cycleFloydWarshall_nonneg_diag G
    simpa only [not_exists, not_lt] using h

/-- Equivalent explicit-witness formulation of the detector. -/
theorem cycleFloydWarshall_negative_iff_closed_walk (G : WeightedGraph V) :
    (∃ i, G.cycleFloydWarshall i i < 0) ↔
      ∃ i p, G.IsWalkFrom i i p ∧ walkWeight G.w p < 0 := by
  rw [cycleFloydWarshall_negative_iff]
  unfold NoNegCycle
  push Not
  rfl


noncomputable def hasNegativeDiagonal (matrix : V → V → WithTop ℝ) : Bool :=
  (Finset.univ : Finset V).toList.any (fun i => decide (matrix i i < 0))

omit [DecidableEq V] in
theorem hasNegativeDiagonal_eq_true_iff (matrix : V → V → WithTop ℝ) :
    hasNegativeDiagonal matrix = true ↔ ∃ i, matrix i i < 0 := by
  simp [hasNegativeDiagonal]

/-- Boolean interface to the corrected global negative-cycle detector. -/
noncomputable def detectsNegativeCycle (G : WeightedGraph V) : Bool :=
  hasNegativeDiagonal G.cycleFloydWarshall

theorem detectsNegativeCycle_iff (G : WeightedGraph V) :
    G.detectsNegativeCycle = true ↔ ¬ G.NoNegCycle := by
  rw [detectsNegativeCycle, hasNegativeDiagonal_eq_true_iff, cycleFloydWarshall_negative_iff]

theorem negative_closed_walk_detected (G : WeightedGraph V) (i : V) (p : List V)
    (hp : G.IsWalkFrom i i p) (hw : walkWeight G.w p < 0) :
    G.detectsNegativeCycle = true := by
  rw [detectsNegativeCycle, hasNegativeDiagonal_eq_true_iff,
    cycleFloydWarshall_negative_iff_closed_walk]
  exact ⟨i, p, hp, hw⟩

theorem cycleFloydWarshall_isShortestDist (G : WeightedGraph V) (hn : G.NoNegCycle)
    (i j : V) : G.IsShortestDist i j (G.cycleFloydWarshall i j) := by
  rw [cycleFloydWarshall_eq_floydWarshall G hn]
  exact G.floydWarshall_isShortestDist hn i j

/-- The original recurrence is the generic stored-matrix target with its original initializer. -/
theorem floydFrom_weightMatrix (G : WeightedGraph V) (ks : List V) :
    floydFrom G.weightMatrix ks = G.D ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      funext i j
      simp only [floydFrom, ih, D_cons]

end CLRS.Chapter24.WeightedGraph
