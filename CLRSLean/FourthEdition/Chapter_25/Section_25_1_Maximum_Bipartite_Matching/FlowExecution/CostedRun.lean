import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.CostedBFS
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.MatchingAugment
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S6_Berge_Flow_Method

/-!
# Attached-cost bipartite matching run

This module closes the adjacency-list execution promised by CLRS §25.1.
Each attempt runs the support-indexed BFS, inspects its returned sink label,
recovers that run's parent path, and executes the concrete matching update.
The counter is accumulated in the same recursion and includes the one-time
support-index construction.

Proof witnesses and erasure/translation proofs carry no RAM charge.  The
charged data operations are precisely support construction, bucket scans,
parent-list construction/reversal, and matching-edge erase/insert updates.
-/

namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform work allowance for one attempted augmentation. -/
def matchingAttemptWorkBudget (G : BipartiteGraph V) : Nat :=
  4 * flowVertexCount V + 8 * flowArcCount G

/-- Every matching has at most one edge per left vertex. -/
theorem Matching.size_le_left_card {G : BipartiteGraph V}
    (M : Matching V G) : M.size ≤ G.L.card := by
  rw [← M.matchedLeft_card]
  apply Finset.card_le_card
  intro l hl
  exact M.mem_L_of_isMatchedLeft ((M.mem_matchedLeft_iff l).1 hl)

/-- A missing sink label in the costed BFS certifies maximality of the
current matching. -/
theorem isMaximum_of_matchingCostedBFS_distance_none
    {G : BipartiteGraph V} (M : Matching V G)
    (hnone : (matchingCostedBFS M).state.distance (Sum.inr false) = none) :
    M.IsMaximum := by
  have hno : ¬ (matchingToFlow M).hasAugmentingPath := by
    intro hpath
    have hex : ∃ d, (residualBFS (matchingToFlow M)).distance
        (Sum.inr false) = some d :=
      (bfsState_distance_defined_iff_reachable (matchingToFlow M)
        (Sum.inr false)).2 hpath
    rw [← matchingCostedBFS_state M] at hex
    rcases hex with ⟨d, hd⟩
    rw [hnone] at hd
    simp at hd
  have hmaxFlow := Flow.maximal_of_noAugmentingPath (matchingToFlow M) hno
  intro M'
  have hle := hmaxFlow (matchingToFlow M')
  rw [matchingToFlow_value, matchingToFlow_value] at hle
  exact_mod_cast hle

/-- Result of at most `fuel` costed augmentation attempts from `initial`. -/
structure CostedMatchingRunFrom (G : BipartiteGraph V)
    (initial : Matching V G) (fuel : Nat) where
  matching : Matching V G
  work : Nat
  augmentations : Nat
  size_eq : matching.size = initial.size + augmentations
  augmentations_le : augmentations ≤ fuel
  maximum_or_full : matching.IsMaximum ∨ augmentations = fuel
  work_le : work ≤ fuel * matchingAttemptWorkBudget G

/-- Run the attached-cost matching loop from an arbitrary matching. -/
noncomputable def costedMatchingRunFrom (G : BipartiteGraph V) :
    (fuel : Nat) → (initial : Matching V G) →
      CostedMatchingRunFrom G initial fuel
  | 0, initial =>
      { matching := initial
        work := 0
        augmentations := 0
        size_eq := by simp
        augmentations_le := by simp
        maximum_or_full := Or.inr rfl
        work_le := by simp }
  | fuel + 1, initial =>
      let bfs := matchingCostedBFS initial
      match hdistance : bfs.state.distance (Sum.inr false) with
      | none =>
          { matching := initial
            work := bfs.work
            augmentations := 0
            size_eq := by simp
            augmentations_le := by simp
            maximum_or_full := Or.inl
              (isMaximum_of_matchingCostedBFS_distance_none initial hdistance)
            work_le := by
              have hbfs : bfs.work ≤
                  flowVertexCount V + 8 * flowArcCount G := by
                simpa [bfs] using matchingCostedBFS_work_le initial
              simp only [matchingAttemptWorkBudget]
              rw [Nat.add_mul]
              simp only [one_mul]
              omega }
      | some d =>
          let recovery := matchingBFSPathRecovery initial hdistance
          let translated := augmentingPath_of_residualPath initial recovery.path
          let p := Classical.choose translated
          let hp := Classical.choose_spec translated
          let update := augmentMatchingAlong initial p hp
          let tail := costedMatchingRunFrom G fuel update.matching
          { matching := tail.matching
            work := bfs.work + recovery.work + update.work + tail.work
            augmentations := tail.augmentations + 1
            size_eq := by
              calc
                tail.matching.size = update.matching.size + tail.augmentations :=
                  tail.size_eq
                _ = initial.size + (tail.augmentations + 1) := by
                  rw [update.size_eq]
                  omega
            augmentations_le := by
              have htail := tail.augmentations_le
              omega
            maximum_or_full := by
              rcases tail.maximum_or_full with hmax | hfull
              · exact Or.inl hmax
              · exact Or.inr (by omega)
            work_le := by
              have hbfs : bfs.work ≤
                  flowVertexCount V + 8 * flowArcCount G := by
                simpa [bfs] using matchingCostedBFS_work_le initial
              have hrecovery : recovery.work ≤ 2 * flowVertexCount V := by
                simpa [recovery] using
                  matchingBFSPathRecovery_work_le initial hdistance
              have hupdate : update.work ≤ Fintype.card V := by
                simpa [update] using
                  augmentMatchingAlong_work_le_vertexCard initial p hp
              have htail := tail.work_le
              simp only [matchingAttemptWorkBudget] at htail ⊢
              have hflowVertices : Fintype.card V ≤ flowVertexCount V := by
                simp [flowVertexCount]
              rw [Nat.add_mul]
              simp only [one_mul]
              omega }

/-- Final result, including one-time adjacency-support construction. -/
structure CostedMatchingRun (G : BipartiteGraph V) where
  matching : Matching V G
  work : Nat
  augmentations : Nat

/-- The full textbook run starts from the empty matching and permits one
successful augmentation per left vertex. -/
noncomputable def costedMatchingRun (G : BipartiteGraph V) :
    CostedMatchingRun G :=
  let core := costedMatchingRunFrom G G.L.card (Matching.empty G)
  { matching := core.matching
    work := (matchingFlowAdjacency G).work + core.work
    augmentations := core.augmentations }

/-- The returned matching is maximum. -/
theorem costedMatchingRun_maximum (G : BipartiteGraph V) :
    (costedMatchingRun G).matching.IsMaximum := by
  let core := costedMatchingRunFrom G G.L.card (Matching.empty G)
  change core.matching.IsMaximum
  rcases core.maximum_or_full with hmax | hfull
  · exact hmax
  · intro M'
    have hsize : core.matching.size = G.L.card := by
      rw [core.size_eq, Matching.empty_size, zero_add, hfull]
    rw [hsize]
    exact Matching.size_le_left_card M'

/-- Exact attached bound: support construction once, followed by at most
`|L|` linear support-BFS/path-update attempts. -/
theorem costedMatchingRun_work_le (G : BipartiteGraph V) :
    (costedMatchingRun G).work ≤
      2 * flowArcCount G + G.L.card * matchingAttemptWorkBudget G := by
  let core := costedMatchingRunFrom G G.L.card (Matching.empty G)
  have hcore := core.work_le
  have hbuild := matchingFlowAdjacency_work G
  change (matchingFlowAdjacency G).work + core.work ≤ _
  rw [hbuild]
  omega

/-- A conventional constant-factor product form of the adjacency-list
bound: the run is `O(V_f E_f)` for the constructed flow network. -/
theorem costedMatchingRun_work_le_product (G : BipartiteGraph V) :
    (costedMatchingRun G).work ≤
      18 * flowVertexCount V * (flowArcCount G + 1) := by
  refine (costedMatchingRun_work_le G).trans ?_
  let vf := flowVertexCount V
  let ef := flowArcCount G
  have hvf : vf ≤ 2 * (ef + 1) := by
    dsimp [vf, ef]
    rw [flowVertexCount_eq, flowArcCount_eq]
    omega
  have hvone : 1 ≤ vf := by
    dsimp [vf]
    rw [flowVertexCount_eq]
    omega
  have hleft : G.L.card ≤ vf := by
    exact (left_card_le_vertex_card G).trans (by
      dsimp [vf]
      rw [flowVertexCount_eq]
      omega)
  have hleftMul :
      G.L.card * (4 * vf + 8 * ef) ≤ vf * (4 * vf + 8 * ef) :=
    Nat.mul_le_mul_right _ hleft
  have hvfSquare : 4 * vf * vf ≤ 8 * vf * (ef + 1) := by
    have h := Nat.mul_le_mul_left (4 * vf) hvf
    calc
      4 * vf * vf ≤ 4 * vf * (2 * (ef + 1)) := h
      _ = 8 * vf * (ef + 1) := by ring
  have hefLinear : 8 * vf * ef ≤ 8 * vf * (ef + 1) := by
    exact Nat.mul_le_mul_left (8 * vf) (Nat.le_succ ef)
  have hefBuild : 2 * ef ≤ 2 * vf * (ef + 1) := by
    have h := Nat.mul_le_mul_right (ef + 1) hvone
    have h' : ef ≤ vf * (ef + 1) :=
      (Nat.le_succ ef).trans (by simpa using h)
    calc
      2 * ef ≤ 2 * (vf * (ef + 1)) := Nat.mul_le_mul_left 2 h'
      _ = 2 * vf * (ef + 1) := by ring
  change 2 * ef + G.L.card * (4 * vf + 8 * ef) ≤
    18 * vf * (ef + 1)
  calc
    2 * ef + G.L.card * (4 * vf + 8 * ef) ≤
        2 * ef + vf * (4 * vf + 8 * ef) :=
      Nat.add_le_add_left hleftMul _
    _ = 2 * ef + 4 * vf * vf + 8 * vf * ef := by ring
    _ ≤ 2 * vf * (ef + 1) + 8 * vf * (ef + 1) +
        8 * vf * (ef + 1) := by
      exact Nat.add_le_add (Nat.add_le_add hefBuild hvfSquare) hefLinear
    _ = 18 * vf * (ef + 1) := by ring

/-- The run performs no more successful augmentations than left vertices. -/
theorem costedMatchingRun_augmentations_le (G : BipartiteGraph V) :
    (costedMatchingRun G).augmentations ≤ G.L.card := by
  exact (costedMatchingRunFrom G G.L.card (Matching.empty G)).augmentations_le

/-- **Attached-cost flow-method headline (CLRS §25.1).**  The returned value
is a maximum matching produced by the support-indexed BFS/update execution,
and its same-execution work satisfies the displayed adjacency-list product
bound. -/
theorem flowMethod_finds_maximum_matching_with_attached_cost
    (G : BipartiteGraph V) :
    let run := costedMatchingRun G
    run.matching.IsMaximum ∧
      run.work ≤ 2 * flowArcCount G +
        G.L.card * matchingAttemptWorkBudget G ∧
      run.augmentations ≤ G.L.card := by
  dsimp only
  exact ⟨costedMatchingRun_maximum G, costedMatchingRun_work_le G,
    costedMatchingRun_augmentations_le G⟩

end Matchings
end CLRS
