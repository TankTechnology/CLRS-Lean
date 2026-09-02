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

The full run binds that support index once and threads it through every
recursive attempt.  Work is stated in the explicit unit-cost RAM model of the
support-BFS layer, not as Lean kernel or compiled-container evaluation time.

Proof witnesses and erasure/translation proofs carry no RAM charge.  The
charged data operations are precisely support construction, bucket scans,
parent-list construction/reversal, residual-to-graph projection, and
matching-edge erase/insert updates.
-/

namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem matchingFlowFunSummand_integral (e : V × V) (u v : V ⊕ Bool) :
    ∃ n : Int, matchingFlowFunSummand e u v = (n : Real) := by
  let n : Int :=
    match u, v with
    | Sum.inr true, Sum.inl l => if e.1 = l then 1 else 0
    | Sum.inl a, Sum.inl b =>
        (if e = (a, b) then 1 else 0) + (if e = (b, a) then -1 else 0)
    | Sum.inl r, Sum.inr false => if e.2 = r then 1 else 0
    | Sum.inl l, Sum.inr true => if e.1 = l then -1 else 0
    | Sum.inr false, Sum.inl r => if e.2 = r then -1 else 0
    | _, _ => 0
  refine ⟨n, ?_⟩
  cases u with
  | inl a =>
      cases v with
      | inl b =>
          by_cases hab : e = (a, b) <;> by_cases hba : e = (b, a) <;>
            simp [n, matchingFlowFunSummand, hab, hba]
      | inr b =>
          cases b <;> simp [n, matchingFlowFunSummand]
  | inr a =>
      cases a <;> cases v with
      | inl b => simp [n, matchingFlowFunSummand]
      | inr b => cases b <;> simp [n, matchingFlowFunSummand]

/-- Every matching-derived semantic flow is integral. -/
theorem matchingToFlow_integral {G : BipartiteGraph V} (M : Matching V G) :
    (matchingToFlow M).IsIntegral := by
  intro u v
  change ∃ n : Int, matchingFlowFun M u v = (n : Real)
  unfold matchingFlowFun
  induction M.edges using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e support he ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm⟩ := matchingFlowFunSummand_integral e u v
      refine ⟨m + n, ?_⟩
      simp [he, hm, hn]

/-- Uniform work allowance for one attempted augmentation. -/
def matchingAttemptWorkBudget (G : BipartiteGraph V) : Nat :=
  5 * flowVertexCount V + 8 * flowArcCount G

/-- Every matching has at most one edge per left vertex. -/
theorem Matching.size_le_left_card {G : BipartiteGraph V}
    (M : Matching V G) : M.size ≤ G.L.card := by
  rw [← M.matchedLeft_card]
  apply Finset.card_le_card
  intro l hl
  exact M.mem_L_of_isMatchedLeft ((M.mem_matchedLeft_iff l).1 hl)

/-- A missing sink label in a BFS using an explicitly supplied support
adjacency certifies maximality of the current matching. -/
theorem isMaximum_of_matchingCostedBFSWith_distance_none
    {G : BipartiteGraph V} (A : SupportAdjacency (V ⊕ Bool))
    (M : Matching V G) (cover : SupportsResidual A (matchingToFlow M))
    (hnone : (matchingCostedBFSWith A M).state.distance
      (Sum.inr false) = none) :
    M.IsMaximum := by
  have hno : ¬ (matchingToFlow M).hasAugmentingPath := by
    intro hpath
    have hex : ∃ d, (residualBFS (matchingToFlow M)).distance
        (Sum.inr false) = some d :=
      (bfsState_distance_defined_iff_reachable (matchingToFlow M)
        (Sum.inr false)).2 hpath
    rw [← matchingCostedBFSWith_state A M cover] at hex
    rcases hex with ⟨d, hd⟩
    rw [hnone] at hd
    simp at hd
  have hmaxFlow := Flow.maximal_of_noAugmentingPath (matchingToFlow M) hno
  intro M'
  have hle := hmaxFlow (matchingToFlow M')
  rw [matchingToFlow_value, matchingToFlow_value] at hle
  exact_mod_cast hle

/-- Specialized maximality wrapper for the canonical matching support. -/
theorem isMaximum_of_matchingCostedBFS_distance_none
    {G : BipartiteGraph V} (M : Matching V G)
    (hnone : (matchingCostedBFS M).state.distance (Sum.inr false) = none) :
    M.IsMaximum :=
  isMaximum_of_matchingCostedBFSWith_distance_none
    (matchingFlowAdjacency G).adjacency M (matchingFlowSupportsResidual M) hnone

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

/-- Run the attached-cost matching loop from an arbitrary matching while
reusing one explicitly supplied support adjacency throughout the recursion. -/
noncomputable def costedMatchingRunFrom (G : BipartiteGraph V)
    (A : SupportAdjacency (V ⊕ Bool))
    (hA : A = (matchingFlowAdjacency G).adjacency) :
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
      let cover : SupportsResidual A (matchingToFlow initial) := by
        rw [hA]
        exact matchingFlowSupportsResidual initial
      let bfs := matchingCostedBFSWith A initial
      match hdistance : bfs.state.distance (Sum.inr false) with
      | none =>
          { matching := initial
            work := bfs.work
            augmentations := 0
            size_eq := by simp
            augmentations_le := by simp
            maximum_or_full := Or.inl
              (isMaximum_of_matchingCostedBFSWith_distance_none
                A initial cover hdistance)
            work_le := by
              have hbfs : bfs.work ≤
                  flowVertexCount V + 8 * flowArcCount G := by
                have h := matchingCostedBFSWith_work_le A initial cover
                have hstorage : A.storage = 2 * flowArcCount G := by
                  rw [hA, matchingFlowAdjacency_storage]
                rw [hstorage] at h
                simp only [bfs, flowVertexCount] at h ⊢
                omega
              simp only [matchingAttemptWorkBudget]
              rw [Nat.add_mul]
              simp only [one_mul]
              omega }
      | some d =>
          let recovery := matchingBFSPathRecoveryWith A initial cover hdistance
          let projection :=
            matchingBFSGraphProjectionWith A initial cover hdistance
          let p := projection.vertices
          let hp := matchingBFSGraphProjectionWith_isAugmenting
            A initial cover hdistance
          let update := augmentMatchingAlong initial p hp
          let tail := costedMatchingRunFrom G A hA fuel update.matching
          { matching := tail.matching
            work := bfs.work + recovery.work + projection.work + update.work +
              tail.work
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
                have h := matchingCostedBFSWith_work_le A initial cover
                have hstorage : A.storage = 2 * flowArcCount G := by
                  rw [hA, matchingFlowAdjacency_storage]
                rw [hstorage] at h
                simp only [bfs, flowVertexCount] at h ⊢
                omega
              have hrecovery : recovery.work ≤ 2 * flowVertexCount V := by
                simpa [recovery] using
                  matchingBFSPathRecoveryWith_work_le A initial cover hdistance
              have hprojection : projection.work ≤ flowVertexCount V := by
                simpa [projection] using
                  matchingBFSGraphProjectionWith_work_le
                    A initial cover hdistance
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
  flow : Flow (V ⊕ Bool) (toFlowNetwork V G)
  flow_eq : flow = matchingToFlow matching
  work : Nat
  augmentations : Nat

/-- The full textbook run starts from the empty matching and permits one
successful augmentation per left vertex. -/
noncomputable def costedMatchingRun (G : BipartiteGraph V) :
    CostedMatchingRun G :=
  let built := matchingFlowAdjacency G
  let core := costedMatchingRunFrom G built.adjacency rfl
    G.L.card (Matching.empty G)
  { matching := core.matching
    flow := matchingToFlow core.matching
    flow_eq := rfl
    work := built.work + core.work
    augmentations := core.augmentations }

/-- The returned matching is maximum. -/
theorem costedMatchingRun_maximum (G : BipartiteGraph V) :
    (costedMatchingRun G).matching.IsMaximum := by
  let built := matchingFlowAdjacency G
  let core := costedMatchingRunFrom G built.adjacency rfl
    G.L.card (Matching.empty G)
  change core.matching.IsMaximum
  rcases core.maximum_or_full with hmax | hfull
  · exact hmax
  · intro M'
    have hsize : core.matching.size = G.L.card := by
      rw [core.size_eq, Matching.empty_size, zero_add, hfull]
    rw [hsize]
    exact Matching.size_le_left_card M'

theorem costedMatchingRun_flow_eq (G : BipartiteGraph V) :
    (costedMatchingRun G).flow =
      matchingToFlow (costedMatchingRun G).matching :=
  (costedMatchingRun G).flow_eq

/-- The semantic flow attached definitionally to the returned matching is
maximal. -/
theorem costedMatchingRun_flow_maximal (G : BipartiteGraph V) :
    (costedMatchingRun G).flow.isMaximal := by
  rw [costedMatchingRun_flow_eq]
  apply Flow.maximal_of_noAugmentingPath
  intro hpath
  have hnoGraph :=
    (berge_maximum_iff_no_augmentingPath (costedMatchingRun G).matching).1
      (costedMatchingRun_maximum G)
  exact hnoGraph
    (augmentingPath_of_hasAugmentingPath (costedMatchingRun G).matching hpath)

theorem costedMatchingRun_flow_integral (G : BipartiteGraph V) :
    (costedMatchingRun G).flow.IsIntegral := by
  rw [costedMatchingRun_flow_eq]
  exact matchingToFlow_integral _

theorem costedMatchingRun_flow_value (G : BipartiteGraph V) :
    (costedMatchingRun G).flow.value =
      ((costedMatchingRun G).matching.size : Real) := by
  rw [costedMatchingRun_flow_eq, matchingToFlow_value]

/-- Exact attached bound: support construction once, followed by at most
`|L|` linear support-BFS/path-update attempts. -/
theorem costedMatchingRun_work_le (G : BipartiteGraph V) :
    (costedMatchingRun G).work ≤
      2 * flowArcCount G + G.L.card * matchingAttemptWorkBudget G := by
  let built := matchingFlowAdjacency G
  let core := costedMatchingRunFrom G built.adjacency rfl
    G.L.card (Matching.empty G)
  have hcore := core.work_le
  have hbuild := matchingFlowAdjacency_work G
  change built.work + core.work ≤ _
  change (matchingFlowAdjacency G).work = _ at hbuild
  rw [hbuild]
  omega

/-- A conventional constant-factor product form of the adjacency-list
bound: the run is `O(V_f E_f)` for the constructed flow network. -/
theorem costedMatchingRun_work_le_product (G : BipartiteGraph V) :
    (costedMatchingRun G).work ≤
      20 * flowVertexCount V * (flowArcCount G + 1) := by
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
      G.L.card * (5 * vf + 8 * ef) ≤ vf * (5 * vf + 8 * ef) :=
    Nat.mul_le_mul_right _ hleft
  have hvfSquare : 5 * vf * vf ≤ 10 * vf * (ef + 1) := by
    have h := Nat.mul_le_mul_left (5 * vf) hvf
    calc
      5 * vf * vf ≤ 5 * vf * (2 * (ef + 1)) := h
      _ = 10 * vf * (ef + 1) := by ring
  have hefLinear : 8 * vf * ef ≤ 8 * vf * (ef + 1) := by
    exact Nat.mul_le_mul_left (8 * vf) (Nat.le_succ ef)
  have hefBuild : 2 * ef ≤ 2 * vf * (ef + 1) := by
    have h := Nat.mul_le_mul_right (ef + 1) hvone
    have h' : ef ≤ vf * (ef + 1) :=
      (Nat.le_succ ef).trans (by simpa using h)
    calc
      2 * ef ≤ 2 * (vf * (ef + 1)) := Nat.mul_le_mul_left 2 h'
      _ = 2 * vf * (ef + 1) := by ring
  change 2 * ef + G.L.card * (5 * vf + 8 * ef) ≤
    20 * vf * (ef + 1)
  calc
    2 * ef + G.L.card * (5 * vf + 8 * ef) ≤
        2 * ef + vf * (5 * vf + 8 * ef) :=
      Nat.add_le_add_left hleftMul _
    _ = 2 * ef + 5 * vf * vf + 8 * vf * ef := by ring
    _ ≤ 2 * vf * (ef + 1) + 10 * vf * (ef + 1) +
        8 * vf * (ef + 1) := by
      exact Nat.add_le_add (Nat.add_le_add hefBuild hvfSquare) hefLinear
    _ = 20 * vf * (ef + 1) := by ring

/-- The run performs no more successful augmentations than left vertices. -/
theorem costedMatchingRun_augmentations_le (G : BipartiteGraph V) :
    (costedMatchingRun G).augmentations ≤ G.L.card := by
  let built := matchingFlowAdjacency G
  exact (costedMatchingRunFrom G built.adjacency rfl
    G.L.card (Matching.empty G)).augmentations_le

/-- **Attached-cost flow-method headline (CLRS §25.1).**  The returned value
is a maximum matching produced by the support-indexed BFS/update execution,
and its same-execution work satisfies the displayed adjacency-list product
bound. -/
theorem flowMethod_finds_maximum_matching_with_attached_cost
    (G : BipartiteGraph V) :
    let run := costedMatchingRun G
    run.matching.IsMaximum ∧
      run.flow.isMaximal ∧
      run.flow.IsIntegral ∧
      run.flow.value = (run.matching.size : Real) ∧
      run.work ≤ 2 * flowArcCount G + G.L.card * matchingAttemptWorkBudget G ∧
      run.augmentations ≤ G.L.card := by
  dsimp only
  exact ⟨costedMatchingRun_maximum G, costedMatchingRun_flow_maximal G,
    costedMatchingRun_flow_integral G, costedMatchingRun_flow_value G,
    costedMatchingRun_work_le G,
    costedMatchingRun_augmentations_le G⟩

end Matchings
end CLRS
