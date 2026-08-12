import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S1_ComputationDAG

/-!
# 26.1 S2. Ready execution

Residual computation states, ready strands, and the work/span progress lemmas
for executing a set of ready nodes.
-/

namespace CLRS
namespace Chapter27

namespace CompDAG

/-! ## Residual computation states -/

/-- Work remaining in a partially executed computation. -/
def remainingWork (G : CompDAG) (remaining : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range G.n, remaining i

/-- Reuse the dependency graph with a new node-work function. -/
def withWork (G : CompDAG) (nodeWork : ℕ → ℕ) : CompDAG where
  n := G.n
  node_work := nodeWork
  edges := G.edges
  h_edges_in_bounds := G.h_edges_in_bounds
  h_edges_forward := G.h_edges_forward

/-- Critical-path work remaining in a partially executed computation. -/
def remainingSpan (G : CompDAG) (remaining : ℕ → ℕ) : ℕ :=
  (G.withWork remaining).span

/-- Execute one unit of work at each selected node. -/
def execute (_G : CompDAG) (remaining : ℕ → ℕ) (run : Finset ℕ) : ℕ → ℕ :=
  fun v => if v ∈ run then remaining v - 1 else remaining v

private theorem foldr_max_map_le {α : Type} (items : List α) (f g : α → ℕ)
    (hfg : ∀ item ∈ items, f item ≤ g item) :
    (items.map f).foldr max 0 ≤ (items.map g).foldr max 0 := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le_max (hfg item List.mem_cons_self)
        (ih fun tailItem hmem => hfg tailItem (List.mem_cons_of_mem item hmem))

private theorem foldr_max_map_add_one_le {α : Type} (items : List α)
    (f : α → ℕ) (bound : ℕ) (hbound : 0 < bound)
    (hf : ∀ item ∈ items, f item + 1 ≤ bound) :
    (items.map f).foldr max 0 + 1 ≤ bound := by
  induction items with
  | nil => simp; omega
  | cons item items ih =>
      have hitem := hf item List.mem_cons_self
      have htail := ih fun tailItem hmem =>
        hf tailItem (List.mem_cons_of_mem item hmem)
      simp only [List.map_cons, List.foldr_cons]
      rcases le_total (f item) ((items.map f).foldr max 0) with hle | hge
      · rw [max_eq_right hle]
        exact htail
      · rw [max_eq_left hge]
        exact hitem

/-- Increasing node work can only increase the longest path ending at a node. -/
theorem longestTo_mono_work (G : CompDAG) (smaller larger : ℕ → ℕ)
    (hwork : ∀ v, smaller v ≤ larger v) (v : ℕ) :
    (G.withWork smaller).longestTo v ≤ (G.withWork larger).longestTo v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      rw [longestTo, longestTo]
      apply Nat.add_le_add (hwork v)
      apply foldr_max_map_le
      intro edge _hmem
      have hfilt := List.mem_filter.mp edge.property
      have htarget : edge.val.2 = v := of_decide_eq_true hfilt.2
      have hsource_lt : edge.val.1 < v := by
        have hforward := G.h_edges_forward edge.val hfilt.1
        omega
      exact ih edge.val.1 hsource_lt

/-- Residual span is monotone in every node's remaining work. -/
theorem remainingSpan_mono (G : CompDAG) (smaller larger : ℕ → ℕ)
    (hwork : ∀ v, smaller v ≤ larger v) :
    G.remainingSpan smaller ≤ G.remainingSpan larger := by
  unfold remainingSpan span
  apply foldr_max_map_le
  intro v _hv
  exact G.longestTo_mono_work smaller larger hwork v

/-- Executing work cannot increase the residual critical path. -/
theorem remainingSpan_execute_le (G : CompDAG) (remaining : ℕ → ℕ)
    (run : Finset ℕ) :
    G.remainingSpan (G.execute remaining run) ≤ G.remainingSpan remaining := by
  apply G.remainingSpan_mono
  intro v
  simp only [execute]
  split <;> omega

/-- Nodes that have positive remaining work and whose immediate predecessors
have finished. -/
def ready (G : CompDAG) (remaining : ℕ → ℕ) : Finset ℕ :=
  (Finset.range G.n).filter fun v =>
    0 < remaining v ∧
      ∀ edge ∈ G.edges, edge.2 = v → remaining edge.1 = 0

theorem mem_ready_iff (G : CompDAG) (remaining : ℕ → ℕ) (v : ℕ) :
    v ∈ G.ready remaining ↔
      v < G.n ∧ 0 < remaining v ∧
        ∀ edge ∈ G.edges, edge.2 = v → remaining edge.1 = 0 := by
  simp [ready]

private theorem longestTo_execute_ready_add_one_le (G : CompDAG)
    (remaining : ℕ → ℕ) (v : ℕ) (hv : v < G.n)
    (hpositive : 0 < (G.withWork remaining).longestTo v) :
    (G.withWork (G.execute remaining (G.ready remaining))).longestTo v + 1 ≤
      (G.withWork remaining).longestTo v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      let predEdges := (G.edges.filter fun edge => edge.2 = v).attach
      let beforeMax :=
        (predEdges.map fun edge =>
          (G.withWork remaining).longestTo edge.val.1).foldr max 0
      let afterMax :=
        (predEdges.map fun edge =>
          (G.withWork (G.execute remaining (G.ready remaining))).longestTo
            edge.val.1).foldr max 0
      rw [longestTo] at hpositive
      rw [longestTo, longestTo]
      change 0 < remaining v + beforeMax at hpositive
      change G.execute remaining (G.ready remaining) v + afterMax + 1 ≤
        remaining v + beforeMax
      have hnode_mono : ∀ node,
          G.execute remaining (G.ready remaining) node ≤ remaining node := by
        intro node
        simp only [execute]
        split <;> omega
      have hmax_mono : afterMax ≤ beforeMax := by
        apply foldr_max_map_le
        intro edge _hmem
        exact G.longestTo_mono_work _ _ hnode_mono edge.val.1
      have hmax_drop (hmax_positive : 0 < beforeMax) :
          afterMax + 1 ≤ beforeMax := by
        apply foldr_max_map_add_one_le predEdges _ beforeMax hmax_positive
        intro edge _hmem
        have hfilt := List.mem_filter.mp edge.property
        have htarget : edge.val.2 = v := of_decide_eq_true hfilt.2
        have hsource_lt : edge.val.1 < v := by
          have hforward := G.h_edges_forward edge.val hfilt.1
          omega
        have hsource_bound : edge.val.1 < G.n :=
          (G.h_edges_in_bounds edge.val hfilt.1).1
        by_cases hpred_positive :
            0 < (G.withWork remaining).longestTo edge.val.1
        · have hdrop := ih edge.val.1 hsource_lt hsource_bound hpred_positive
          have hmem : (G.withWork remaining).longestTo edge.val.1 ∈
              predEdges.map fun predecessor =>
                (G.withWork remaining).longestTo predecessor.val.1 :=
            List.mem_map.mpr ⟨edge, _hmem, rfl⟩
          have hle := List.le_max_of_le' 0 hmem (le_refl _)
          exact hdrop.trans hle
        · have hbefore_zero :
              (G.withWork remaining).longestTo edge.val.1 = 0 :=
            Nat.eq_zero_of_not_pos hpred_positive
          have hafter_le :=
            G.longestTo_mono_work _ _ hnode_mono edge.val.1
          have hafter_zero :
              (G.withWork (G.execute remaining (G.ready remaining))).longestTo
                  edge.val.1 = 0 := by
            omega
          omega
      by_cases hready : v ∈ G.ready remaining
      · have hvpos := ((G.mem_ready_iff remaining v).mp hready).2.1
        have hexecute :
            G.execute remaining (G.ready remaining) v = remaining v - 1 := by
          simp [execute, hready]
        rw [hexecute]
        omega
      · have hbefore_max_positive : 0 < beforeMax := by
          by_cases hvpos : 0 < remaining v
          · have hnot_all :
                ¬ ∀ edge ∈ G.edges,
                  edge.2 = v → remaining edge.1 = 0 := by
              intro hall
              exact hready ((G.mem_ready_iff remaining v).mpr ⟨hv, hvpos, hall⟩)
            push Not at hnot_all
            obtain ⟨edge, hedge, htarget, hsource_ne⟩ := hnot_all
            let attached :
                { candidate // candidate ∈
                  (G.edges.filter fun candidate => candidate.2 = v) } :=
              ⟨edge, List.mem_filter.mpr ⟨hedge, by simp [htarget]⟩⟩
            have hsource_pos : 0 < remaining edge.1 := Nat.pos_of_ne_zero hsource_ne
            have hlongest_pos :
                0 < (G.withWork remaining).longestTo edge.1 := by
              rw [longestTo]
              change 0 < remaining edge.1 + _
              omega
            have hmem :
                (G.withWork remaining).longestTo edge.1 ∈
                  predEdges.map fun predecessor =>
                    (G.withWork remaining).longestTo predecessor.val.1 :=
              List.mem_map.mpr ⟨attached, by
                simp [predEdges], rfl⟩
            have hle := List.le_max_of_le' 0 hmem (le_refl _)
            exact Nat.lt_of_lt_of_le hlongest_pos hle
          · have hvzero : remaining v = 0 := Nat.eq_zero_of_not_pos hvpos
            omega
        have hexecute :
            G.execute remaining (G.ready remaining) v = remaining v := by
          simp [execute, hready]
        rw [hexecute]
        exact Nat.add_le_add_left (hmax_drop hbefore_max_positive) (remaining v)

/-- If unfinished work remains, executing every ready node removes at least one
unit from the residual critical path. -/
theorem remainingSpan_execute_ready_add_one_le (G : CompDAG)
    (remaining : ℕ → ℕ) (hwork : 0 < G.remainingWork remaining) :
    G.remainingSpan (G.execute remaining (G.ready remaining)) + 1 ≤
      G.remainingSpan remaining := by
  have hwork' : 0 < ∑ v ∈ Finset.range G.n, remaining v := by
    simpa [remainingWork] using hwork
  obtain ⟨v, hvrange, hvpos⟩ := Finset.sum_pos_iff.mp hwork'
  have hvlt : v < G.n := Finset.mem_range.mp hvrange
  have hlongest_pos : 0 < (G.withWork remaining).longestTo v := by
    rw [longestTo]
    change 0 < remaining v + _
    omega
  have hspan_positive : 0 < G.remainingSpan remaining := by
    unfold remainingSpan span
    have hmem : (G.withWork remaining).longestTo v ∈
        (List.range G.n).map (G.withWork remaining).longestTo :=
      List.mem_map.mpr ⟨v, List.mem_range.mpr hvlt, rfl⟩
    have hle := List.le_max_of_le' 0 hmem (le_refl _)
    exact Nat.lt_of_lt_of_le hlongest_pos hle
  unfold remainingSpan span
  apply foldr_max_map_add_one_le (List.range G.n) _ _ hspan_positive
  intro node hnode
  have hnode_lt : node < G.n := List.mem_range.mp hnode
  by_cases hnode_positive : 0 < (G.withWork remaining).longestTo node
  · have hdrop :=
      G.longestTo_execute_ready_add_one_le remaining node hnode_lt hnode_positive
    have hmem : (G.withWork remaining).longestTo node ∈
        (List.range G.n).map (G.withWork remaining).longestTo :=
      List.mem_map.mpr ⟨node, hnode, rfl⟩
    have hle := List.le_max_of_le' 0 hmem (le_refl _)
    exact hdrop.trans hle
  · have hbefore_zero : (G.withWork remaining).longestTo node = 0 :=
      Nat.eq_zero_of_not_pos hnode_positive
    have hnode_mono : ∀ i,
        G.execute remaining (G.ready remaining) i ≤ remaining i := by
      intro i
      simp only [execute]
      split <;> omega
    have hafter_le := G.longestTo_mono_work _ _ hnode_mono node
    omega

/-- Executing a set of ready nodes consumes exactly one work unit per selected
node. -/
theorem remainingWork_execute_add_card (G : CompDAG) (remaining : ℕ → ℕ)
    (run : Finset ℕ) (hrun : run ⊆ G.ready remaining) :
    G.remainingWork (G.execute remaining run) + run.card =
      G.remainingWork remaining := by
  have hrun_range : run ⊆ Finset.range G.n := by
    intro v hv
    exact Finset.mem_range.mpr ((G.mem_ready_iff remaining v).mp (hrun hv)).1
  have hfilter :
      (Finset.range G.n).filter (fun v => v ∈ run) = run := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun hv => hv.2
    · exact fun hv => ⟨hrun_range hv, hv⟩
  have hcard :
      (∑ v ∈ Finset.range G.n, if v ∈ run then 1 else 0) = run.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [remainingWork, remainingWork, ← hcard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvrun : v ∈ run
  · have hvpos : 0 < remaining v :=
      ((G.mem_ready_iff remaining v).mp (hrun hvrun)).2.1
    simp [execute, hvrun, Nat.sub_add_cancel hvpos]
  · simp [execute, hvrun]


end CompDAG

end Chapter27
end CLRS
