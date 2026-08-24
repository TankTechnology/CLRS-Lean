import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Instance
import Mathlib.Data.List.Cycle

/-!
# A local-neighbor interface for ordered Hamiltonian cycles

The language-level certificate uses a list.  Gadget soundness is easier to
state using the cyclic predecessor and successor of a vertex.  This module
bridges those views once, independently of the later reduction graph.
-/

namespace CLRS.Chapter34

namespace CliqueInstance

theorem pathAdjacent_iff_isChain (I : CliqueInstance) (vertices : List Nat) :
    I.PathAdjacent vertices ↔ vertices.IsChain I.Adj := by
  induction vertices using List.twoStepInduction with
  | nil => simp [PathAdjacent]
  | singleton v => simp [PathAdjacent]
  | cons_cons u v rest _ ih =>
      simp only [PathAdjacent, List.isChain_cons_cons, ih]

theorem lastFrom_eq_getLast (first : Nat) (rest : List Nat) :
    lastFrom first rest = (first :: rest).getLast (by simp) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      simpa [lastFrom] using ih next

theorem adj_getLast_head_of_cycleAdjacent
    (I : CliqueInstance) {vertices : List Nat}
    (hne : vertices ≠ []) (hcycle : I.CycleAdjacent vertices) :
    I.Adj (vertices.getLast hne) (vertices.head hne) := by
  cases vertices with
  | nil => exact (hne rfl).elim
  | cons first rest =>
      simpa [CycleAdjacent, lastFrom_eq_getLast] using hcycle.2

/-- The cyclic successor in an ordered cycle is joined to the current vertex. -/
theorem adj_next_of_cycleAdjacent
    (I : CliqueInstance) {vertices : List Nat}
    (hnodup : vertices.Nodup) (hcycle : I.CycleAdjacent vertices)
    {v : Nat} (hv : v ∈ vertices) :
    I.Adj v (vertices.next v hv) := by
  have hne : vertices ≠ [] := List.ne_nil_of_mem hv
  have hpath : I.PathAdjacent vertices := by
    cases vertices with
    | nil => exact (hne rfl).elim
    | cons first rest => exact hcycle.1
  have hchain : vertices.IsChain I.Adj :=
    (I.pathAdjacent_iff_isChain vertices).1 hpath
  by_cases hdrop : v ∈ vertices.dropLast
  · have hinfix : [v, vertices.next v hv] <:+: vertices := by
      unfold List.next
      exact List.nextOr_infix_of_mem_dropLast hdrop _
    exact List.isChain_pair.mp (hchain.infix hinfix)
  · have hvlast : v = vertices.getLast hne := by
      by_contra hneLast
      exact hdrop (List.mem_dropLast_of_mem_of_ne_getLast hv hneLast)
    subst v
    rw [List.next_getLast_eq_head vertices hne hnodup]
    exact I.adj_getLast_head_of_cycleAdjacent hne hcycle

/-- The cyclic predecessor in an ordered cycle is joined to the current vertex. -/
theorem adj_prev_of_cycleAdjacent
    (I : CliqueInstance) {vertices : List Nat}
    (hnodup : vertices.Nodup) (hcycle : I.CycleAdjacent vertices)
    {v : Nat} (hv : v ∈ vertices) :
    I.Adj v (vertices.prev v hv) := by
  have hprev := I.adj_next_of_cycleAdjacent hnodup hcycle
    (List.prev_mem vertices v hv)
  rw [List.next_prev vertices hnodup v hv] at hprev
  exact (I.adj_comm _ _).2 hprev

/-- In a duplicate-free cycle of length at least three, predecessor and
successor are different vertices. -/
theorem next_ne_prev_of_three_le_length
    {vertices : List Nat} (hnodup : vertices.Nodup)
    (hlength : 3 ≤ vertices.length) {v : Nat} (hv : v ∈ vertices) :
    vertices.next v hv ≠ vertices.prev v hv := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  rw [List.next_getElem vertices hnodup i hi,
    List.prev_getElem vertices hnodup i hi]
  intro heq
  have hindex := (List.nodup_iff_injective_get.mp hnodup) heq
  have hmod :
      (i + 1) % vertices.length =
        (i + (vertices.length - 1)) % vertices.length := by
    exact Fin.val_eq_of_eq hindex
  cases i with
  | zero =>
      have hone : 1 < vertices.length := by omega
      have hpred : vertices.length - 1 < vertices.length := by omega
      simp only [Nat.zero_add, Nat.mod_eq_of_lt hone,
        Nat.mod_eq_of_lt hpred] at hmod
      omega
  | succ j =>
      have hj : j < vertices.length := by omega
      have hright :
          j + 1 + (vertices.length - 1) = j + vertices.length := by
        omega
      rw [hright, Nat.add_mod_right, Nat.mod_eq_of_lt hj] at hmod
      by_cases hsucc : j + 2 < vertices.length
      · rw [Nat.mod_eq_of_lt hsucc] at hmod
        omega
      · have heq : j + 2 = vertices.length := by omega
        rw [heq, Nat.mod_self] at hmod
        omega

/-- A duplicate-free in-range list of the full vertex count contains every
vertex in that range. -/
theorem mem_of_lt_of_full_cycle_list
    {I : CliqueInstance} {vertices : List Nat}
    (hnodup : vertices.Nodup)
    (hlength : vertices.length = I.vertexCount)
    (hbound : ∀ w ∈ vertices, w < I.vertexCount)
    {v : Nat} (hv : v < I.vertexCount) :
    v ∈ vertices := by
  have hsubset : vertices.toFinset ⊆ Finset.range I.vertexCount := by
    intro w hw
    exact Finset.mem_range.mpr (hbound w (List.mem_toFinset.mp hw))
  have hcard : vertices.toFinset.card = I.vertexCount := by
    rw [List.toFinset_card_of_nodup hnodup, hlength]
  have heq : vertices.toFinset = Finset.range I.vertexCount := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [hcard]
  exact List.mem_toFinset.mp (heq.symm ▸ Finset.mem_range.mpr hv)

/-- A degree-two graph neighborhood fixes the two cyclic neighbors, up to
orientation. -/
theorem cycle_neighbors_of_adj_iff_pair
    (I : CliqueInstance) {vertices : List Nat}
    (hnodup : vertices.Nodup) (hlength : 3 ≤ vertices.length)
    (hcycle : I.CycleAdjacent vertices)
    {v left right : Nat} (hv : v ∈ vertices)
    (hadj : ∀ w, I.Adj v w ↔ w = left ∨ w = right) :
    (vertices.next v hv = left ∧ vertices.prev v hv = right) ∨
      (vertices.next v hv = right ∧ vertices.prev v hv = left) := by
  have hnext := (hadj _).1 (I.adj_next_of_cycleAdjacent hnodup hcycle hv)
  have hprev := (hadj _).1 (I.adj_prev_of_cycleAdjacent hnodup hcycle hv)
  have hne := next_ne_prev_of_three_le_length hnodup hlength hv
  rcases hnext with hnext | hnext <;>
    rcases hprev with hprev | hprev <;> aesop

end CliqueInstance

end CLRS.Chapter34
