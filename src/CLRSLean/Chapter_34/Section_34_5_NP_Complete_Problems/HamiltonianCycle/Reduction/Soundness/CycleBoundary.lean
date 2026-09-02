import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CycleEdges

/-!
# Boundary edges in a cyclic list

A nonempty proper subset of a duplicate-free cyclic list has an edge crossing
its boundary.  This rules out a gadget that closes into a smaller cycle inside
one Hamiltonian certificate and is also reusable for selector counting.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem exists_adjacent_boundary
    {vertices : List Nat} {P : Nat → Prop}
    (hinside : ∃ vertex ∈ vertices, P vertex)
    (houtside : ∃ vertex ∈ vertices, ¬ P vertex) :
    ∃ pre u v suffix,
      vertices = pre ++ u :: v :: suffix ∧
        ((P u ∧ ¬ P v) ∨ (¬ P u ∧ P v)) := by
  classical
  induction vertices with
  | nil => simp at hinside
  | cons x xs ih =>
      cases xs with
      | nil => simp at hinside houtside; aesop
      | cons y ys =>
          by_cases hx : P x
          · by_cases hy : P y
            · have houtsideTail : ∃ vertex ∈ y :: ys, ¬ P vertex := by
                rcases houtside with ⟨vertex, hvertex, hnot⟩
                refine ⟨vertex, ?_, hnot⟩
                simp only [List.mem_cons] at hvertex ⊢
                rcases hvertex with rfl | htail
                · exact (hnot hx).elim
                · exact htail
              rcases ih ⟨y, by simp, hy⟩ houtsideTail with
                ⟨pre, u, v, suffix, heq, hboundary⟩
              exact ⟨x :: pre, u, v, suffix, by simp [heq], hboundary⟩
            · exact ⟨[], x, y, ys, rfl, Or.inl ⟨hx, hy⟩⟩
          · by_cases hy : P y
            · exact ⟨[], x, y, ys, rfl, Or.inr ⟨hx, hy⟩⟩
            · have hinsideTail : ∃ vertex ∈ y :: ys, P vertex := by
                rcases hinside with ⟨vertex, hvertex, hpos⟩
                refine ⟨vertex, ?_, hpos⟩
                simp only [List.mem_cons] at hvertex ⊢
                rcases hvertex with rfl | htail
                · exact (hx hpos).elim
                · exact htail
              rcases ih hinsideTail ⟨y, by simp, hy⟩ with
                ⟨pre, u, v, suffix, heq, hboundary⟩
              exact ⟨x :: pre, u, v, suffix, by simp [heq], hboundary⟩

theorem cycleLinked_of_adjacent
    {vertices pre suffix : List Nat} {u v : Nat}
    (hnodup : vertices.Nodup)
    (heq : vertices = pre ++ u :: v :: suffix) :
    CycleLinked vertices u v := by
  subst vertices
  have hnotPrefix : u ∉ pre := by
    have hnodupAppend := hnodup
    rw [List.nodup_append] at hnodupAppend
    exact fun hu => hnodupAppend.2.2 u hu u (by simp) rfl
  have hu : u ∈ pre ++ u :: v :: suffix := by simp
  rw [cycleLinked_iff hu]
  left
  rw [List.next_eq_getElem hu]
  have hidx : (pre ++ u :: v :: suffix).idxOf u = pre.length := by
    rw [List.idxOf_append_of_notMem hnotPrefix]
    simp
  rw [hidx]
  have hlt : pre.length + 1 < (pre ++ u :: v :: suffix).length := by
    simp
  simp only [Nat.mod_eq_of_lt hlt]
  simp

theorem exists_cycleLinked_boundary
    {vertices : List Nat} (hnodup : vertices.Nodup)
    {P : Nat → Prop}
    (hinside : ∃ vertex ∈ vertices, P vertex)
    (houtside : ∃ vertex ∈ vertices, ¬ P vertex) :
    ∃ u v, P u ∧ ¬ P v ∧ CycleLinked vertices u v := by
  rcases exists_adjacent_boundary hinside houtside with
    ⟨pre, u, v, suffix, heq, hboundary⟩
  have hlinked := cycleLinked_of_adjacent hnodup heq
  rcases hboundary with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact ⟨u, v, hu, hv, hlinked⟩
  · exact ⟨v, u, hv, hu, cycleLinked_symm hnodup hlinked⟩

theorem all_mem_of_cycleLinked_closed
    {vertices : List Nat} (hnodup : vertices.Nodup)
    {P : Nat → Prop}
    (hinside : ∃ vertex ∈ vertices, P vertex)
    (hclosed : ∀ u, u ∈ vertices → P u →
      ∀ v, CycleLinked vertices u v → P v) :
    ∀ vertex ∈ vertices, P vertex := by
  intro vertex hvertex
  by_contra houtside
  rcases exists_cycleLinked_boundary hnodup hinside
      ⟨vertex, hvertex, houtside⟩ with
    ⟨u, v, hu, hv, hlinked⟩
  exact hv (hclosed u (by
    rcases hlinked with ⟨hmem, _⟩
    exact hmem) hu v hlinked)

end CLRS.Chapter34.HamiltonianCycleReduction
