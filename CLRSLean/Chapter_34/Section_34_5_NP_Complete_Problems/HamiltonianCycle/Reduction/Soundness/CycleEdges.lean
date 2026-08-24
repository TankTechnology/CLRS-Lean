import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CycleCore

/-!
# Edges used by an ordered Hamiltonian cycle

`CycleLinked vertices u v` forgets the orientation of the certificate list:
`v` is either the cyclic successor or predecessor of `u`.  This proof-free
relation is symmetric on duplicate-free lists and lets the finite gadget
argument reason about undirected cycle edges.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def CycleLinked (vertices : List Nat) (u v : Nat) : Prop :=
  ∃ hu : u ∈ vertices,
    vertices.next u hu = v ∨ vertices.prev u hu = v

theorem cycleLinked_iff
    {vertices : List Nat} {u v : Nat} (hu : u ∈ vertices) :
    CycleLinked vertices u v ↔
      vertices.next u hu = v ∨ vertices.prev u hu = v := by
  simp only [CycleLinked]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · exact fun h => ⟨hu, h⟩

theorem cycleLinked_symm
    {vertices : List Nat} (hnodup : vertices.Nodup)
    {u v : Nat} (hlinked : CycleLinked vertices u v) :
    CycleLinked vertices v u := by
  rcases hlinked with ⟨hu, hnext | hprev⟩
  · subst v
    refine ⟨List.next_mem vertices u hu, Or.inr ?_⟩
    exact List.prev_next vertices hnodup u hu
  · subst v
    refine ⟨List.prev_mem vertices u hu, Or.inl ?_⟩
    exact List.next_prev vertices hnodup u hu

theorem adj_of_cycleLinked
    {I : CliqueInstance} {vertices : List Nat}
    (hnodup : vertices.Nodup) (hcycle : I.CycleAdjacent vertices)
    {u v : Nat} (hlinked : CycleLinked vertices u v) :
    I.Adj u v := by
  rcases hlinked with ⟨hu, hnext | hprev⟩
  · rw [← hnext]
    exact I.adj_next_of_cycleAdjacent hnodup hcycle hu
  · rw [← hprev]
    exact I.adj_prev_of_cycleAdjacent hnodup hcycle hu

theorem cycleLinked_next
    {vertices : List Nat} {u : Nat} (hu : u ∈ vertices) :
    CycleLinked vertices u (vertices.next u hu) :=
  ⟨hu, Or.inl rfl⟩

theorem cycleLinked_prev
    {vertices : List Nat} {u : Nat} (hu : u ∈ vertices) :
    CycleLinked vertices u (vertices.prev u hu) :=
  ⟨hu, Or.inr rfl⟩

theorem cycleLinked_pair_of_neighbors
    {vertices : List Nat} {u first second : Nat} (hu : u ∈ vertices)
    (hneighbors :
      (vertices.next u hu = first ∧ vertices.prev u hu = second) ∨
      (vertices.next u hu = second ∧ vertices.prev u hu = first)) :
    CycleLinked vertices u first ∧ CycleLinked vertices u second := by
  rcases hneighbors with ⟨hnext, hprev⟩ | ⟨hnext, hprev⟩
  · exact ⟨⟨hu, Or.inl hnext⟩, ⟨hu, Or.inr hprev⟩⟩
  · exact ⟨⟨hu, Or.inr hprev⟩, ⟨hu, Or.inl hnext⟩⟩

/-- Once two distinct cyclic neighbors are known, no third distinct vertex
can also be a cyclic neighbor. -/
theorem not_cycleLinked_of_two
    {vertices : List Nat} {u first second third : Nat}
    (hu : u ∈ vertices)
    (hfirst : CycleLinked vertices u first)
    (hsecond : CycleLinked vertices u second)
    (hfirstSecond : first ≠ second)
    (hthirdFirst : third ≠ first)
    (hthirdSecond : third ≠ second) :
    ¬ CycleLinked vertices u third := by
  rw [cycleLinked_iff hu] at hfirst hsecond ⊢
  rcases hfirst with hnextFirst | hprevFirst
  · rcases hsecond with hnextSecond | hprevSecond
    · exact (hfirstSecond (hnextFirst.symm.trans hnextSecond)).elim
    · rintro (hnextThird | hprevThird)
      · exact hthirdFirst (hnextThird.symm.trans hnextFirst)
      · exact hthirdSecond (hprevThird.symm.trans hprevSecond)
  · rcases hsecond with hnextSecond | hprevSecond
    · rintro (hnextThird | hprevThird)
      · exact hthirdSecond (hnextThird.symm.trans hnextSecond)
      · exact hthirdFirst (hprevThird.symm.trans hprevFirst)
    · exact (hfirstSecond (hprevFirst.symm.trans hprevSecond)).elim

/-- At a three-neighbor graph vertex, once the cycle is known to use the
first neighbor, it must use at least one of the other two. -/
theorem cycleLinked_other_of_adj_iff_three
    {I : CliqueInstance} {vertices : List Nat}
    (hnodup : vertices.Nodup) (hlength : 3 ≤ vertices.length)
    (hcycle : I.CycleAdjacent vertices)
    {u first second third : Nat} (hu : u ∈ vertices)
    (hadj : ∀ vertex,
      I.Adj u vertex ↔
        vertex = first ∨ vertex = second ∨ vertex = third)
    (hfirst : CycleLinked vertices u first) :
    CycleLinked vertices u second ∨ CycleLinked vertices u third := by
  have hne := CliqueInstance.next_ne_prev_of_three_le_length
    hnodup hlength hu
  rw [cycleLinked_iff hu] at hfirst
  rcases hfirst with hnextFirst | hprevFirst
  · have hprevAdj := (hadj _).1
      (I.adj_prev_of_cycleAdjacent hnodup hcycle hu)
    rcases hprevAdj with hprev | hprev | hprev
    · exact (hne (hnextFirst.trans hprev.symm)).elim
    · exact Or.inl ⟨hu, Or.inr hprev⟩
    · exact Or.inr ⟨hu, Or.inr hprev⟩
  · have hnextAdj := (hadj _).1
      (I.adj_next_of_cycleAdjacent hnodup hcycle hu)
    rcases hnextAdj with hnext | hnext | hnext
    · exact (hne (hnext.trans hprevFirst.symm)).elim
    · exact Or.inl ⟨hu, Or.inl hnext⟩
    · exact Or.inr ⟨hu, Or.inl hnext⟩

end CLRS.Chapter34.HamiltonianCycleReduction
