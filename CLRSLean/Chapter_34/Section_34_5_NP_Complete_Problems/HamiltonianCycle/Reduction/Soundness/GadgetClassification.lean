import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.ClosedGadget

/-!
# The three allowed Hamiltonian traversals of a gadget

After excluding the closed twelve-vertex subcycle, the four branch choices
collapse to exactly the three traversal shapes used in the CLRS proof.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def UsesWidgetSplitTraversal (vertices : List Nat) (occurrence : Nat) : Prop :=
  CycleLinked vertices (globalWidgetVertex occurrence 2)
      (globalWidgetVertex occurrence 3) ∧
    CycleLinked vertices (globalWidgetVertex occurrence 8)
      (globalWidgetVertex occurrence 9)

def UsesWidgetLeftFullTraversal
    (vertices : List Nat) (occurrence : Nat) : Prop :=
  CycleLinked vertices (globalWidgetVertex occurrence 2)
      (globalWidgetVertex occurrence 6) ∧
    CycleLinked vertices (globalWidgetVertex occurrence 3)
      (globalWidgetVertex occurrence 11) ∧
    CycleLinked vertices (globalWidgetVertex occurrence 8)
      (globalWidgetVertex occurrence 9)

def UsesWidgetRightFullTraversal
    (vertices : List Nat) (occurrence : Nat) : Prop :=
  CycleLinked vertices (globalWidgetVertex occurrence 2)
      (globalWidgetVertex occurrence 3) ∧
    CycleLinked vertices (globalWidgetVertex occurrence 8)
      (globalWidgetVertex occurrence 0) ∧
    CycleLinked vertices (globalWidgetVertex occurrence 9)
      (globalWidgetVertex occurrence 5)

theorem cycle_uses_allowed_widget_traversal
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    UsesWidgetSplitTraversal vertices occurrence ∨
      UsesWidgetLeftFullTraversal vertices occurrence ∨
      UsesWidgetRightFullTraversal vertices occurrence := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hone := cycleLinked_globalWidgetVertex_one_pair hfull hoccurrence
  have hseven := cycleLinked_globalWidgetVertex_seven_pair hfull hoccurrence
  have hmem2 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 2 < widgetVertexCount by decide)
  have hmem8 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 8 < widgetVertexCount by decide)
  have h21 := cycleLinked_symm hnodup hone.2
  have h87 := cycleLinked_symm hnodup hseven.2
  rcases cycleLinked_globalWidgetVertex_two_choice hfull hoccurrence with
    h23 | h26
  · rcases cycleLinked_globalWidgetVertex_eight_choice hfull hoccurrence with
      h89 | h80
    · exact Or.inl ⟨h23, h89⟩
    · have hnot89 : ¬CycleLinked vertices
          (globalWidgetVertex occurrence 8)
          (globalWidgetVertex occurrence 9) := by
        exact not_cycleLinked_of_two hmem8 h87 h80
          (by simp [globalWidgetVertex])
          (by simp [globalWidgetVertex])
          (by simp [globalWidgetVertex])
      have h95 : CycleLinked vertices (globalWidgetVertex occurrence 9)
          (globalWidgetVertex occurrence 5) := by
        rcases cycleLinked_globalWidgetVertex_nine_choice hfull hoccurrence with
          h98 | h95
        · exact (hnot89 (cycleLinked_symm hnodup h98)).elim
        · exact h95
      exact Or.inr (Or.inr ⟨h23, h80, h95⟩)
  · have hnot23 : ¬CycleLinked vertices
        (globalWidgetVertex occurrence 2)
        (globalWidgetVertex occurrence 3) := by
      exact not_cycleLinked_of_two hmem2 h21 h26
        (by simp [globalWidgetVertex])
        (by simp [globalWidgetVertex])
        (by simp [globalWidgetVertex])
    have h311 : CycleLinked vertices (globalWidgetVertex occurrence 3)
        (globalWidgetVertex occurrence 11) := by
      rcases cycleLinked_globalWidgetVertex_three_choice hfull hoccurrence with
        h32 | h311
      · exact (hnot23 (cycleLinked_symm hnodup h32)).elim
      · exact h311
    rcases cycleLinked_globalWidgetVertex_eight_choice hfull hoccurrence with
      h89 | h80
    · exact Or.inr (Or.inl ⟨h26, h311, h89⟩)
    · have hnot89 : ¬CycleLinked vertices
          (globalWidgetVertex occurrence 8)
          (globalWidgetVertex occurrence 9) := by
        exact not_cycleLinked_of_two hmem8 h87 h80
          (by simp [globalWidgetVertex])
          (by simp [globalWidgetVertex])
          (by simp [globalWidgetVertex])
      have h95 : CycleLinked vertices (globalWidgetVertex occurrence 9)
          (globalWidgetVertex occurrence 5) := by
        rcases cycleLinked_globalWidgetVertex_nine_choice hfull hoccurrence with
          h98 | h95
        · exact (hnot89 (cycleLinked_symm hnodup h98)).elim
        · exact h95
      exact (not_closed_widget_crossing_pattern hfull htarget hoccurrence
        ⟨h26, h311, h80, h95⟩).elim

end CLRS.Chapter34.HamiltonianCycleReduction
