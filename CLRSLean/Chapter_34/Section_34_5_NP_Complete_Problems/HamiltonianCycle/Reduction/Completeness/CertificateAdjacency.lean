import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.CertificateBuilder

/-!
# Adjacency of the cover-induced Hamiltonian certificate

This file proves the path-edge part of the completeness certificate.  It is
kept separate from the later coverage and duplicate-freedom arguments so Lean
can rebuild the difficult layers independently.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem cycleAdjacent_of_endpoint_options
    {I : CliqueInstance} {vertices : List Nat} {first last : Nat}
    (hhead : vertices.head? = some first)
    (hlast : vertices.getLast? = some last)
    (hpath : I.PathAdjacent vertices)
    (hclose : I.Adj last first) :
    I.CycleAdjacent vertices := by
  cases vertices with
  | nil => simp at hhead
  | cons actualFirst rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst actualFirst
      constructor
      · exact hpath
      · rw [CliqueInstance.lastFrom_eq_getLast]
        have hlastEq : (first :: rest).getLast (by simp) = last :=
          (List.getLast_eq_iff_getLast?_eq_some _).2 hlast
        simpa [hlastEq] using hclose

theorem selectedSourceVertexPath_ne_nil
    {I : CliqueInstance} {cover : Finset Nat} {u : Nat}
    (hne : incidentOccurrences I u ≠ []) :
    selectedSourceVertexPath I cover u ≠ [] := by
  obtain ⟨first, rest, hrefs⟩ := List.exists_cons_of_ne_nil hne
  intro hpath
  have hhead := selectedSourceVertexPath_head
    (cover := cover) hrefs
  rw [hpath] at hhead
  simp at hhead

theorem selectedCoverPathFrom_ne_nil
    (I : CliqueInstance) (cover : Finset Nat) (selector u : Nat)
    (vertices : List Nat) :
    selectedCoverPathFrom I cover selector (u :: vertices) ≠ [] := by
  simp [selectedCoverPathFrom]

theorem selectedCoverPathFrom_getLast
    {I : CliqueInstance} {cover : Finset Nat} {selector : Nat}
    {first : Nat} {rest : List Nat}
    (hvertices : ∀ u ∈ first :: rest, incidentOccurrences I u ≠ []) :
    (selectedCoverPathFrom I cover selector (first :: rest)).getLast? =
      (selectedSourceVertexPath I cover
        ((first :: rest).getLast (by simp))).getLast? := by
  induction rest generalizing selector first with
  | nil =>
      have hpathNe := selectedSourceVertexPath_ne_nil (cover := cover)
        (hvertices first (by simp))
      simp only [selectedCoverPathFrom, List.append_nil]
      exact List.getLast?_cons_of_ne_nil hpathNe
  | cons second rest ih =>
      have htailNe := selectedCoverPathFrom_ne_nil I cover
        (selector + 1) second rest
      change
        (selectorVertex I.edges.length selector ::
          (selectedSourceVertexPath I cover first ++
            selectedCoverPathFrom I cover (selector + 1)
              (second :: rest))).getLast? = _
      rw [List.getLast?_cons_of_ne_nil]
      · rw [List.getLast?_append_of_ne_nil _ htailNe]
        simpa only [List.getLast_cons_cons] using ih
          (selector := selector + 1) (first := second) (by
            intro u hu
            exact hvertices u (by simp [hu]))
      · exact List.append_ne_nil_of_right_ne_nil _ htailNe

/-- Consecutive selectors form a path inside the selector clique. -/
theorem selectorRange_pathAdjacent
    (I : CliqueInstance) (start count : Nat)
    (hbound : start + count ≤ I.targetSize) :
    (clrsHamiltonianInstance I).PathAdjacent
      ((List.range' start count).map
        (selectorVertex I.edges.length)) := by
  rw [CliqueInstance.pathAdjacent_iff_isChain]
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
      simp only [List.range'_succ, List.map_cons]
      cases count with
      | zero => simp
      | succ count =>
          apply List.IsChain.cons
          · apply ih (start := start + 1)
            omega
          · simp only [List.range'_succ, List.map_cons, List.head?_cons,
              Option.mem_some_iff]
            intro y hy
            subst y
            apply adj_selector_selector
            · omega
            · omega
            · omega

theorem unusedSelectorPath_pathAdjacent
    {I : CliqueInstance} {usedSelectors : Nat}
    (hused : usedSelectors ≤ I.targetSize) :
    (clrsHamiltonianInstance I).PathAdjacent
      (unusedSelectorPath I usedSelectors) := by
  apply selectorRange_pathAdjacent
  omega

theorem unusedSelectorPath_head
    {I : CliqueInstance} {usedSelectors : Nat}
    (hused : usedSelectors < I.targetSize) :
    (unusedSelectorPath I usedSelectors).head? =
      some (selectorVertex I.edges.length usedSelectors) := by
  have hcount : I.targetSize - usedSelectors =
      (I.targetSize - usedSelectors - 1) + 1 := by
    omega
  rw [unusedSelectorPath, hcount, List.range'_succ, List.map_cons]
  rfl

theorem unusedSelectorPath_getLast
    {I : CliqueInstance} {usedSelectors : Nat}
    (hused : usedSelectors < I.targetSize) :
    (unusedSelectorPath I usedSelectors).getLast? =
      some (selectorVertex I.edges.length (I.targetSize - 1)) := by
  simp only [unusedSelectorPath, List.getLast?_map, List.getLast?_range']
  rw [if_neg (Nat.sub_ne_zero_iff_lt.mpr hused)]
  simp only [Option.map_some, Option.some.injEq]
  apply congrArg (selectorVertex I.edges.length)
  omega

/-- Interleaving selectors with nonempty source-vertex paths preserves path
adjacency. -/
theorem selectedCoverPathFrom_pathAdjacent
    {I : CliqueInstance} {cover : Finset Nat}
    {selector : Nat} {vertices : List Nat}
    (hvertices : ∀ u ∈ vertices,
      u < I.vertexCount ∧ incidentOccurrences I u ≠ [])
    (hselectors : selector + vertices.length ≤ I.targetSize) :
    (clrsHamiltonianInstance I).PathAdjacent
      (selectedCoverPathFrom I cover selector vertices) := by
  rw [CliqueInstance.pathAdjacent_iff_isChain]
  induction vertices generalizing selector with
  | nil => simp [selectedCoverPathFrom]
  | cons u vertices ih =>
      have hu := (hvertices u (by simp)).1
      have huRefs := (hvertices u (by simp)).2
      obtain ⟨first, refs, hrefs⟩ := List.exists_cons_of_ne_nil huRefs
      have hpath : (clrsHamiltonianInstance I).PathAdjacent
          (selectedSourceVertexPath I cover u) :=
        selectedSourceVertexPath_pathAdjacent hu
      have hpathChain :=
        (CliqueInstance.pathAdjacent_iff_isChain _ _).1 hpath
      have hpathNe : selectedSourceVertexPath I cover u ≠ [] :=
        selectedSourceVertexPath_ne_nil huRefs
      have hselector : selector < I.targetSize := by
        simp only [List.length_cons] at hselectors
        omega
      have hselectorFirst : (clrsHamiltonianInstance I).Adj
          (selectorVertex I.edges.length selector)
          (incidentVertex first 0) :=
        adj_selector_incident_first hu hrefs hselector
      cases vertices with
      | nil =>
          simp only [selectedCoverPathFrom, List.append_nil]
          apply List.IsChain.cons hpathChain
          intro y hy
          rw [selectedSourceVertexPath_head hrefs] at hy
          simp only [Option.mem_some_iff] at hy
          subst y
          exact hselectorFirst
      | cons v vertices =>
          have htailProperties : ∀ w ∈ v :: vertices,
              w < I.vertexCount ∧ incidentOccurrences I w ≠ [] := by
            intro w hw
            exact hvertices w (by simp [hw])
          have htailSelectors : selector + 1 + (v :: vertices).length ≤
              I.targetSize := by
            simp only [List.length_cons] at hselectors ⊢
            omega
          have htailChain : List.IsChain
              (clrsHamiltonianInstance I).Adj
              (selectedCoverPathFrom I cover (selector + 1)
                (v :: vertices)) :=
            ih htailProperties htailSelectors
          have hjoined : List.IsChain (clrsHamiltonianInstance I).Adj
              (selectedSourceVertexPath I cover u ++
                selectedCoverPathFrom I cover (selector + 1)
                  (v :: vertices)) := by
            apply List.IsChain.append hpathChain htailChain
            intro x hx y hy
            rw [selectedSourceVertexPath_getLast hrefs] at hx
            rw [selectedCoverPathFrom_head] at hy
            simp only [Option.mem_some_iff] at hx hy
            subst x
            subst y
            apply adj_incident_last_selector hu hrefs
            simp only [List.length_cons] at htailSelectors
            omega
          simp only [selectedCoverPathFrom]
          apply List.IsChain.cons hjoined
          intro y hy
          rw [List.head?_append_of_ne_nil _ hpathNe] at hy
          rw [selectedSourceVertexPath_head hrefs] at hy
          simp only [Option.mem_some_iff] at hy
          subst y
          exact hselectorFirst

theorem selectedCoverPathFrom_active_pathAdjacent
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover)
    (hcard : cover.card ≤ I.targetSize) :
    (clrsHamiltonianInstance I).PathAdjacent
      (selectedCoverPathFrom I cover 0
        (activeCoverVertices I cover)) := by
  apply selectedCoverPathFrom_pathAdjacent
  · intro u hu
    exact ⟨vertex_lt_of_mem_activeCoverVertices hcover hu,
      incidentOccurrences_ne_nil_of_mem_activeCoverVertices hu⟩
  · simpa using activeCoverVertices_length_le_target hcard

theorem coverHamiltonianCertificate_pathAdjacent
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover)
    (hcard : cover.card ≤ I.targetSize)
    (hedges : I.edges ≠ []) :
    (clrsHamiltonianInstance I).PathAdjacent
      (coverHamiltonianCertificate I cover) := by
  let active := activeCoverVertices I cover
  have hactive : active ≠ [] :=
    activeCoverVertices_ne_nil_of_edge hcover hedges
  obtain ⟨first, rest, hactiveEq⟩ := List.exists_cons_of_ne_nil hactive
  have hactiveBound : active.length ≤ I.targetSize :=
    activeCoverVertices_length_le_target hcard
  have hproperties : ∀ u ∈ active,
      u < I.vertexCount ∧ incidentOccurrences I u ≠ [] := by
    intro u hu
    exact ⟨vertex_lt_of_mem_activeCoverVertices hcover hu,
      incidentOccurrences_ne_nil_of_mem_activeCoverVertices hu⟩
  rw [CliqueInstance.pathAdjacent_iff_isChain]
  apply List.IsChain.append
  · exact (CliqueInstance.pathAdjacent_iff_isChain _ _).1
      (selectedCoverPathFrom_active_pathAdjacent hcover hcard)
  · exact (CliqueInstance.pathAdjacent_iff_isChain _ _).1
      (unusedSelectorPath_pathAdjacent hactiveBound)
  · intro x hx y hy
    have hused : active.length < I.targetSize := by
      by_contra hnot
      have heq : I.targetSize - active.length = 0 := by omega
      simp [coverHamiltonianCertificate, active, unusedSelectorPath, heq] at hy
    have hlastMem : (first :: rest).getLast (by simp) ∈ active := by
      rw [hactiveEq]
      exact List.getLast_mem _
    have hlastProperties := hproperties _ hlastMem
    obtain ⟨lastRef, lastRefs, hlastRefs⟩ :=
      List.exists_cons_of_ne_nil hlastProperties.2
    change x ∈ (selectedCoverPathFrom I cover 0 active).getLast? at hx
    rw [hactiveEq, selectedCoverPathFrom_getLast] at hx
    · rw [selectedSourceVertexPath_getLast hlastRefs] at hx
      change y ∈ (unusedSelectorPath I active.length).head? at hy
      rw [unusedSelectorPath_head hused] at hy
      simp only [Option.mem_some_iff] at hx hy
      subst x
      subst y
      apply adj_incident_last_selector hlastProperties.1 hlastRefs hused
    · intro u hu
      exact (hproperties u (by simpa [hactiveEq] using hu)).2

theorem coverHamiltonianCertificate_head
    {I : CliqueInstance} {cover : Finset Nat}
    (hactive : activeCoverVertices I cover ≠ []) :
    (coverHamiltonianCertificate I cover).head? =
      some (selectorVertex I.edges.length 0) := by
  obtain ⟨first, rest, hrefs⟩ := List.exists_cons_of_ne_nil hactive
  have hselectedNe := selectedCoverPathFrom_ne_nil I cover 0 first rest
  rw [coverHamiltonianCertificate, hrefs]
  rw [List.head?_append_of_ne_nil _ hselectedNe]
  simpa using
    selectedCoverPathFrom_head I cover 0 first rest

theorem coverHamiltonianCertificate_cycleAdjacent
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover)
    (hcard : cover.card ≤ I.targetSize)
    (hedges : I.edges ≠ []) :
    (clrsHamiltonianInstance I).CycleAdjacent
      (coverHamiltonianCertificate I cover) := by
  let active := activeCoverVertices I cover
  have hactive : active ≠ [] :=
    activeCoverVertices_ne_nil_of_edge hcover hedges
  obtain ⟨first, rest, hactiveEq⟩ := List.exists_cons_of_ne_nil hactive
  have hactiveBound : active.length ≤ I.targetSize :=
    activeCoverVertices_length_le_target hcard
  have hproperties : ∀ u ∈ active,
      u < I.vertexCount ∧ incidentOccurrences I u ≠ [] := by
    intro u hu
    exact ⟨vertex_lt_of_mem_activeCoverVertices hcover hu,
      incidentOccurrences_ne_nil_of_mem_activeCoverVertices hu⟩
  have hhead : (coverHamiltonianCertificate I cover).head? =
      some (selectorVertex I.edges.length 0) := by
    apply coverHamiltonianCertificate_head
    simpa [active]
  have hpath := coverHamiltonianCertificate_pathAdjacent hcover hcard hedges
  have hpositive : 0 < I.targetSize := by
    have hlen : 0 < active.length := by
      rw [hactiveEq]
      simp
    omega
  by_cases hunused : active.length < I.targetSize
  · have hunusedNe : unusedSelectorPath I active.length ≠ [] := by
      simp [unusedSelectorPath, Nat.sub_ne_zero_iff_lt.mpr hunused]
    have hlast : (coverHamiltonianCertificate I cover).getLast? =
        some (selectorVertex I.edges.length (I.targetSize - 1)) := by
      rw [coverHamiltonianCertificate]
      rw [List.getLast?_append_of_ne_nil _ hunusedNe]
      exact unusedSelectorPath_getLast hunused
    apply cycleAdjacent_of_endpoint_options hhead hlast hpath
    apply adj_selector_selector
    · omega
    · exact hpositive
    · have hlen : 0 < active.length := by
        rw [hactiveEq]
        simp
      omega
  · have husedEq : active.length = I.targetSize := by omega
    have hunusedEmpty : unusedSelectorPath I active.length = [] := by
      simp [unusedSelectorPath, husedEq]
    have hlastMem : (first :: rest).getLast (by simp) ∈ active := by
      rw [hactiveEq]
      exact List.getLast_mem _
    have hlastProperties := hproperties _ hlastMem
    obtain ⟨lastRef, lastRefs, hlastRefs⟩ :=
      List.exists_cons_of_ne_nil hlastProperties.2
    have hlast : (coverHamiltonianCertificate I cover).getLast? =
        some (incidentVertex ((lastRef :: lastRefs).getLast (by simp)) 5) := by
      rw [coverHamiltonianCertificate]
      rw [hunusedEmpty, List.append_nil]
      change (selectedCoverPathFrom I cover 0 active).getLast? = _
      rw [hactiveEq]
      rw [selectedCoverPathFrom_getLast]
      · exact selectedSourceVertexPath_getLast hlastRefs
      · intro u hu
        exact (hproperties u (by simpa [hactiveEq] using hu)).2
    apply cycleAdjacent_of_endpoint_options hhead hlast hpath
    exact adj_incident_last_selector hlastProperties.1 hlastRefs hpositive

end CLRS.Chapter34.HamiltonianCycleReduction
