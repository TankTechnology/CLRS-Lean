import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.ChainEndpoints

/-!
# The selector budget

Every selected source vertex supplies two distinct endpoint ports.  Each such
port reaches a selector through one of that selector's two cyclic directions.
The resulting map into `selector × {next, prev}` is injective, so at most `k`
source vertices can be selected.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def endpointTagPosition (rightEndpoint : Bool) : Nat :=
  if rightEndpoint then 5 else 0

noncomputable def cycleSelectedEndpointTags
    (I : CliqueInstance) (vertices : List Nat) : Finset (Nat × Bool) :=
  (cycleSelectedSourceVertices I vertices).product Finset.univ

def EndpointRealization
    (I : CliqueInstance) (vertices : List Nat)
    (tag : Nat × Bool) (port : Nat) (selector : Fin I.targetSize) : Prop :=
  ∃ endpoint,
    endpoint ∈ incidentOccurrences I tag.1 ∧
    port = incidentVertex endpoint (endpointTagPosition tag.2) ∧
    CycleLinked vertices port
      (selectorVertex I.edges.length selector)

theorem exists_endpointRealization
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {tag : Nat × Bool}
    (htag : tag ∈ cycleSelectedEndpointTags I vertices) :
    ∃ port selector, EndpointRealization I vertices tag port selector := by
  classical
  rcases Finset.mem_product.mp htag with ⟨hsource, _⟩
  have hselects := (mem_cycleSelectedSourceVertices_iff.mp hsource).2
  rcases hselects with ⟨ref, href, hselected⟩
  cases tag with
  | mk u rightEndpoint =>
      cases rightEndpoint with
      | false =>
          obtain ⟨endpoint, hendpointMem, _, _, selector,
              hselectorLt, hlinked⟩ :=
            exists_left_selector_endpoint hcycle htarget href hselected
          exact ⟨incidentVertex endpoint 0, ⟨selector, hselectorLt⟩,
            endpoint, hendpointMem, by simp [endpointTagPosition], hlinked⟩
      | true =>
          obtain ⟨endpoint, hendpointMem, _, _, selector,
              hselectorLt, hlinked⟩ :=
            exists_right_selector_endpoint hcycle htarget href hselected
          exact ⟨incidentVertex endpoint 5, ⟨selector, hselectorLt⟩,
            endpoint, hendpointMem, by simp [endpointTagPosition], hlinked⟩

theorem tag_eq_of_endpointRealization_same_port
    {I : CliqueInstance} {vertices : List Nat}
    {firstTag secondTag : Nat × Bool} {port : Nat}
    {firstSelector secondSelector : Fin I.targetSize}
    (hfirst : EndpointRealization I vertices firstTag port firstSelector)
    (hsecond : EndpointRealization I vertices secondTag port secondSelector) :
    firstTag = secondTag := by
  rcases firstTag with ⟨firstSource, firstSide⟩
  rcases secondTag with ⟨secondSource, secondSide⟩
  rcases hfirst with ⟨firstEndpoint, hfirstMem, hfirstPort, _⟩
  rcases hsecond with ⟨secondEndpoint, hsecondMem, hsecondPort, _⟩
  have hfirstPosition : endpointTagPosition firstSide < 6 := by
    cases firstSide <;> simp [endpointTagPosition]
  have hsecondPosition : endpointTagPosition secondSide < 6 := by
    cases secondSide <;> simp [endpointTagPosition]
  have hident := incidentVertex_injective hfirstPosition hsecondPosition
    (hfirstPort.symm.trans hsecondPort)
  have hsource := source_eq_of_mem_incidentOccurrences hfirstMem
    (hident.1 ▸ hsecondMem)
  have hside : firstSide = secondSide := by
    cases firstSide <;> cases secondSide <;>
      simp [endpointTagPosition] at hident ⊢
  exact Prod.ext hsource hside

def CycleSelectorSlotRealizes
    (I : CliqueInstance) (vertices : List Nat)
    (slot : Fin I.targetSize × Bool) (port : Nat) : Prop :=
  ∃ hmem : selectorVertex I.edges.length slot.1 ∈ vertices,
    if slot.2 then
      vertices.next (selectorVertex I.edges.length slot.1) hmem = port
    else
      vertices.prev (selectorVertex I.edges.length slot.1) hmem = port

theorem exists_cycleSelectorSlotRealizes
    {I : CliqueInstance} {vertices : List Nat}
    (hnodup : vertices.Nodup)
    {tag : Nat × Bool} {port : Nat} {selector : Fin I.targetSize}
    (hrealization : EndpointRealization I vertices tag port selector) :
    ∃ orientation,
      CycleSelectorSlotRealizes I vertices (selector, orientation) port := by
  rcases hrealization with ⟨_, _, _, hlinked⟩
  rcases cycleLinked_symm hnodup hlinked with ⟨hmem, hnext | hprev⟩
  · exact ⟨true, hmem, by simpa using hnext⟩
  · exact ⟨false, hmem, by simpa using hprev⟩

theorem port_eq_of_cycleSelectorSlotRealizes
    {I : CliqueInstance} {vertices : List Nat}
    {slot : Fin I.targetSize × Bool} {firstPort secondPort : Nat}
    (hfirst : CycleSelectorSlotRealizes I vertices slot firstPort)
    (hsecond : CycleSelectorSlotRealizes I vertices slot secondPort) :
    firstPort = secondPort := by
  rcases slot with ⟨selector, orientation⟩
  rcases hfirst with ⟨hfirstMem, hfirst⟩
  rcases hsecond with ⟨hsecondMem, hsecond⟩
  cases orientation
  · change vertices.prev (selectorVertex I.edges.length selector)
        hfirstMem = firstPort at hfirst
    change vertices.prev (selectorVertex I.edges.length selector)
        hsecondMem = secondPort at hsecond
    exact hfirst.symm.trans hsecond
  · change vertices.next (selectorVertex I.edges.length selector)
        hfirstMem = firstPort at hfirst
    change vertices.next (selectorVertex I.edges.length selector)
        hsecondMem = secondPort at hsecond
    exact hfirst.symm.trans hsecond

structure TagSlotWitness
    (I : CliqueInstance) (vertices : List Nat) (tag : Nat × Bool) where
  port : Nat
  slot : Fin I.targetSize × Bool
  endpointRealization :
    EndpointRealization I vertices tag port slot.1
  slotRealization : CycleSelectorSlotRealizes I vertices slot port

theorem exists_tagSlotWitness
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {tag : Nat × Bool}
    (htag : tag ∈ cycleSelectedEndpointTags I vertices) :
    Nonempty (TagSlotWitness I vertices tag) := by
  obtain ⟨port, selector, hrealization⟩ :=
    exists_endpointRealization hcycle htarget htag
  obtain ⟨orientation, hslot⟩ :=
    exists_cycleSelectorSlotRealizes hcycle.2.1 hrealization
  exact ⟨⟨port, (selector, orientation), hrealization, hslot⟩⟩

noncomputable def chosenTagSlotWitness
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    (tag : ↑(cycleSelectedEndpointTags I vertices)) :
    TagSlotWitness I vertices tag.1 :=
  Classical.choice (exists_tagSlotWitness hcycle htarget tag.2)

noncomputable def chosenTagSlot
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize) :
    ↑(cycleSelectedEndpointTags I vertices) → Fin I.targetSize × Bool :=
  fun tag => (chosenTagSlotWitness hcycle htarget tag).slot

theorem chosenTagSlot_injective
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize) :
    Function.Injective (chosenTagSlot hcycle htarget) := by
  intro first second hslots
  let firstWitness := chosenTagSlotWitness hcycle htarget first
  let secondWitness := chosenTagSlotWitness hcycle htarget second
  have hslots' : firstWitness.slot = secondWitness.slot := by
    simpa [firstWitness, secondWitness, chosenTagSlot] using hslots
  have hsecondSlot : CycleSelectorSlotRealizes I vertices
      firstWitness.slot secondWitness.port := by
    rw [hslots']
    exact secondWitness.slotRealization
  have hports : firstWitness.port = secondWitness.port :=
    port_eq_of_cycleSelectorSlotRealizes
      firstWitness.slotRealization hsecondSlot
  have hsecondEndpoint : EndpointRealization I vertices second.1
      firstWitness.port secondWitness.slot.1 := by
    simpa [hports] using secondWitness.endpointRealization
  apply Subtype.ext
  exact tag_eq_of_endpointRealization_same_port
    firstWitness.endpointRealization hsecondEndpoint

theorem cycleSelectedSourceVertices_card_le_targetSize
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize) :
    (cycleSelectedSourceVertices I vertices).card ≤ I.targetSize := by
  classical
  have hcard := Fintype.card_le_of_injective
    (chosenTagSlot hcycle htarget)
    (chosenTagSlot_injective hcycle htarget)
  have htagsCard : (cycleSelectedEndpointTags I vertices).card =
      (cycleSelectedSourceVertices I vertices).card * 2 := by
    simp [cycleSelectedEndpointTags]
  rw [Fintype.card_coe, htagsCard] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool] at hcard
  omega

end CLRS.Chapter34.HamiltonianCycleReduction
