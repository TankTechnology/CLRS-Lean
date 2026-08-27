import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Operations

/-!
# Refinement from binary heaps to sorted Huffman queues

The ordered entry list is a proof-only observation.  The executable operations use
only the array heap; sorting appears solely in the refinement specification.
-/

namespace CLRS.HuffmanV2

/-- Insert one entry into a priority-sorted proof view. -/
def insertEntry (e : HeapEntry) : List HeapEntry → List HeapEntry
  | [] => [e]
  | u :: us =>
      if HeapEntry.PriorityLE e u then e :: u :: us
      else u :: insertEntry e us

/-- Canonical priority-sorted observation of an entry multiset. -/
def orderedEntries : List HeapEntry → List HeapEntry
  | [] => []
  | e :: es => insertEntry e (orderedEntries es)

@[simp] theorem insertEntry_length (e : HeapEntry) (es : List HeapEntry) :
    (insertEntry e es).length = es.length + 1 := by
  induction es with
  | nil => rfl
  | cons u us ih => simp [insertEntry]; split <;> simp [ih]

theorem insertEntry_perm (e : HeapEntry) (es : List HeapEntry) :
    (insertEntry e es).Perm (e :: es) := by
  induction es with
  | nil => rfl
  | cons u us ih =>
      simp only [insertEntry]
      split
      · rfl
      · exact (List.Perm.cons u ih).trans (List.Perm.swap u e us).symm

@[simp] theorem orderedEntries_length (es : List HeapEntry) :
    (orderedEntries es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [orderedEntries, ih]

theorem orderedEntries_perm (es : List HeapEntry) :
    (orderedEntries es).Perm es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      exact (insertEntry_perm e (orderedEntries es)).trans (List.Perm.cons e ih)

theorem mem_insertEntry (x e : HeapEntry) (es : List HeapEntry) :
    x ∈ insertEntry e es ↔ x = e ∨ x ∈ es := by
  simpa only [List.mem_cons] using List.Perm.mem_iff (insertEntry_perm e es)

theorem mem_orderedEntries (x : HeapEntry) (es : List HeapEntry) :
    x ∈ orderedEntries es ↔ x ∈ es :=
  List.Perm.mem_iff (orderedEntries_perm es)

theorem pairwise_insertEntry {e : HeapEntry} {es : List HeapEntry}
    (hsorted : es.Pairwise HeapEntry.PriorityLE) :
    (insertEntry e es).Pairwise HeapEntry.PriorityLE := by
  induction es with
  | nil => simp [insertEntry]
  | cons u us ih =>
      rw [List.pairwise_cons] at hsorted
      simp only [insertEntry]
      by_cases heu : HeapEntry.PriorityLE e u
      · rw [if_pos heu, List.pairwise_cons]
        refine ⟨?_, (List.pairwise_cons.mpr hsorted)⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hxu | hx
        · subst x
          exact heu
        · exact HeapEntry.priorityLE_trans heu (hsorted.1 x hx)
      · rw [if_neg heu, List.pairwise_cons]
        refine ⟨?_, ih hsorted.2⟩
        intro x hx
        rw [mem_insertEntry] at hx
        rcases hx with hxe | hx
        · subst x
          rcases HeapEntry.priorityLE_total u e with hue | heu'
          · exact hue
          · exact False.elim (heu heu')
        · exact hsorted.1 x hx

theorem orderedEntries_pairwise (es : List HeapEntry) :
    (orderedEntries es).Pairwise HeapEntry.PriorityLE := by
  induction es with
  | nil => simp [orderedEntries]
  | cons e es ih => exact pairwise_insertEntry ih

theorem map_stamp_perm_of_perm {as bs : List HeapEntry} (h : as.Perm bs) :
    (as.map HeapEntry.stamp).Perm (bs.map HeapEntry.stamp) := h.map _

private theorem eq_of_same_stamp_mem_cons
    {a b : HeapEntry} {as : List HeapEntry}
    (hnodup : (HeapEntry.stamp a :: as.map HeapEntry.stamp).Nodup)
    (hb : b ∈ a :: as) (hstamp : b.stamp = a.stamp) : b = a := by
  simp only [List.mem_cons] at hb
  rcases hb with hba | hb
  · exact hba
  · have hmem : b.stamp ∈ as.map HeapEntry.stamp :=
      List.mem_map.mpr ⟨b, hb, rfl⟩
    have hnot := (List.nodup_cons.mp hnodup).1
    exact False.elim (hnot (hstamp ▸ hmem))

/-- A sorted permutation with distinct stamps is unique. -/
theorem eq_of_pairwise_priority_of_perm :
    ∀ {as bs : List HeapEntry},
      as.Pairwise HeapEntry.PriorityLE →
      bs.Pairwise HeapEntry.PriorityLE →
      (as.map HeapEntry.stamp).Nodup →
      as.Perm bs → as = bs
  | [], bs, _, _, _, hperm => by
      cases bs with
      | nil => rfl
      | cons b bs => simpa using hperm.length_eq
  | a :: as, [], _, _, _, hperm => by simpa using hperm.length_eq
  | a :: as, b :: bs, has, hbs, hnodup, hperm => by
      rw [List.pairwise_cons] at has hbs
      have hbIn : b ∈ a :: as :=
        (List.Perm.mem_iff hperm).mpr (by simp)
      have haIn : a ∈ b :: bs :=
        (List.Perm.mem_iff hperm).mp (by simp)
      have hab : HeapEntry.PriorityLE a b := by
        simp only [List.mem_cons] at hbIn
        rcases hbIn with hba | hbTail
        · subst b
          exact HeapEntry.priorityLE_refl _
        · exact has.1 b hbTail
      have hba : HeapEntry.PriorityLE b a := by
        simp only [List.mem_cons] at haIn
        rcases haIn with hab | haTail
        · subst a
          exact HeapEntry.priorityLE_refl _
        · exact hbs.1 a haTail
      have hcomponents := HeapEntry.priorityLE_antisymm_components hab hba
      have habEq : b = a :=
        eq_of_same_stamp_mem_cons hnodup hbIn hcomponents.2.symm
      subst b
      have htailPerm : as.Perm bs := hperm.cons_inv
      have htailNodup : (as.map HeapEntry.stamp).Nodup :=
        (List.nodup_cons.mp hnodup).2
      rw [eq_of_pairwise_priority_of_perm has.2 hbs.2 htailNodup htailPerm]

/-- Priority sorting is invariant under permutations with distinct stamps. -/
theorem orderedEntries_eq_of_perm {as bs : List HeapEntry}
    (hnodup : (as.map HeapEntry.stamp).Nodup) (hperm : as.Perm bs) :
    orderedEntries as = orderedEntries bs := by
  apply eq_of_pairwise_priority_of_perm
    (orderedEntries_pairwise as) (orderedEntries_pairwise bs)
  · exact (map_stamp_perm_of_perm (orderedEntries_perm as)).nodup_iff.mpr hnodup
  · exact (orderedEntries_perm as).trans (hperm.trans (orderedEntries_perm bs).symm)

theorem orderedEntries_stamps_nodup {es : List HeapEntry}
    (h : (es.map HeapEntry.stamp).Nodup) :
    ((orderedEntries es).map HeapEntry.stamp).Nodup :=
  (map_stamp_perm_of_perm (orderedEntries_perm es)).nodup_iff.mpr h

/-! ## Heap operation observations -/

def MinHeap.orderedView {params : HeapParams} (h : MinHeap params) :
    List HeapEntry := orderedEntries h.data

theorem MinHeap.orderedView_insert {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) (he : params.Bounded e)
    (hnodup : ((e :: h.data).map HeapEntry.stamp).Nodup) :
    (h.insert e he).orderedView = insertEntry e h.orderedView := by
  change orderedEntries (h.insert e he).data =
    orderedEntries (e :: h.data)
  exact orderedEntries_eq_of_perm
    ((map_stamp_perm_of_perm (MinHeap.insert_perm h e he)).nodup_iff.mpr hnodup)
    (MinHeap.insert_perm h e he)

theorem MinHeap.orderedView_extractMin {params : HeapParams}
    {h h' : MinHeap params} {e : HeapEntry}
    (hnodup : (h.data.map HeapEntry.stamp).Nodup)
    (hextract : h.extractMin = some (e, h')) :
    h.orderedView = e :: h'.orderedView := by
  have hspec := MinHeap.extractMin_spec hextract
  apply eq_of_pairwise_priority_of_perm
    (orderedEntries_pairwise h.data) ?_ ?_ ?_
  · rw [List.pairwise_cons]
    refine ⟨?_, orderedEntries_pairwise h'.data⟩
    intro u hu
    have hu' : u ∈ h'.data := (mem_orderedEntries u h'.data).mp hu
    have huOld : u ∈ h.data :=
      (List.Perm.mem_iff hspec.1).mp (List.mem_cons_of_mem e hu')
    exact hspec.2.2 u huOld
  · exact (map_stamp_perm_of_perm (orderedEntries_perm h.data)).nodup_iff.mpr hnodup
  · exact (orderedEntries_perm h.data).trans
      (hspec.1.symm.trans (List.Perm.cons e (orderedEntries_perm h'.data).symm))

/-! ## Erasing stable entries to the existing sorted forest -/

theorem map_tree_insertEntry_of_stamp_lt (e : HeapEntry) (es : List HeapEntry)
    (hstamps : ∀ u ∈ es, e.stamp < u.stamp) :
    (insertEntry e es).map HeapEntry.tree =
      insortTree e.tree (es.map HeapEntry.tree) := by
  induction es with
  | nil => rfl
  | cons u us ih =>
      simp only [insertEntry, insortTree, List.map_cons]
      have hstamp := hstamps u (by simp)
      by_cases hfreq : rootFreq e.tree ≤ rootFreq u.tree
      · have hpriority : HeapEntry.PriorityLE e u := by
          rcases Nat.lt_or_eq_of_le hfreq with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨heq, Nat.le_of_lt hstamp⟩
        simp [hpriority, hfreq]
      · have hpriority : ¬ HeapEntry.PriorityLE e u := by
          intro h
          rcases h with hlt | ⟨heq, _⟩
          · exact hfreq (Nat.le_of_lt hlt)
          · exact hfreq (Nat.le_of_eq heq)
        simp [hpriority, hfreq, ih (fun v hv => hstamps v (by simp [hv]))]

theorem orderedEntries_decorateFrom_trees (base : Nat) (ts : List HuffTree) :
    (orderedEntries (decorateFrom base ts)).map HeapEntry.tree = sortForest ts := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih =>
      simp only [decorateFrom, orderedEntries, sortForest]
      rw [map_tree_insertEntry_of_stamp_lt, ih]
      intro u hu
      have hu' : u ∈ decorateFrom (base + 1) ts :=
        (mem_orderedEntries u (decorateFrom (base + 1) ts)).mp hu
      have hge := decorateFrom_stamp_ge hu'
      change base < u.stamp
      omega

theorem orderedEntries_initial_trees (ts : List HuffTree) :
    (orderedEntries (initialEntries ts)).map HeapEntry.tree = sortForest ts := by
  exact orderedEntries_decorateFrom_trees ts.length ts

end CLRS.HuffmanV2
