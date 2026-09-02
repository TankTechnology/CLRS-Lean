import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Refinement

/-!
# Complete heap-based Huffman execution

This module joins the verified binary heap to the existing Huffman recursion.
The state invariant supplies the global frequency and stable-stamp facts needed
to construct every newly merged entry inside the fixed heap bounds.
-/

namespace CLRS.HuffmanV2

/-- Sum of root frequencies in an active heap forest. -/
def entryRootSum (entries : List HeapEntry) : Nat :=
  (entries.map (fun e => rootFreq e.tree)).sum

theorem entryRootSum_eq_of_perm {as bs : List HeapEntry} (h : as.Perm bs) :
    entryRootSum as = entryRootSum bs := by
  unfold entryRootSum
  exact (h.map (fun e => rootFreq e.tree)).sum_eq

@[simp] theorem entryRootSum_cons (e : HeapEntry) (es : List HeapEntry) :
    entryRootSum (e :: es) = rootFreq e.tree + entryRootSum es := by
  simp [entryRootSum]

theorem entryRootSum_decorateFrom (base : Nat) (ts : List HuffTree) :
    entryRootSum (decorateFrom base ts) = (ts.map rootFreq).sum := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih =>
      rw [decorateFrom, entryRootSum]
      simp only [List.map_cons, List.sum_cons]
      change rootFreq t + entryRootSum (decorateFrom (base + 1) ts) =
        rootFreq t + (ts.map rootFreq).sum
      rw [ih]

theorem tableFreq_le_tableTotal_of_mem {p : Nat × Nat}
    {xs : List (Nat × Nat)} (hp : p ∈ xs) : p.2 ≤ HeapParams.tableTotal xs := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with hpq | hp
      · subst p
        simp [HeapParams.tableTotal]
      · have htail := ih hp
        exact htail.trans (by simp [HeapParams.tableTotal])

/-- All initial decorated leaves lie inside the fixed execution envelope. -/
theorem initialEntries_bounded (xs : List (Nat × Nat)) :
    ∀ e ∈ initialEntries (leavesOfFreqs xs),
      (HeapParams.ofFreqs xs).Bounded e := by
  intro e he
  constructor
  · have htree : e.tree ∈ leavesOfFreqs xs := by
      have : e.tree ∈ (initialEntries (leavesOfFreqs xs)).map HeapEntry.tree :=
        List.mem_map.mpr ⟨e, he, rfl⟩
      simpa using this
    rcases List.mem_map.mp htree with ⟨p, hp, htree⟩
    rw [← htree]
    simpa [HeapParams.ofFreqs, rootFreq] using
      tableFreq_le_tableTotal_of_mem hp
  · have hstamp := decorateFrom_stamp_lt
      (base := (leavesOfFreqs xs).length) (ts := leavesOfFreqs xs) he
    simp [HeapParams.ofFreqs, HeapParams.base,
      leavesOfFreqs] at hstamp ⊢
    omega

/-- The initial forest's aggregate root frequency is the table total. -/
theorem initialEntries_rootSum (xs : List (Nat × Nat)) :
    entryRootSum (initialEntries (leavesOfFreqs xs)) =
      HeapParams.tableTotal xs := by
  rw [initialEntries, entryRootSum_decorateFrom]
  unfold HeapParams.tableTotal
  induction xs with
  | nil => rfl
  | cons p ps ih =>
      change p.2 + (List.map rootFreq (leavesOfFreqs ps)).sum =
        p.2 + (List.map Prod.snd ps).sum
      rw [ih]

/-- Execution invariant maintained across every two-extract/one-insert merge. -/
structure HeapHuffmanState (params : HeapParams) where
  heap : MinHeap params
  stampsNodup : (heap.data.map HeapEntry.stamp).Nodup
  stampFloor : ∀ e ∈ heap.data, heap.data.length - 1 ≤ e.stamp
  rootSum : entryRootSum heap.data = params.totalFreq
  size_le_input : heap.data.length ≤ params.inputSize

namespace HeapHuffmanState

/-- Initialize the complete verified state from a raw frequency table. -/
def ofFreqs (xs : List (Nat × Nat)) : HeapHuffmanState (HeapParams.ofFreqs xs) :=
  let entries := initialEntries (leavesOfFreqs xs)
  let hbounded := initialEntries_bounded xs
  let heap := MinHeap.build (HeapParams.ofFreqs xs) entries hbounded
  { heap := heap
    stampsNodup := by
      exact (map_stamp_perm_of_perm
        (MinHeap.build_perm (HeapParams.ofFreqs xs) entries hbounded)).nodup_iff.mpr
          (initialEntries_stamps_nodup (leavesOfFreqs xs))
    stampFloor := by
      intro e he
      have he' : e ∈ entries :=
        (List.Perm.mem_iff
          (MinHeap.build_perm (HeapParams.ofFreqs xs) entries hbounded)).mp he
      have hge := initialEntries_stamp_ge he'
      rw [MinHeap.build_size]
      simp [entries, leavesOfFreqs] at hge ⊢
      omega
    rootSum := by
      rw [entryRootSum_eq_of_perm
        (MinHeap.build_perm (HeapParams.ofFreqs xs) entries hbounded)]
      exact initialEntries_rootSum xs
    size_le_input := by
      rw [MinHeap.build_size]
      simp [entries, HeapParams.ofFreqs, leavesOfFreqs] }

@[simp] theorem ofFreqs_size (xs : List (Nat × Nat)) :
    (ofFreqs xs).heap.data.length = xs.length := by
  unfold ofFreqs
  rw [MinHeap.build_size]
  simp [leavesOfFreqs]

theorem ofFreqs_ordered_trees (xs : List (Nat × Nat)) :
    (ofFreqs xs).heap.orderedView.map HeapEntry.tree =
      sortForest (leavesOfFreqs xs) := by
  unfold ofFreqs MinHeap.orderedView
  let entries := initialEntries (leavesOfFreqs xs)
  let hbounded := initialEntries_bounded xs
  rw [orderedEntries_eq_of_perm
    ((map_stamp_perm_of_perm
      (MinHeap.build_perm (HeapParams.ofFreqs xs) entries hbounded)).nodup_iff.mpr
        (initialEntries_stamps_nodup (leavesOfFreqs xs)))
    (MinHeap.build_perm (HeapParams.ofFreqs xs) entries hbounded)]
  exact orderedEntries_initial_trees (leavesOfFreqs xs)

/-! ## One verified merge transition -/

/-- Two successful extractions followed by insertion of their joined tree. -/
def mergeState {params : HeapParams} (s : HeapHuffmanState params)
    {e₁ e₂ : HeapEntry} {h₁ h₂ : MinHeap params}
    (hextract₁ : s.heap.extractMin = some (e₁, h₁))
    (hextract₂ : h₁.extractMin = some (e₂, h₂)) :
    HeapHuffmanState params := by
  let oldSize := s.heap.data.length
  let newEntry := mergedEntry oldSize e₁ e₂
  have hspec₁ := MinHeap.extractMin_spec hextract₁
  have hspec₂ := MinHeap.extractMin_spec hextract₂
  have hsize₁ : h₁.data.length + 1 = oldSize := by simpa [oldSize] using hspec₁.2.1
  have hsize₂ : h₂.data.length + 1 = h₁.data.length := hspec₂.2.1
  have holdSize : oldSize = h₂.data.length + 2 := by omega
  have hsum₁ : rootFreq e₁.tree + entryRootSum h₁.data = params.totalFreq := by
    calc
      rootFreq e₁.tree + entryRootSum h₁.data = entryRootSum (e₁ :: h₁.data) := by simp
      _ = entryRootSum s.heap.data := entryRootSum_eq_of_perm hspec₁.1
      _ = params.totalFreq := s.rootSum
  have hsum₂ : rootFreq e₂.tree + entryRootSum h₂.data = entryRootSum h₁.data := by
    calc
      rootFreq e₂.tree + entryRootSum h₂.data = entryRootSum (e₂ :: h₂.data) := by simp
      _ = entryRootSum h₁.data := entryRootSum_eq_of_perm hspec₂.1
  have hboundedNew : params.Bounded newEntry := by
    constructor
    · change rootFreq e₁.tree + rootFreq e₂.tree ≤ params.totalFreq
      omega
    · change oldSize - 2 < params.base
      have hsizeBound : oldSize ≤ params.inputSize := by
        simpa [oldSize] using s.size_le_input
      simp only [HeapParams.base]
      omega
  let heap' := h₂.insert newEntry hboundedNew
  have hinsertPerm : heap'.data.Perm (newEntry :: h₂.data) :=
    MinHeap.insert_perm h₂ newEntry hboundedNew
  have hnodup₁ : ((e₁ :: h₁.data).map HeapEntry.stamp).Nodup :=
    (map_stamp_perm_of_perm hspec₁.1).nodup_iff.mpr s.stampsNodup
  have hnodupH₁ : (h₁.data.map HeapEntry.stamp).Nodup :=
    (List.nodup_cons.mp hnodup₁).2
  have hnodup₂ : ((e₂ :: h₂.data).map HeapEntry.stamp).Nodup :=
    (map_stamp_perm_of_perm hspec₂.1).nodup_iff.mpr hnodupH₁
  have hnodupH₂ : (h₂.data.map HeapEntry.stamp).Nodup :=
    (List.nodup_cons.mp hnodup₂).2
  have hnewFresh : ∀ u ∈ h₂.data, newEntry.stamp < u.stamp := by
    intro u hu
    have huH₁ : u ∈ h₁.data :=
      (List.Perm.mem_iff hspec₂.1).mp (List.mem_cons_of_mem e₂ hu)
    have huOld : u ∈ s.heap.data :=
      (List.Perm.mem_iff hspec₁.1).mp (List.mem_cons_of_mem e₁ huH₁)
    have hfloor := s.stampFloor u huOld
    change oldSize - 2 < u.stamp
    change oldSize - 1 ≤ u.stamp at hfloor
    omega
  refine
    { heap := heap'
      stampsNodup := ?_
      stampFloor := ?_
      rootSum := ?_
      size_le_input := ?_ }
  · apply (map_stamp_perm_of_perm hinsertPerm).nodup_iff.mpr
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnodupH₂⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨u, hu, hstamp⟩
    have hfresh := hnewFresh u hu
    omega
  · intro u hu
    have hu' : u ∈ newEntry :: h₂.data :=
      (List.Perm.mem_iff hinsertPerm).mp hu
    simp only [List.mem_cons] at hu'
    rcases hu' with hueq | huOld
    · subst u
      rw [MinHeap.insert_size]
      change h₂.data.length + 1 - 1 ≤ oldSize - 2
      omega
    · have huH₁ : u ∈ h₁.data :=
        (List.Perm.mem_iff hspec₂.1).mp (List.mem_cons_of_mem e₂ huOld)
      have huSource : u ∈ s.heap.data :=
        (List.Perm.mem_iff hspec₁.1).mp (List.mem_cons_of_mem e₁ huH₁)
      have hfloor := s.stampFloor u huSource
      rw [MinHeap.insert_size]
      omega
  · calc
      entryRootSum heap'.data = entryRootSum (newEntry :: h₂.data) :=
        entryRootSum_eq_of_perm hinsertPerm
      _ = rootFreq e₁.tree + rootFreq e₂.tree + entryRootSum h₂.data := by
        simp [newEntry, mergedEntry, unite, rootFreq]
      _ = params.totalFreq := by omega
  · rw [MinHeap.insert_size]
    have holdBound : oldSize ≤ params.inputSize := by
      simpa [oldSize] using s.size_le_input
    omega

theorem stampsNodup_after_extract {params : HeapParams}
    {h h' : MinHeap params} {e : HeapEntry}
    (hnodup : (h.data.map HeapEntry.stamp).Nodup)
    (hextract : h.extractMin = some (e, h')) :
    (h'.data.map HeapEntry.stamp).Nodup := by
  have hspec := MinHeap.extractMin_spec hextract
  have hcons : ((e :: h'.data).map HeapEntry.stamp).Nodup :=
    (map_stamp_perm_of_perm hspec.1).nodup_iff.mpr hnodup
  exact (List.nodup_cons.mp hcons).2

@[simp] theorem mergeState_size {params : HeapParams}
    (s : HeapHuffmanState params) {e₁ e₂ : HeapEntry} {h₁ h₂ : MinHeap params}
    (hextract₁ : s.heap.extractMin = some (e₁, h₁))
    (hextract₂ : h₁.extractMin = some (e₂, h₂)) :
    (mergeState s hextract₁ hextract₂).heap.data.length + 1 =
      s.heap.data.length := by
  have hspec₁ := MinHeap.extractMin_spec hextract₁
  have hspec₂ := MinHeap.extractMin_spec hextract₂
  unfold mergeState
  simp only [MinHeap.insert_size]
  omega

/-- The merge transition implements exactly the sorted-list reinsertion step. -/
theorem mergeState_ordered_trees {params : HeapParams}
    (s : HeapHuffmanState params) {e₁ e₂ : HeapEntry} {h₁ h₂ : MinHeap params}
    (hextract₁ : s.heap.extractMin = some (e₁, h₁))
    (hextract₂ : h₁.extractMin = some (e₂, h₂)) :
    (mergeState s hextract₁ hextract₂).heap.orderedView.map HeapEntry.tree =
      insortTree (unite e₁.tree e₂.tree) (h₂.orderedView.map HeapEntry.tree) := by
  let oldSize := s.heap.data.length
  let newEntry := mergedEntry oldSize e₁ e₂
  have hnodup₁ := stampsNodup_after_extract s.stampsNodup hextract₁
  have hnodup₂ := stampsNodup_after_extract hnodup₁ hextract₂
  have hspec₁ := MinHeap.extractMin_spec hextract₁
  have hspec₂ := MinHeap.extractMin_spec hextract₂
  have hsize₁ : h₁.data.length + 1 = oldSize := by simpa [oldSize] using hspec₁.2.1
  have hsize₂ : h₂.data.length + 1 = h₁.data.length := hspec₂.2.1
  have hboundedNew : params.Bounded newEntry := by
    constructor
    · change rootFreq e₁.tree + rootFreq e₂.tree ≤ params.totalFreq
      have hsum₁ : rootFreq e₁.tree + entryRootSum h₁.data = params.totalFreq := by
        calc
          _ = entryRootSum (e₁ :: h₁.data) := by simp
          _ = entryRootSum s.heap.data := entryRootSum_eq_of_perm hspec₁.1
          _ = params.totalFreq := s.rootSum
      have hsum₂ : rootFreq e₂.tree + entryRootSum h₂.data = entryRootSum h₁.data := by
        calc
          _ = entryRootSum (e₂ :: h₂.data) := by simp
          _ = entryRootSum h₁.data := entryRootSum_eq_of_perm hspec₂.1
      omega
    · change oldSize - 2 < params.base
      have holdBound : oldSize ≤ params.inputSize := by
        simpa [oldSize] using s.size_le_input
      simp only [HeapParams.base]
      omega
  have hconsNodup : ((newEntry :: h₂.data).map HeapEntry.stamp).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnodup₂⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨u, hu, hstamp⟩
    have huH₁ : u ∈ h₁.data :=
      (List.Perm.mem_iff hspec₂.1).mp (List.mem_cons_of_mem e₂ hu)
    have huOld : u ∈ s.heap.data :=
      (List.Perm.mem_iff hspec₁.1).mp (List.mem_cons_of_mem e₁ huH₁)
    have hfloor := s.stampFloor u huOld
    have hlt : newEntry.stamp < u.stamp := by
      change oldSize - 2 < u.stamp
      change oldSize - 1 ≤ u.stamp at hfloor
      omega
    omega
  have hviewInsert := MinHeap.orderedView_insert h₂ newEntry hboundedNew hconsNodup
  have hstampLt : ∀ u ∈ h₂.orderedView, newEntry.stamp < u.stamp := by
    intro u hu
    have huData := (mem_orderedEntries u h₂.data).mp hu
    have huH₁ : u ∈ h₁.data :=
      (List.Perm.mem_iff hspec₂.1).mp (List.mem_cons_of_mem e₂ huData)
    have huOld : u ∈ s.heap.data :=
      (List.Perm.mem_iff hspec₁.1).mp (List.mem_cons_of_mem e₁ huH₁)
    have hfloor := s.stampFloor u huOld
    change oldSize - 2 < u.stamp
    change oldSize - 1 ≤ u.stamp at hfloor
    omega
  unfold mergeState
  rw [hviewInsert]
  simpa [newEntry, mergedEntry] using
    map_tree_insertEntry_of_stamp_lt newEntry h₂.orderedView hstampLt

end HeapHuffmanState

/-! ## Total heap execution -/

/-- Execute at most one merge per unit of fuel. -/
def heapHuffmanLoop {params : HeapParams} :
    Nat → HeapHuffmanState params → HuffTree
  | 0, _ => HuffTree.htLeaf 0 0
  | fuel + 1, s =>
      match hextract₁ : s.heap.extractMin with
      | none => HuffTree.htLeaf 0 0
      | some (e₁, h₁) =>
          match hextract₂ : h₁.extractMin with
          | none => e₁.tree
          | some (_e₂, _h₂) =>
              heapHuffmanLoop fuel
                (HeapHuffmanState.mergeState s hextract₁ hextract₂)

/-- Textbook Huffman using the verified binary min-heap. -/
def heapHuffmanOfFreqs (xs : List (Nat × Nat)) : HuffTree :=
  heapHuffmanLoop xs.length (HeapHuffmanState.ofFreqs xs)

theorem MinHeap.orderedView_eq_nil_iff {params : HeapParams}
    (h : MinHeap params) : h.orderedView = [] ↔ h.data = [] := by
  constructor
  · intro hview
    change h.ranked.data = []
    apply List.eq_nil_of_length_eq_zero
    rw [← orderedEntries_length h.ranked.data]
    simpa [MinHeap.orderedView] using congrArg List.length hview
  · intro hdata
    change h.ranked.data = [] at hdata
    change orderedEntries h.ranked.data = []
    simp [hdata, orderedEntries]

/-- The complete heap loop refines the existing sorted-list recursion exactly. -/
theorem heapHuffmanLoop_eq_huffman {params : HeapParams}
    (s : HeapHuffmanState params) :
    heapHuffmanLoop s.heap.data.length s =
      huffman (s.heap.orderedView.map HeapEntry.tree) := by
  induction hlen : s.heap.data.length using Nat.strong_induction_on generalizing s with
  | h n ih =>
      cases n with
      | zero =>
          have hdata : s.heap.data = [] := List.eq_nil_of_length_eq_zero hlen
          have hview : s.heap.orderedView = [] :=
            (MinHeap.orderedView_eq_nil_iff s.heap).2 hdata
          simp [heapHuffmanLoop, hview, huffman]
      | succ n =>
          simp only [heapHuffmanLoop]
          split
          next hextract₁ =>
            have hdata : s.heap.data = [] :=
              (MinHeap.extractMin_eq_none_iff s.heap).1 hextract₁
            change s.heap.ranked.data = [] at hdata
            change s.heap.ranked.data.length = n + 1 at hlen
            simp [hdata] at hlen
          next e₁ h₁ hextract₁ =>
            have hview₁ := MinHeap.orderedView_extractMin
              s.stampsNodup hextract₁
            have hnodup₁ := HeapHuffmanState.stampsNodup_after_extract
              s.stampsNodup hextract₁
            split
            next hextract₂ =>
              have hdata₁ : h₁.data = [] :=
                (MinHeap.extractMin_eq_none_iff h₁).1 hextract₂
              have hviewEmpty : h₁.orderedView = [] :=
                (MinHeap.orderedView_eq_nil_iff h₁).2 hdata₁
              have htrees :
                  s.heap.orderedView.map HeapEntry.tree = [e₁.tree] := by
                rw [hview₁, hviewEmpty]
                rfl
              rw [htrees]
              simp [huffman]
            next e₂ h₂ hextract₂ =>
              let next := HeapHuffmanState.mergeState s hextract₁ hextract₂
              have hnextSize : next.heap.ranked.data.length = n := by
                have hdrop := HeapHuffmanState.mergeState_size
                  s hextract₁ hextract₂
                change next.heap.ranked.data.length + 1 =
                  s.heap.ranked.data.length at hdrop
                change s.heap.ranked.data.length = n + 1 at hlen
                omega
              have hnextLt : next.heap.ranked.data.length < n + 1 := by omega
              have hrec := ih next.heap.ranked.data.length hnextLt next rfl
              have hrec' :
                  heapHuffmanLoop n next =
                    huffman (next.heap.orderedView.map HeapEntry.tree) := by
                rw [hnextSize] at hrec
                exact hrec
              have hview₂ := MinHeap.orderedView_extractMin hnodup₁ hextract₂
              have holdTrees :
                  s.heap.orderedView.map HeapEntry.tree =
                    e₁.tree :: e₂.tree :: h₂.orderedView.map HeapEntry.tree := by
                rw [hview₁, hview₂]
                rfl
              have hnextTrees := HeapHuffmanState.mergeState_ordered_trees
                s hextract₁ hextract₂
              calc
                heapHuffmanLoop n next =
                    huffman (next.heap.orderedView.map HeapEntry.tree) := hrec'
                _ = huffman
                    (insortTree (unite e₁.tree e₂.tree)
                      (h₂.orderedView.map HeapEntry.tree)) := by rw [hnextTrees]
                _ = huffman (s.heap.orderedView.map HeapEntry.tree) := by
                  rw [holdTrees]
                  symm
                  simp [huffman]

/-- Exact erasure/refinement theorem for the public frequency-table program. -/
theorem heapHuffmanOfFreqs_eq (xs : List (Nat × Nat)) :
    heapHuffmanOfFreqs xs = huffmanOfFreqs xs := by
  let s := HeapHuffmanState.ofFreqs xs
  calc
    heapHuffmanOfFreqs xs = heapHuffmanLoop s.heap.data.length s := by
      have hs := HeapHuffmanState.ofFreqs_size xs
      change s.heap.ranked.data.length = xs.length at hs
      unfold heapHuffmanOfFreqs
      change heapHuffmanLoop xs.length s =
        heapHuffmanLoop s.heap.ranked.data.length s
      rw [hs]
    _ = huffman (s.heap.orderedView.map HeapEntry.tree) :=
      heapHuffmanLoop_eq_huffman s
    _ = huffman (sortForest (leavesOfFreqs xs)) := by
      rw [HeapHuffmanState.ofFreqs_ordered_trees]
    _ = huffmanOfFreqs xs := rfl

/-- Frequency semantics and optimality transported to the genuine heap run. -/
theorem heapHuffmanOfFreqs_semantic_correct (xs : List (Nat × Nat))
    (h_nodup : (xs.map Prod.fst).Nodup)
    (h_pos : ∀ p ∈ xs, p.2 > 0)
    (h_nonempty : xs ≠ []) :
    (∀ symbol, freqOf symbol (heapHuffmanOfFreqs xs) = tableFreq xs symbol) ∧
      optimum (heapHuffmanOfFreqs xs) := by
  rw [heapHuffmanOfFreqs_eq]
  exact huffmanOfFreqs_correct xs h_nodup h_pos h_nonempty

end CLRS.HuffmanV2
