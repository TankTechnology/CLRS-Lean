import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.ArrayHeap
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Ranking

/-!
# Verified structural operations for the Huffman binary heap

The central reuse theorem says that mapping entries to ranks commutes with
every heap controller.  Chapter 6 can therefore discharge the indexed heap
invariant while this module separately proves preservation of the actual tree
multiset.
-/

namespace CLRS.HuffmanV2

section Swap

variable {α β : Type}

/-- Auxiliary permutation lemma for a generic head/cell exchange. -/
theorem cons_set_perm_of_get?_generic {xs : List α} {j : Nat} {x y : α}
    (h : xs[j]? = some y) : (y :: xs.set j x).Perm (x :: xs) := by
  induction xs generalizing j with
  | nil => simp at h
  | cons z zs ih =>
      cases j with
      | zero =>
          simp at h
          subst y
          simp [List.set]
          exact List.Perm.swap x z zs
      | succ j =>
          simp at h
          have ih' := ih h
          simp [List.set]
          exact ((List.Perm.swap y z (zs.set j x)).symm.trans
            (List.Perm.cons z ih')).trans (List.Perm.swap z x zs).symm

@[simp] theorem swapEntries_length (a : List α) (i j : Nat) :
    (swapEntries a i j).length = a.length := by
  unfold swapEntries
  cases a[i]? <;> cases a[j]? <;> simp

theorem swapEntries_perm (a : List α) (i j : Nat) :
    (swapEntries a i j).Perm a := by
  induction a generalizing i j with
  | nil => simp [swapEntries]
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [swapEntries]
          | succ j =>
              unfold swapEntries
              simp
              cases h : xs[j]? with
              | none => simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get?_generic (xs := xs) (j := j) (x := x) h
      | succ i =>
          cases j with
          | zero =>
              unfold swapEntries
              simp
              cases h : xs[i]? with
              | none => simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get?_generic (xs := xs) (j := i) (x := x) h
          | succ j =>
              cases hi : xs[i]? with
              | none => simp [swapEntries, hi]
              | some ai =>
                  cases hj : xs[j]? with
                  | none => simp [swapEntries, hi, hj]
                  | some aj =>
                      simpa [swapEntries, hi, hj, List.set] using ih i j

/-- Mapping a generic swap is exactly Chapter 6's natural-key swap. -/
theorem map_swapEntries (f : α → Nat) (a : List α) (i j : Nat) :
    (swapEntries a i j).map f =
      CLRS.Chapter06.swapAt (a.map f) i j := by
  unfold swapEntries CLRS.Chapter06.swapAt
  simp only [List.getElem?_map]
  cases hi : a[i]? <;> cases hj : a[j]? <;>
    simp [List.map_set]

/-- The right destination of an in-bounds generic swap contains the old left value. -/
theorem getElem?_swapEntries_right {a : List α} {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) :
    (swapEntries a i j)[j]? = a[i]? := by
  by_cases hij : i = j
  · subst j
    simp [swapEntries, List.getElem?_eq_getElem hi]
  · unfold swapEntries
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp
    rw [List.getElem?_set_self']
    have hjset : j < (a.set i a[j]).length := by simpa using hj
    simp [List.getElem?_eq_getElem hjset]

end Swap

/-! ## Controller erasure and structural laws -/

theorem bubbleUpFuel_map_rank (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleUpFuel rank fuel a heapSize i).map rank =
      CLRS.Chapter06.arrayHeapIncreaseKeyBubbleUpFuel fuel (a.map rank)
        heapSize i := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleUpFuel,
        CLRS.Chapter06.arrayHeapIncreaseKeyBubbleUpFuel]
      split_ifs
      · rw [ih, map_swapEntries]
      · rfl
      · rfl

@[simp] theorem bubbleUpFuel_length (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleUpFuel rank fuel a heapSize i).length = a.length := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleUpFuel]
      split_ifs
      · rw [ih, swapEntries_length]
      · rfl
      · rfl

theorem bubbleUpFuel_perm (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleUpFuel rank fuel a heapSize i).Perm a := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleUpFuel]
      split_ifs
      · exact (ih _ _).trans (swapEntries_perm _ _ _)
      · rfl
      · rfl

theorem bubbleDownFuel_map_rank (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleDownFuel rank fuel a heapSize i).map rank =
      CLRS.Chapter06.maxHeapifyFuel fuel (a.map rank) heapSize i := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleDownFuel, CLRS.Chapter06.maxHeapifyFuel]
      split
      · rfl
      · rw [ih, map_swapEntries]

@[simp] theorem bubbleDownFuel_length (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleDownFuel rank fuel a heapSize i).length = a.length := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleDownFuel]
      split
      · rfl
      · rw [ih, swapEntries_length]

theorem bubbleDownFuel_perm (rank : HeapEntry → Nat) (fuel : Nat)
    (a : List HeapEntry) (heapSize i : Nat) :
    (bubbleDownFuel rank fuel a heapSize i).Perm a := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [bubbleDownFuel]
      split
      · rfl
      · exact (ih _ _).trans (swapEntries_perm _ _ _)

@[simp] theorem heapInsertRaw_length (rank : HeapEntry → Nat)
    (a : List HeapEntry) (e : HeapEntry) :
    (heapInsertRaw rank a e).length = a.length + 1 := by
  simp [heapInsertRaw]

theorem heapInsertRaw_perm (rank : HeapEntry → Nat)
    (a : List HeapEntry) (e : HeapEntry) :
    (heapInsertRaw rank a e).Perm (e :: a) := by
  exact (bubbleUpFuel_perm rank a.length (a ++ [e]) (a.length + 1) a.length).trans
    (by
      convert (List.perm_append_comm (l₁ := a) (l₂ := [e])) using 1
      all_goals simp)

theorem heapInsertRaw_map_rank (rank : HeapEntry → Nat)
    (a : List HeapEntry) (e : HeapEntry) :
    (heapInsertRaw rank a e).map rank =
      CLRS.Chapter06.arrayHeapInsert (a.map rank) (rank e) := by
  simp only [heapInsertRaw, CLRS.Chapter06.arrayHeapInsert]
  rw [bubbleUpFuel_map_rank]
  simp

/-! ## Heap invariant preservation -/

theorem heapInsertRaw_isRankHeap {rank : HeapEntry → Nat}
    {a : List HeapEntry} (e : HeapEntry) (hheap : IsRankHeap rank a) :
    IsRankHeap rank (heapInsertRaw rank a e) := by
  unfold IsRankHeap at hheap ⊢
  rw [heapInsertRaw_map_rank]
  have hheap' :
      CLRS.Chapter06.ArrayMaxHeap (a.map rank) (a.map rank).length := by
    simpa using hheap
  simpa [heapInsertRaw_length] using
    CLRS.Chapter06.arrayHeapInsert_isMaxHeap (rank e) hheap'

/-- Taking the active prefix preserves an except-at-one-node heap predicate. -/
theorem arrayMaxHeapExcept_take {a : List Nat} {heapSize bad : Nat}
    (hheap : CLRS.Chapter06.ArrayMaxHeapExcept a heapSize bad) :
    CLRS.Chapter06.ArrayMaxHeapExcept (a.take heapSize) heapSize bad := by
  have hlen : (a.take heapSize).length = heapSize :=
    List.length_take_of_le hheap.heapSize_le_length
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hi hne hl
    simpa only [List.getElem_take] using hheap.left_le hi hne hl
  · intro i hi hne hr
    simpa only [List.getElem_take] using hheap.right_le hi hne hr

/-- One raw extraction removes exactly the returned root entry. -/
theorem heapExtractMaxRaw_perm {rank : HeapEntry → Nat}
    {a rest : List HeapEntry} {root : HeapEntry}
    (h : heapExtractMaxRaw rank a = some (root, rest)) :
    (root :: rest).Perm a := by
  cases a with
  | nil => simp [heapExtractMaxRaw] at h
  | cons x xs =>
      simp only [heapExtractMaxRaw, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      let moved := swapEntries (x :: xs) 0 xs.length
      let active := moved.take xs.length
      have hlenMoved : moved.length = xs.length + 1 := by
        simp [moved]
      have hlast : xs.length < moved.length := by omega
      have hlastValue : moved[xs.length]'hlast = x := by
        have hread :=
          getElem?_swapEntries_right (a := x :: xs) (i := 0) (j := xs.length)
            (by simp) (by simp)
        rw [List.getElem?_eq_getElem hlast] at hread
        simpa [moved] using hread
      have hsplit : active ++ [x] = moved := by
        calc
          active ++ [x] = moved.take xs.length ++ [moved[xs.length]] := by
            simp [active, hlastValue]
          _ = moved.take (xs.length + 1) := by simp
          _ = moved := by simp [hlenMoved]
      have hactive : (x :: active).Perm (x :: xs) := by
        have hrotate : (x :: active).Perm (active ++ [x]) := by
          simpa using (List.perm_append_comm (l₁ := [x]) (l₂ := active))
        exact hrotate.trans (by rw [hsplit]; exact swapEntries_perm _ _ _)
      exact (List.Perm.cons x
        (bubbleDownFuel_perm rank xs.length active xs.length 0)).trans hactive

theorem heapExtractMaxRaw_length {rank : HeapEntry → Nat}
    {a rest : List HeapEntry} {root : HeapEntry}
    (h : heapExtractMaxRaw rank a = some (root, rest)) :
    rest.length + 1 = a.length := by
  have hp := heapExtractMaxRaw_perm h
  simpa using hp.length_eq

theorem heapExtractMaxRaw_eq_none_iff (rank : HeapEntry → Nat)
    (a : List HeapEntry) : heapExtractMaxRaw rank a = none ↔ a = [] := by
  cases a <;> simp [heapExtractMaxRaw]

/-- Extraction from a ranked heap returns a ranked heap of one smaller size. -/
theorem heapExtractMaxRaw_isRankHeap {rank : HeapEntry → Nat}
    {a rest : List HeapEntry} {root : HeapEntry}
    (hheap : IsRankHeap rank a)
    (h : heapExtractMaxRaw rank a = some (root, rest)) :
    IsRankHeap rank rest := by
  cases a with
  | nil => simp [heapExtractMaxRaw] at h
  | cons x xs =>
      simp only [heapExtractMaxRaw, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      let scores := (x :: xs).map rank
      let moved := CLRS.Chapter06.swapAt scores 0 xs.length
      let active := moved.take xs.length
      have hheapScores : CLRS.Chapter06.ArrayMaxHeap scores (xs.length + 1) := by
        simpa [IsRankHeap, scores] using hheap
      have hexceptFull :
          CLRS.Chapter06.ArrayMaxHeapExcept moved xs.length 0 := by
        exact CLRS.Chapter06.ArrayMaxHeapExcept.of_swap_root_last hheapScores
      have hexceptActive :
          CLRS.Chapter06.ArrayMaxHeapExcept active xs.length 0 :=
        arrayMaxHeapExcept_take hexceptFull
      have hvalidNat :
          CLRS.Chapter06.ArrayMaxHeap
            (CLRS.Chapter06.maxHeapifyFuel xs.length active xs.length 0)
            xs.length := by
        by_cases hpos : 0 < xs.length
        · exact CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap
            hexceptActive hpos (Nat.le_refl _)
        · have hzero : xs.length = 0 := by omega
          rw [hzero]
          exact ⟨by simp [active], by intro i hi; omega, by intro i hi; omega⟩
      unfold IsRankHeap
      rw [bubbleDownFuel_map_rank]
      have hmapActive :
          ((swapEntries (x :: xs) 0 xs.length).take xs.length).map rank = active := by
        simp [active, moved, scores, map_swapEntries]
      rw [hmapActive]
      simpa using hvalidNat

/-- The extracted root has maximum rank among all entries in the old heap. -/
theorem heapExtractMaxRaw_rank_max {rank : HeapEntry → Nat}
    {a rest : List HeapEntry} {root : HeapEntry}
    (hheap : IsRankHeap rank a)
    (h : heapExtractMaxRaw rank a = some (root, rest)) :
    ∀ e ∈ a, rank e ≤ rank root := by
  intro e he
  cases a with
  | nil => simp at he
  | cons x xs =>
      simp only [heapExtractMaxRaw, Option.some.injEq, Prod.mk.injEq] at h
      have hx : root = x := h.1.symm
      subst root
      have heMap : rank e ∈ (x :: xs).map rank := List.mem_map.mpr ⟨e, he, rfl⟩
      rcases List.get_of_mem heMap with ⟨i, hi⟩
      have hheap' :
          CLRS.Chapter06.ArrayMaxHeap ((x :: xs).map rank)
            ((x :: xs).map rank).length := by
        simpa [IsRankHeap] using hheap
      have hbound := hheap'.getElem_le_root i.isLt
      change ((x :: xs).map rank).get i ≤ rank x at hbound
      rw [hi] at hbound
      exact hbound

/-! ## Packaged ranked heap -/

/-- A concrete binary heap bundled with its verified ranked-array invariant. -/
structure RankedHeap (rank : HeapEntry → Nat) where
  data : List HeapEntry
  valid : IsRankHeap rank data

namespace RankedHeap

def empty (rank : HeapEntry → Nat) : RankedHeap rank :=
  ⟨[], by
    unfold IsRankHeap
    refine ⟨by simp, ?_, ?_⟩
    · intro i hi hl
      simp at hi
    · intro i hi hr
      simp at hi⟩

def insert {rank : HeapEntry → Nat} (h : RankedHeap rank)
    (e : HeapEntry) : RankedHeap rank :=
  ⟨heapInsertRaw rank h.data e, heapInsertRaw_isRankHeap e h.valid⟩

def extractMax {rank : HeapEntry → Nat} (h : RankedHeap rank) :
    Option (HeapEntry × RankedHeap rank) :=
  match hextract : heapExtractMaxRaw rank h.data with
  | none => none
  | some (e, data) => some (e, ⟨data, heapExtractMaxRaw_isRankHeap h.valid hextract⟩)

/-- Erasing the invariant package recovers the raw extraction exactly. -/
theorem extractMax_erases {rank : HeapEntry → Nat} (h : RankedHeap rank) :
    h.extractMax.map (fun p => (p.1, p.2.data)) =
      heapExtractMaxRaw rank h.data := by
  unfold extractMax
  split <;> simp_all

theorem extractMax_eq_none_iff {rank : HeapEntry → Nat} (h : RankedHeap rank) :
    h.extractMax = none ↔ h.data = [] := by
  constructor
  · intro hnone
    have hmapped :
        h.extractMax.map (fun p => (p.1, p.2.data)) = none := by simp [hnone]
    rw [extractMax_erases] at hmapped
    exact (heapExtractMaxRaw_eq_none_iff rank h.data).mp hmapped
  · intro hempty
    have hraw : heapExtractMaxRaw rank h.data = none :=
      (heapExtractMaxRaw_eq_none_iff rank h.data).mpr hempty
    cases hextract : h.extractMax with
    | none => rfl
    | some result =>
        have hmapped :
            h.extractMax.map (fun p => (p.1, p.2.data)) = none := by
          rw [extractMax_erases, hraw]
        simp [hextract] at hmapped

@[simp] theorem empty_data (rank : HeapEntry → Nat) :
    (empty rank).data = [] := rfl

@[simp] theorem insert_data {rank : HeapEntry → Nat} (h : RankedHeap rank)
    (e : HeapEntry) : (h.insert e).data = heapInsertRaw rank h.data e := rfl

@[simp] theorem insert_size {rank : HeapEntry → Nat} (h : RankedHeap rank)
    (e : HeapEntry) : (h.insert e).data.length = h.data.length + 1 := by
  simp [insert]

theorem insert_perm {rank : HeapEntry → Nat} (h : RankedHeap rank)
    (e : HeapEntry) : (h.insert e).data.Perm (e :: h.data) :=
  heapInsertRaw_perm rank h.data e

theorem extractMax_spec {rank : HeapEntry → Nat} {h : RankedHeap rank}
    {e : HeapEntry} {h' : RankedHeap rank}
    (hextract : h.extractMax = some (e, h')) :
    (e :: h'.data).Perm h.data ∧
      h'.data.length + 1 = h.data.length ∧
      ∀ u ∈ h.data, rank u ≤ rank e := by
  have hmapped := congrArg (Option.map (fun p => (p.1, p.2.data))) hextract
  rw [extractMax_erases] at hmapped
  have hraw : heapExtractMaxRaw rank h.data = some (e, h'.data) := by
    simpa using hmapped
  exact ⟨heapExtractMaxRaw_perm hraw, heapExtractMaxRaw_length hraw,
    heapExtractMaxRaw_rank_max h.valid hraw⟩

end RankedHeap

/-! ## Bounded binary min-heap for Huffman priorities -/

/-- Parent/child invariant stated directly in Huffman's lexicographic order. -/
def IsMinHeap (a : List HeapEntry) : Prop :=
  (∀ {i : Nat}, (hi : i < a.length) →
      (hl : CLRS.Chapter06.left i < a.length) →
      HeapEntry.PriorityLE a[i] a[CLRS.Chapter06.left i]) ∧
    (∀ {i : Nat}, (hi : i < a.length) →
      (hr : CLRS.Chapter06.right i < a.length) →
      HeapEntry.PriorityLE a[i] a[CLRS.Chapter06.right i])

/-- A ranked array together with the bounds that make its rank order faithful. -/
structure MinHeap (params : HeapParams) where
  ranked : RankedHeap params.rank
  bounded : ∀ e ∈ ranked.data, params.Bounded e

namespace MinHeap

def data {params : HeapParams} (h : MinHeap params) : List HeapEntry :=
  h.ranked.data

@[simp] theorem data_eq {params : HeapParams} (h : MinHeap params) :
    h.data = h.ranked.data := rfl

/-- The inherited numeric max-heap is genuinely a binary min-heap on entries. -/
theorem valid {params : HeapParams} (h : MinHeap params) : IsMinHeap h.data := by
  change IsMinHeap h.ranked.data
  constructor
  · intro i hi hl
    have hrank := h.ranked.valid.left_le hi hl
    apply (HeapParams.priorityLE_iff_rank_ge
      (h.bounded h.ranked.data[i] (List.getElem_mem hi))
      (h.bounded h.ranked.data[CLRS.Chapter06.left i] (List.getElem_mem hl))).2
    simpa only [List.getElem_map] using hrank
  · intro i hi hr
    have hrank := h.ranked.valid.right_le hi hr
    apply (HeapParams.priorityLE_iff_rank_ge
      (h.bounded h.ranked.data[i] (List.getElem_mem hi))
      (h.bounded h.ranked.data[CLRS.Chapter06.right i] (List.getElem_mem hr))).2
    simpa only [List.getElem_map] using hrank

def empty (params : HeapParams) : MinHeap params :=
  ⟨RankedHeap.empty params.rank, by simp⟩

def insert {params : HeapParams} (h : MinHeap params) (e : HeapEntry)
    (he : params.Bounded e) : MinHeap params :=
  ⟨h.ranked.insert e, by
    intro u hu
    have hu' : u ∈ e :: h.ranked.data :=
      (List.Perm.mem_iff (RankedHeap.insert_perm h.ranked e)).mp hu
    simp only [List.mem_cons] at hu'
    rcases hu' with hue | hu'
    · subst u
      exact he
    · exact h.bounded u hu'⟩

/-- Initialize a verified heap by repeated executable insertion. -/
def build (params : HeapParams) :
    (entries : List HeapEntry) →
      (∀ e ∈ entries, params.Bounded e) → MinHeap params
  | [], _ => empty params
  | e :: entries, hbounded =>
      let tailHeap := build params entries (fun u hu => hbounded u (by simp [hu]))
      tailHeap.insert e (hbounded e (by simp))

def extractMin {params : HeapParams} (h : MinHeap params) :
    Option (HeapEntry × MinHeap params) :=
  match hextract : h.ranked.extractMax with
  | none => none
  | some (e, ranked') =>
      some (e, ⟨ranked', by
        intro u hu
        have hspec := RankedHeap.extractMax_spec hextract
        have hu' : u ∈ e :: ranked'.data := by simp [hu]
        exact h.bounded u ((List.Perm.mem_iff hspec.1).mp hu')⟩)

@[simp] theorem empty_data (params : HeapParams) :
    (empty params).data = [] := rfl

@[simp] theorem insert_data {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) (he : params.Bounded e) :
    (h.insert e he).data = (h.ranked.insert e).data := rfl

theorem insert_perm {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) (he : params.Bounded e) :
    (h.insert e he).data.Perm (e :: h.data) :=
  RankedHeap.insert_perm h.ranked e

theorem build_perm (params : HeapParams) (entries : List HeapEntry)
    (hbounded : ∀ e ∈ entries, params.Bounded e) :
    (build params entries hbounded).data.Perm entries := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
      simp only [build]
      let htail : ∀ u ∈ entries, params.Bounded u :=
        fun u hu => hbounded u (by simp [hu])
      exact (insert_perm (build params entries htail) e (hbounded e (by simp))).trans
        (List.Perm.cons e (ih htail))

@[simp] theorem build_size (params : HeapParams) (entries : List HeapEntry)
    (hbounded : ∀ e ∈ entries, params.Bounded e) :
    (build params entries hbounded).data.length = entries.length := by
  exact (build_perm params entries hbounded).length_eq

@[simp] theorem insert_size {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) (he : params.Bounded e) :
    (h.insert e he).data.length = h.data.length + 1 := by
  exact RankedHeap.insert_size h.ranked e

/-- Erasing the bounded package recovers ranked extraction. -/
theorem extractMin_erases {params : HeapParams} (h : MinHeap params) :
    h.extractMin.map (fun p => (p.1, p.2.ranked)) = h.ranked.extractMax := by
  unfold extractMin
  split <;> simp_all

/-- Complete minimum, multiset, and size contract for one extraction. -/
theorem extractMin_spec {params : HeapParams} {h : MinHeap params}
    {e : HeapEntry} {h' : MinHeap params}
    (hextract : h.extractMin = some (e, h')) :
    (e :: h'.data).Perm h.data ∧
      h'.data.length + 1 = h.data.length ∧
      ∀ u ∈ h.data, HeapEntry.PriorityLE e u := by
  have hmapped := congrArg (Option.map (fun p => (p.1, p.2.ranked))) hextract
  rw [extractMin_erases] at hmapped
  have hranked : h.ranked.extractMax = some (e, h'.ranked) := by
    simpa using hmapped
  have hspec := RankedHeap.extractMax_spec hranked
  refine ⟨hspec.1, hspec.2.1, ?_⟩
  intro u hu
  exact (HeapParams.priorityLE_iff_rank_ge
    (h.bounded e ((List.Perm.mem_iff hspec.1).mp (by simp)))
    (h.bounded u hu)).2 (hspec.2.2 u hu)

theorem extractMin_eq_none_iff {params : HeapParams} (h : MinHeap params) :
    h.extractMin = none ↔ h.data = [] := by
  constructor
  · intro hnone
    have hmapped :
        h.extractMin.map (fun p => (p.1, p.2.ranked)) = none := by simp [hnone]
    rw [extractMin_erases] at hmapped
    exact (RankedHeap.extractMax_eq_none_iff h.ranked).mp hmapped
  · intro hempty
    have hranked : h.ranked.extractMax = none :=
      (RankedHeap.extractMax_eq_none_iff h.ranked).mpr hempty
    have hmapped :
        h.extractMin.map (fun p => (p.1, p.2.ranked)) = none := by
      rw [extractMin_erases, hranked]
    cases hextract : h.extractMin with
    | none => rfl
    | some result => simp [hextract] at hmapped

end MinHeap

end CLRS.HuffmanV2
