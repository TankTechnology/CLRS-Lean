import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Execution
import CLRSLean.FourthEdition.Chapter_06.Section_06_4_Heapsort.CostedExecution
import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues.Insert.Cost

/-!
# Costed binary-heap Huffman execution

The counter in this module is the Chapter 6 abstract heap-controller metric:
one unit is charged for each visited upward- or downward-repair frame.  List
allocation, indexing, guards, and proof objects are deliberately outside this
metric.  Every charge is read from the same ranked array and the same branch
conditions as the executable heap operation; it is not a detached envelope.
-/

namespace CLRS.HuffmanV2

/-- A value paired with the heap-controller work used to produce it. -/
structure Costed (α : Type) where
  value : α
  work : Nat

/-- One global logarithmic allowance for a heap whose size is at most the input size. -/
def HeapParams.opBudget (params : HeapParams) : Nat :=
  Nat.log 2 (params.inputSize + 1) + 1

/-- Actual upward-repair work performed by one heap insertion. -/
def MinHeap.insertWork {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) : Nat :=
  (CLRS.Chapter06.arrayHeapInsertWithCost
    (h.data.map params.rank) (params.rank e)).2

theorem MinHeap.insertWork_le_log {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) :
    h.insertWork e ≤ Nat.log 2 (h.data.length + 1) + 1 := by
  simpa [MinHeap.insertWork] using
    CLRS.Chapter06.arrayHeapInsertWithCost_cost_le_log
      (h.data.map params.rank) (params.rank e)

theorem MinHeap.insertWork_le_budget {params : HeapParams} (h : MinHeap params)
    (e : HeapEntry) (hsize : h.data.length ≤ params.inputSize) :
    h.insertWork e ≤ params.opBudget := by
  have hstep := h.insertWork_le_log e
  have hlog : Nat.log 2 (h.data.length + 1) ≤
      Nat.log 2 (params.inputSize + 1) :=
    Nat.log_mono_right (by omega)
  exact hstep.trans (Nat.add_le_add_right hlog 1)

/-- Actual downward-repair work performed by extracting a nonempty heap root. -/
def MinHeap.extractWork {params : HeapParams} (h : MinHeap params) : Nat :=
  match h.data with
  | [] => 0
  | root :: rest =>
      let moved := swapEntries (root :: rest) 0 rest.length
      let active := moved.take rest.length
      (CLRS.Chapter06.maxHeapifyFuelWithCost rest.length
        (active.map params.rank) rest.length 0).2

theorem MinHeap.extractWork_le_log {params : HeapParams} (h : MinHeap params) :
    h.extractWork ≤ Nat.log 2 (h.data.length + 1) + 1 := by
  unfold MinHeap.extractWork
  cases hdata : h.ranked.data with
  | nil => simp [MinHeap.data, hdata]
  | cons root rest =>
      by_cases hrest : rest.length = 0
      · simp [MinHeap.data, hdata, hrest,
          CLRS.Chapter06.maxHeapifyFuelWithCost]
      · have hpos : 0 < rest.length := Nat.pos_of_ne_zero hrest
        let moved := swapEntries (root :: rest) 0 rest.length
        let active := moved.take rest.length
        have hstep := CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_log
          rest.length (active.map params.rank) rest.length 0 hpos
        have hlog : Nat.log 2 rest.length ≤
            Nat.log 2 ((root :: rest).length + 1) :=
          Nat.log_mono_right (by simp; omega)
        simp only [MinHeap.data, hdata]
        change
          (CLRS.Chapter06.maxHeapifyFuelWithCost rest.length
            (active.map params.rank) rest.length 0).2 ≤
              Nat.log 2 ((root :: rest).length + 1) + 1
        exact hstep.trans (Nat.add_le_add_right hlog 1)

theorem MinHeap.extractWork_le_budget {params : HeapParams} (h : MinHeap params)
    (hsize : h.data.length ≤ params.inputSize) :
    h.extractWork ≤ params.opBudget := by
  have hstep := h.extractWork_le_log
  have hlog : Nat.log 2 (h.data.length + 1) ≤
      Nat.log 2 (params.inputSize + 1) :=
    Nat.log_mono_right (by omega)
  exact hstep.trans (Nat.add_le_add_right hlog 1)

/-! ## Costed heap construction -/

/-- Repeated insertion paired with the exact sum of its upward-repair work. -/
def MinHeap.buildWithCost (params : HeapParams) :
    (entries : List HeapEntry) →
      (∀ e ∈ entries, params.Bounded e) → MinHeap params × Nat
  | [], _ => (MinHeap.empty params, 0)
  | e :: entries, hbounded =>
      let htail : ∀ u ∈ entries, params.Bounded u :=
        fun u hu => hbounded u (by simp [hu])
      let tail := buildWithCost params entries htail
      let he : params.Bounded e := hbounded e (by simp)
      (tail.1.insert e he, tail.2 + tail.1.insertWork e)

@[simp] theorem MinHeap.buildWithCost_size (params : HeapParams)
    (entries : List HeapEntry) (hbounded : ∀ e ∈ entries, params.Bounded e) :
    (MinHeap.buildWithCost params entries hbounded).1.data.length = entries.length := by
  induction entries with
  | nil => simp [MinHeap.buildWithCost, MinHeap.empty, MinHeap.data,
      RankedHeap.empty]
  | cons e entries ih =>
      simp only [MinHeap.buildWithCost, MinHeap.insert_size]
      let htail : ∀ u ∈ entries, params.Bounded u :=
        fun u hu => hbounded u (by simp [hu])
      simpa using congrArg Nat.succ (ih htail)

/-- Erasing construction cost recovers the verified executable heap data. -/
theorem MinHeap.buildWithCost_data (params : HeapParams)
    (entries : List HeapEntry) (hbounded : ∀ e ∈ entries, params.Bounded e) :
    (MinHeap.buildWithCost params entries hbounded).1.data =
      (MinHeap.build params entries hbounded).data := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
      simp only [MinHeap.buildWithCost, MinHeap.build]
      let htail : ∀ u ∈ entries, params.Bounded u :=
        fun u hu => hbounded u (by simp [hu])
      change
        heapInsertRaw params.rank
            (MinHeap.buildWithCost params entries htail).1.data e =
          heapInsertRaw params.rank (MinHeap.build params entries htail).data e
      rw [ih htail]

theorem MinHeap.buildWithCost_work_le (params : HeapParams)
    (entries : List HeapEntry) (hbounded : ∀ e ∈ entries, params.Bounded e)
    (hsize : entries.length ≤ params.inputSize) :
    (MinHeap.buildWithCost params entries hbounded).2 ≤
      entries.length * params.opBudget := by
  induction entries with
  | nil => simp [MinHeap.buildWithCost]
  | cons e entries ih =>
      let htail : ∀ u ∈ entries, params.Bounded u :=
        fun u hu => hbounded u (by simp [hu])
      have htailSize : entries.length ≤ params.inputSize := by
        simp only [List.length_cons] at hsize
        omega
      have hrec := ih htail htailSize
      have hentrySize :
          (MinHeap.buildWithCost params entries htail).1.data.length ≤
            params.inputSize := by
        rw [MinHeap.buildWithCost_size]
        exact htailSize
      have hstep := MinHeap.insertWork_le_budget
        (MinHeap.buildWithCost params entries htail).1 e hentrySize
      simp only [MinHeap.buildWithCost]
      change
        (MinHeap.buildWithCost params entries htail).2 +
            (MinHeap.buildWithCost params entries htail).1.insertWork e ≤
          (entries.length + 1) * params.opBudget
      rw [Nat.add_mul]
      omega

/-! ## Costed Huffman merge loop -/

/-- Exact repair-frame count along the executable Huffman loop's control path. -/
def heapHuffmanLoopWork {params : HeapParams} :
    Nat → HeapHuffmanState params → Nat
  | 0, _ => 0
  | fuel + 1, s =>
      let work₁ := s.heap.extractWork
      match hextract₁ : s.heap.extractMin with
      | none => work₁
      | some (e₁, h₁) =>
          let work₂ := h₁.extractWork
          match hextract₂ : h₁.extractMin with
          | none => work₁ + work₂
          | some (e₂, h₂) =>
              let next := HeapHuffmanState.mergeState s hextract₁ hextract₂
              let newEntry := mergedEntry s.heap.data.length e₁ e₂
              let insertWork := h₂.insertWork newEntry
              work₁ + work₂ + insertWork + heapHuffmanLoopWork fuel next

/-- The heap execution paired with its exact repair-frame count. -/
def heapHuffmanLoopWithCost {params : HeapParams}
    (fuel : Nat) (s : HeapHuffmanState params) : Costed HuffTree :=
  ⟨heapHuffmanLoop fuel s, heapHuffmanLoopWork fuel s⟩

/-- Removing the counter yields the complete uninstrumented heap execution. -/
theorem heapHuffmanLoopWithCost_value {params : HeapParams}
    (fuel : Nat) (s : HeapHuffmanState params) :
    (heapHuffmanLoopWithCost fuel s).value = heapHuffmanLoop fuel s := rfl

theorem heapHuffmanLoopWithCost_work_le {params : HeapParams}
    (fuel : Nat) (s : HeapHuffmanState params) :
    (heapHuffmanLoopWithCost fuel s).work ≤
      fuel * (3 * params.opBudget) := by
  induction fuel generalizing s with
  | zero => simp [heapHuffmanLoopWithCost, heapHuffmanLoopWork]
  | succ fuel ih =>
      change heapHuffmanLoopWork (fuel + 1) s ≤
        (fuel + 1) * (3 * params.opBudget)
      simp only [heapHuffmanLoopWork]
      split
      next hextract₁ =>
        have hwork₁ := s.heap.extractWork_le_budget s.size_le_input
        change s.heap.extractWork ≤ (fuel + 1) * (3 * params.opBudget)
        rw [Nat.succ_mul]
        omega
      next e₁ h₁ hextract₁ =>
        rcases MinHeap.extractMin_spec hextract₁ with
          ⟨_hperm₁, hlen₁, _hmin₁⟩
        have hsize := s.size_le_input
        have hsize₁ : h₁.data.length ≤ params.inputSize := by
          omega
        have hwork₁ := s.heap.extractWork_le_budget s.size_le_input
        have hwork₂ := h₁.extractWork_le_budget hsize₁
        split
        next hextract₂ =>
          change s.heap.extractWork + h₁.extractWork ≤
            (fuel + 1) * (3 * params.opBudget)
          rw [Nat.succ_mul]
          omega
        next e₂ h₂ hextract₂ =>
          rcases MinHeap.extractMin_spec hextract₂ with
            ⟨_hperm₂, hlen₂, _hmin₂⟩
          have hsize₂ : h₂.data.length ≤ params.inputSize := by
            omega
          have hinsert := h₂.insertWork_le_budget
            (mergedEntry s.heap.data.length e₁ e₂) hsize₂
          have hrec := ih (HeapHuffmanState.mergeState s hextract₁ hextract₂)
          change
            heapHuffmanLoopWork fuel
                (HeapHuffmanState.mergeState s hextract₁ hextract₂) ≤
              fuel * (3 * params.opBudget) at hrec
          change
            s.heap.extractWork + h₁.extractWork +
                h₂.insertWork (mergedEntry s.heap.data.length e₁ e₂) +
                heapHuffmanLoopWork fuel
                  (HeapHuffmanState.mergeState s hextract₁ hextract₂) ≤
              (fuel + 1) * (3 * params.opBudget)
          rw [Nat.succ_mul]
          omega

/-! ## Public costed program -/

/-- Verified heap Huffman paired with construction and merge-controller work. -/
def heapHuffmanOfFreqsWithCost (xs : List (Nat × Nat)) : Costed HuffTree :=
  let params := HeapParams.ofFreqs xs
  let entries := initialEntries (leavesOfFreqs xs)
  let hbounded := initialEntries_bounded xs
  let buildRun := MinHeap.buildWithCost params entries hbounded
  let mergeRun := heapHuffmanLoopWithCost xs.length (HeapHuffmanState.ofFreqs xs)
  ⟨mergeRun.value, buildRun.2 + mergeRun.work⟩

theorem heapHuffmanOfFreqsWithCost_value (xs : List (Nat × Nat)) :
    (heapHuffmanOfFreqsWithCost xs).value = heapHuffmanOfFreqs xs := by
  unfold heapHuffmanOfFreqsWithCost heapHuffmanOfFreqs
  exact heapHuffmanLoopWithCost_value xs.length (HeapHuffmanState.ofFreqs xs)

/-- Explicit `O(n log n)` controller-work envelope for the actual heap run. -/
theorem heapHuffmanOfFreqs_work_le_nlogn (xs : List (Nat × Nat)) :
    (heapHuffmanOfFreqsWithCost xs).work ≤
      xs.length * (4 * (Nat.log 2 (xs.length + 1) + 1)) := by
  let params := HeapParams.ofFreqs xs
  let entries := initialEntries (leavesOfFreqs xs)
  let hbounded := initialEntries_bounded xs
  have hentries : entries.length = xs.length := by
    simp [entries, leavesOfFreqs]
  have hbuild := MinHeap.buildWithCost_work_le params entries hbounded (by
    rw [hentries]
    rfl)
  have hmerge := heapHuffmanLoopWithCost_work_le xs.length
    (HeapHuffmanState.ofFreqs xs)
  change
    (MinHeap.buildWithCost params entries hbounded).2 +
        (heapHuffmanLoopWithCost xs.length (HeapHuffmanState.ofFreqs xs)).work ≤
      xs.length * (4 * (Nat.log 2 (xs.length + 1) + 1))
  have hbudget : params.opBudget = Nat.log 2 (xs.length + 1) + 1 := by
    rfl
  rw [hentries, hbudget] at hbuild
  rw [hbudget] at hmerge
  calc
    _ ≤ xs.length * (Nat.log 2 (xs.length + 1) + 1) +
        xs.length * (3 * (Nat.log 2 (xs.length + 1) + 1)) :=
      Nat.add_le_add hbuild hmerge
    _ = xs.length * (4 * (Nat.log 2 (xs.length + 1) + 1)) := by ring

end CLRS.HuffmanV2
