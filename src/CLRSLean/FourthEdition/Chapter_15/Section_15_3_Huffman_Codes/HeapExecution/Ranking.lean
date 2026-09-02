import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Entry

/-!
# Order-preserving finite ranks for Huffman heap entries

Chapter 6 verifies max-heaps of natural keys.  On one Huffman input, all active
frequencies and stamps have explicit finite bounds.  Complementing the bounded
lexicographic code turns the smallest Huffman priority into the largest natural
rank and permits direct reuse of those max-heap theorems.
-/

namespace CLRS.HuffmanV2

/-- Bounds fixed for one complete Huffman execution. -/
structure HeapParams where
  inputSize : Nat
  totalFreq : Nat
  deriving Repr, DecidableEq

namespace HeapParams

/-- The stamp base is strictly larger than every initial or merge stamp. -/
def base (p : HeapParams) : Nat := 2 * p.inputSize + 1

/-- Lexicographic priority encoded with the bounded stamp as the low digit. -/
def code (p : HeapParams) (e : HeapEntry) : Nat :=
  rootFreq e.tree * p.base + e.stamp

/-- One-past-frequency capacity for complementing a bounded code. -/
def capacity (p : HeapParams) : Nat :=
  (p.totalFreq + 1) * p.base

/-- Natural max-heap rank: a smaller frequency/stamp pair means a larger rank. -/
def rank (p : HeapParams) (e : HeapEntry) : Nat :=
  p.capacity - p.code e

/-- The entry lies inside the fixed frequency and stamp envelope. -/
def Bounded (p : HeapParams) (e : HeapEntry) : Prop :=
  rootFreq e.tree ≤ p.totalFreq ∧ e.stamp < p.base

theorem base_pos (p : HeapParams) : 0 < p.base := by
  simp [base]

theorem code_lt_capacity {p : HeapParams} {e : HeapEntry}
    (he : p.Bounded e) : p.code e < p.capacity := by
  have hmul : rootFreq e.tree * p.base ≤ p.totalFreq * p.base :=
    Nat.mul_le_mul_right p.base he.1
  have hadd :
      rootFreq e.tree * p.base + e.stamp <
        p.totalFreq * p.base + p.base :=
    Nat.add_lt_add_of_le_of_lt hmul he.2
  simpa [code, capacity, Nat.add_mul] using hadd

theorem code_le_capacity {p : HeapParams} {e : HeapEntry}
    (he : p.Bounded e) : p.code e ≤ p.capacity :=
  Nat.le_of_lt (code_lt_capacity he)

private theorem code_lt_of_freq_lt {p : HeapParams} {a b : HeapEntry}
    (ha : p.Bounded a) (hfreq : rootFreq a.tree < rootFreq b.tree) :
    p.code a < p.code b := by
  have hstamp :
      rootFreq a.tree * p.base + a.stamp <
        rootFreq a.tree * p.base + p.base :=
    Nat.add_lt_add_left ha.2 _
  have hfreqMul :
      (rootFreq a.tree + 1) * p.base ≤ rootFreq b.tree * p.base :=
    Nat.mul_le_mul_right p.base (Nat.succ_le_of_lt hfreq)
  calc
    p.code a < (rootFreq a.tree + 1) * p.base := by
      simpa [code, Nat.add_mul] using hstamp
    _ ≤ rootFreq b.tree * p.base := hfreqMul
    _ ≤ p.code b := by simp [code]

/-- Bounded mixed-radix encoding exactly reflects lexicographic priority. -/
theorem priorityLE_iff_code_le {p : HeapParams} {a b : HeapEntry}
    (ha : p.Bounded a) (hb : p.Bounded b) :
    HeapEntry.PriorityLE a b ↔ p.code a ≤ p.code b := by
  constructor
  · intro hab
    rcases hab with hfreq | ⟨hfreq, hstamp⟩
    · exact Nat.le_of_lt (code_lt_of_freq_lt ha hfreq)
    · simpa [code, hfreq] using Nat.add_le_add_left hstamp
  · intro hcode
    by_cases hfreq : rootFreq a.tree < rootFreq b.tree
    · exact Or.inl hfreq
    · have hba : rootFreq b.tree ≤ rootFreq a.tree := Nat.le_of_not_gt hfreq
      by_cases heq : rootFreq a.tree = rootFreq b.tree
      · right
        refine ⟨heq, ?_⟩
        simpa [code, heq] using hcode
      · have hrev : rootFreq b.tree < rootFreq a.tree :=
          Nat.lt_of_le_of_ne hba (Ne.symm heq)
        have hstrict : p.code b < p.code a := code_lt_of_freq_lt hb hrev
        omega

/-- Complemented rank reverses the bounded priority order exactly. -/
theorem priorityLE_iff_rank_ge {p : HeapParams} {a b : HeapEntry}
    (ha : p.Bounded a) (hb : p.Bounded b) :
    HeapEntry.PriorityLE a b ↔ p.rank b ≤ p.rank a := by
  rw [priorityLE_iff_code_le ha hb]
  unfold rank
  have hca := code_le_capacity ha
  have hcb := code_le_capacity hb
  omega

/-- The frequency total attached to a raw table. -/
def tableTotal (xs : List (Nat × Nat)) : Nat :=
  (xs.map Prod.snd).sum

/-- Fixed heap bounds used by the execution on a frequency table. -/
def ofFreqs (xs : List (Nat × Nat)) : HeapParams :=
  { inputSize := xs.length, totalFreq := tableTotal xs }

end HeapParams

end CLRS.HuffmanV2
