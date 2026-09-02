import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes

/-!
# Stable entries for the executable Huffman heap

The existing list implementation inserts a newly created tree before older
trees of the same frequency.  A distinct stamp records that tie-breaking rule
inside the heap priority.
-/

namespace CLRS.HuffmanV2

/-- A Huffman tree together with its stable priority-queue stamp. -/
structure HeapEntry where
  tree : HuffTree
  stamp : Nat
  deriving Repr, DecidableEq

namespace HeapEntry

/-- The observable priority components of a heap entry. -/
def priority (e : HeapEntry) : Nat × Nat :=
  (rootFreq e.tree, e.stamp)

/-- Lexicographic non-strict priority order: frequency first, stamp second. -/
def PriorityLE (a b : HeapEntry) : Prop :=
  rootFreq a.tree < rootFreq b.tree ∨
    (rootFreq a.tree = rootFreq b.tree ∧ a.stamp ≤ b.stamp)

/-- Lexicographic strict priority order: frequency first, stamp second. -/
def PriorityLT (a b : HeapEntry) : Prop :=
  rootFreq a.tree < rootFreq b.tree ∨
    (rootFreq a.tree = rootFreq b.tree ∧ a.stamp < b.stamp)

instance (a b : HeapEntry) : Decidable (PriorityLE a b) := by
  unfold PriorityLE
  infer_instance

instance (a b : HeapEntry) : Decidable (PriorityLT a b) := by
  unfold PriorityLT
  infer_instance

theorem priorityLE_refl (a : HeapEntry) : PriorityLE a a := by
  right
  exact ⟨rfl, Nat.le_refl _⟩

theorem priorityLE_trans {a b c : HeapEntry}
    (hab : PriorityLE a b) (hbc : PriorityLE b c) : PriorityLE a c := by
  rcases hab with hab | ⟨habFreq, habStamp⟩
  · rcases hbc with hbc | ⟨hbcFreq, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hbc | ⟨hbcFreq, hbcStamp⟩
    · left; omega
    · right
      exact ⟨habFreq.trans hbcFreq, Nat.le_trans habStamp hbcStamp⟩

theorem priorityLE_total (a b : HeapEntry) :
    PriorityLE a b ∨ PriorityLE b a := by
  by_cases hfreq : rootFreq a.tree = rootFreq b.tree
  · rcases Nat.le_total a.stamp b.stamp with hab | hba
    · exact Or.inl (Or.inr ⟨hfreq, hab⟩)
    · exact Or.inr (Or.inr ⟨hfreq.symm, hba⟩)
  · rcases Nat.lt_or_gt_of_ne hfreq with hab | hba
    · exact Or.inl (Or.inl hab)
    · exact Or.inr (Or.inl hba)

theorem priorityLE_antisymm_components {a b : HeapEntry}
    (hab : PriorityLE a b) (hba : PriorityLE b a) :
    rootFreq a.tree = rootFreq b.tree ∧ a.stamp = b.stamp := by
  rcases hab with hab | ⟨habFreq, habStamp⟩
  · rcases hba with hba | ⟨hbaFreq, _⟩ <;> omega
  · rcases hba with hba | ⟨hbaFreq, hbaStamp⟩
    · omega
    · exact ⟨habFreq, Nat.le_antisymm habStamp hbaStamp⟩

theorem priorityLT_iff_le_not_le (a b : HeapEntry) :
    PriorityLT a b ↔ PriorityLE a b ∧ ¬ PriorityLE b a := by
  constructor
  · intro h
    constructor
    · rcases h with h | ⟨hfreq, hstamp⟩
      · exact Or.inl h
      · exact Or.inr ⟨hfreq, Nat.le_of_lt hstamp⟩
    · intro hba
      rcases h with h | ⟨hfreq, hstamp⟩
      · rcases hba with hba | ⟨hbaFreq, _⟩ <;> omega
      · rcases hba with hba | ⟨hbaFreq, hbaStamp⟩ <;> omega
  · rintro ⟨hab, hnba⟩
    rcases hab with hab | ⟨hfreq, hstamp⟩
    · exact Or.inl hab
    · right
      refine ⟨hfreq, Nat.lt_of_le_of_ne hstamp ?_⟩
      intro heq
      apply hnba
      exact Or.inr ⟨hfreq.symm, Nat.le_of_eq heq.symm⟩

theorem priorityLT_irrefl (a : HeapEntry) : ¬ PriorityLT a a := by
  intro h
  rcases h with h | ⟨_, h⟩ <;> omega

theorem priorityLT_trans {a b c : HeapEntry}
    (hab : PriorityLT a b) (hbc : PriorityLT b c) : PriorityLT a c := by
  rcases hab with hab | ⟨habFreq, habStamp⟩
  · rcases hbc with hbc | ⟨hbcFreq, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hbc | ⟨hbcFreq, hbcStamp⟩
    · left; omega
    · right
      exact ⟨habFreq.trans hbcFreq, Nat.lt_trans habStamp hbcStamp⟩

theorem priorityLT_of_not_le {a b : HeapEntry}
    (h : ¬ PriorityLE b a) : PriorityLT a b := by
  have hab := priorityLE_total a b
  rcases hab with hab | hba
  · exact (priorityLT_iff_le_not_le a b).2 ⟨hab, h⟩
  · exact False.elim (h hba)

theorem priorityLE_of_not_lt {a b : HeapEntry}
    (h : ¬ PriorityLT b a) : PriorityLE a b := by
  rcases priorityLE_total a b with hab | hba
  · exact hab
  · by_contra hnab
    exact h (priorityLT_of_not_le hnab)

end HeapEntry

/-- Decorate a list with consecutive stamps starting at the supplied base. -/
def decorateFrom : Nat → List HuffTree → List HeapEntry
  | _, [] => []
  | base, t :: ts =>
      { tree := t, stamp := base } :: decorateFrom (base + 1) ts

/-- Initial leaves use stamps at least the input length. -/
def initialEntries (ts : List HuffTree) : List HeapEntry :=
  decorateFrom ts.length ts

/-- A merge uses the current queue size to obtain the next decreasing stamp. -/
def mergedEntry (queueSize : Nat) (a b : HeapEntry) : HeapEntry :=
  { tree := unite a.tree b.tree, stamp := queueSize - 2 }

@[simp] theorem decorateFrom_length (base : Nat) (ts : List HuffTree) :
    (decorateFrom base ts).length = ts.length := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih => simp [decorateFrom, ih]

@[simp] theorem decorateFrom_map_tree (base : Nat) (ts : List HuffTree) :
    (decorateFrom base ts).map HeapEntry.tree = ts := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih => simp [decorateFrom, ih]

@[simp] theorem decorateFrom_map_stamp (base : Nat) (ts : List HuffTree) :
    (decorateFrom base ts).map HeapEntry.stamp = List.range' base ts.length := by
  induction ts generalizing base with
  | nil => simp [decorateFrom]
  | cons t ts ih =>
      simp [decorateFrom, ih, List.range'_succ]

@[simp] theorem initialEntries_length (ts : List HuffTree) :
    (initialEntries ts).length = ts.length := by
  simp [initialEntries]

@[simp] theorem initialEntries_map_tree (ts : List HuffTree) :
    (initialEntries ts).map HeapEntry.tree = ts := by
  simp [initialEntries]

theorem decorateFrom_stamp_ge {base : Nat} {ts : List HuffTree} {e : HeapEntry}
    (he : e ∈ decorateFrom base ts) : base ≤ e.stamp := by
  induction ts generalizing base with
  | nil => simp [decorateFrom] at he
  | cons t ts ih =>
      simp only [decorateFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ base) (ih he)

theorem decorateFrom_stamp_lt {base : Nat} {ts : List HuffTree} {e : HeapEntry}
    (he : e ∈ decorateFrom base ts) : e.stamp < base + ts.length := by
  induction ts generalizing base with
  | nil => simp [decorateFrom] at he
  | cons t ts ih =>
      simp only [decorateFrom, List.mem_cons] at he
      rcases he with rfl | he
      · simp
      · have h := ih he
        simp only [List.length_cons]
        omega

theorem initialEntries_stamp_ge {ts : List HuffTree} {e : HeapEntry}
    (he : e ∈ initialEntries ts) : ts.length ≤ e.stamp := by
  exact decorateFrom_stamp_ge he

theorem initialEntries_stamps_nodup (ts : List HuffTree) :
    ((initialEntries ts).map HeapEntry.stamp).Nodup := by
  rw [initialEntries, decorateFrom_map_stamp]
  exact List.nodup_range'

@[simp] theorem mergedEntry_tree (queueSize : Nat) (a b : HeapEntry) :
    (mergedEntry queueSize a b).tree = unite a.tree b.tree := rfl

@[simp] theorem mergedEntry_stamp (queueSize : Nat) (a b : HeapEntry) :
    (mergedEntry queueSize a b).stamp = queueSize - 2 := rfl

end CLRS.HuffmanV2
