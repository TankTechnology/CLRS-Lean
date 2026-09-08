import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S3_ExecutablePrim
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming.Execution

/-!
# Prim's cached array queue

The queue is an array-backed {lit}`Vector`, with one cell per vertex. Extraction
scans the array and carries the current minimum cell, so it never traverses a
chain of functional updates. Relaxation reads one target cell and writes it
only on a strict improvement. Input adjacency lists are stored separately.
-/
namespace CLRS.MST.ExecutablePrim.ArrayPrim
variable {n : Nat} {E : Type}

structure Cell (E : Type) where
  active : Bool := true
  key : Key := ⊤
  parent : Option E := none
  deriving Repr, DecidableEq

abbrev Cells (n : Nat) (E : Type) := Vector (Cell E) n

def read (q : Cells n E) (v : Fin n) : Cell E := q[v.val]
def write (q : Cells n E) (v : Fin n) (c : Cell E) : Cells n E := q.set v.val c

@[simp] theorem read_write (q : Cells n E) (u v : Fin n) (c : Cell E) :
    read (write q u c) v = if u = v then c else read q v := by
  simp only [read, write, Vector.getElem_set]
  simp [Fin.ext_iff]

/-- Initialization appends each queue cell once, using the shared counted array builder. -/
def initialCells (n : Nat) : Cells n E × Nat :=
  let b := CLRS.Chapter15.DPExecution.buildRow (fun _ => (({} : Cell E), 0)) n
  (⟨b.cells, by simp [b]⟩, b.writes)

@[simp] theorem initialCells_writes : (initialCells (E := E) n).2 = n := by
  simp [initialCells]

@[simp] theorem initialCells_read (v : Fin n) : read (initialCells (E := E) n).1 v = {} := by
  simp [initialCells, read, CLRS.Chapter15.DPExecution.buildRow_cells]

/-- Deactivation is one cached-cell write, retaining the selected parent and key. -/
def deactivate (q : Cells n E) (v : Fin n) : Cells n E :=
  write q v { read q v with active := false }

@[simp] theorem deactivate_active (q : Cells n E) (u v : Fin n) :
    (read (deactivate q u) v).active = if u = v then false else (read q v).active := by
  by_cases h : u = v <;> simp [deactivate, h]

@[simp] theorem deactivate_key (q : Cells n E) (u v : Fin n) :
    (read (deactivate q u) v).key = (read q v).key := by
  by_cases h : u = v <;> simp [deactivate, h]

@[simp] theorem deactivate_parent (q : Cells n E) (u v : Fin n) :
    (read (deactivate q u) v).parent = (read q v).parent := by
  by_cases h : u = v <;> simp [deactivate, h]

structure Scan (n : Nat) (E : Type) where
  choice : Option (Fin n × Cell E)
  reads : Nat
  comparisons : Nat

def scan (q : Cells n E) : List (Fin n) → Scan n E
  | [] => ⟨none, 0, 0⟩
  | v :: vs =>
    let old := scan q vs
    let cell := read q v
    if cell.active then
      match old.choice with
      | none => ⟨some (v, cell), old.reads + 1, old.comparisons⟩
      | some (u, prior) =>
        ⟨if cell.key ≤ prior.key then some (v, cell) else some (u, prior),
          old.reads + 1, old.comparisons + 1⟩
    else ⟨old.choice, old.reads + 1, old.comparisons⟩

theorem scan_counts (q : Cells n E) (vs : List (Fin n)) :
    (scan q vs).reads = vs.length ∧ (scan q vs).comparisons ≤ vs.length := by
  induction vs with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan]
    split
    · split <;> simp only [List.length_cons] <;> omega
    · simp only [List.length_cons]; omega

theorem scan_none (q : Cells n E) (vs : List (Fin n)) :
    (scan q vs).choice = none ↔ ∀ v ∈ vs, (read q v).active = false := by
  induction vs with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan]
    split
    · rename_i ha
      split
      · simp_all
      · split <;> simp_all
    · rename_i ha
      have hf := Bool.eq_false_iff.mpr ha
      simpa [hf] using ih


theorem scan_some (q : Cells n E) (vs : List (Fin n)) (u : Fin n) (c : Cell E)
    (h : (scan q vs).choice = some (u,c)) :
    u ∈ vs ∧ c = read q u ∧ c.active = true ∧
      ∀ v ∈ vs, (read q v).active = true → c.key ≤ (read q v).key := by
  induction vs generalizing u c with
  | nil => simp [scan] at h
  | cons v vs ih =>
    simp only [scan] at h
    split at h
    · rename_i ha
      split at h
      · rename_i hn
        cases h
        refine ⟨by simp, rfl, ha, ?_⟩
        intro x hx hxactive
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · have hf := (scan_none q vs).1 hn x hx
          simp [hf] at hxactive
      · rename_i v' c' ho
        have old := ih v' c' ho
        split at h
        · rename_i hle
          cases h
          refine ⟨by simp, rfl, ha, ?_⟩
          intro x hx hxactive
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact hle.trans (old.2.2.2 x hx hxactive)
        · rename_i hle
          cases h
          refine ⟨by simp [old.1], old.2.1, old.2.2.1, ?_⟩
          intro x hx hxactive
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_of_not_ge hle
          · exact old.2.2.2 x hx hxactive
    · rename_i ha
      have old := ih u c h
      refine ⟨by simp [old.1], old.2.1, old.2.2.1, ?_⟩
      intro x hx hxactive
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (ha hxactive).elim
      · exact old.2.2.2 x hx hxactive


structure Relaxed (n : Nat) (E : Type) where
  cells : Cells n E
  edgeVisits : Nat
  tests : Nat
  writes : Nat

def relax (w : E → Nat) (q : Cells n E) (v : Fin n) (e : E) : Relaxed n E :=
  let cell := read q v
  if cell.active then
    if (w e : Key) < cell.key then
      ⟨write q v ⟨true, w e, some e⟩, 1, 1, 1⟩
    else ⟨q, 1, 1, 0⟩
  else ⟨q, 1, 0, 0⟩

@[simp] theorem relax_active (w : E → Nat) (q : Cells n E) (v x : Fin n) (e : E) :
    (read (relax w q v e).cells x).active = (read q x).active := by
  simp only [relax]
  split
  · rename_i ha
    split
    · by_cases hx : v = x
      · subst v; simp [ha]
      · simp [hx]
    · rfl
  · rfl

theorem relax_key_le (w : E → Nat) (q : Cells n E) (v x : Fin n) (e : E) :
    (read (relax w q v e).cells x).key ≤ (read q x).key := by
  simp only [relax]
  split
  · split
    · rename_i hk
      by_cases hx : v = x
      · subst v; simpa using hk.le
      · simp [hx]
    · exact le_rfl
  · exact le_rfl

theorem relax_target_le (w : E → Nat) (q : Cells n E) (v : Fin n) (e : E)
    (ha : (read q v).active = true) :
    (read (relax w q v e).cells v).key ≤ (w e : Key) := by
  simp only [relax, ha, ↓reduceIte]
  split
  · simp
  · rename_i h; exact le_of_not_gt h

theorem relax_changed (w : E → Nat) (q : Cells n E) (v x : Fin n) (e : E) :
    read (relax w q v e).cells x = read q x ∨
      (x = v ∧ read (relax w q v e).cells x = ⟨true, w e, some e⟩) := by
  simp only [relax]
  split
  · split
    · by_cases hx : v = x
      · subst v; right; simp
      · left; simp [hx]
    · exact Or.inl rfl
  · exact Or.inl rfl

def relaxAll (w : E → Nat) (q : Cells n E) : List (Fin n × E) → Relaxed n E
  | [] => ⟨q, 0, 0, 0⟩
  | (v,e) :: es =>
    let first := relax w q v e
    let rest := relaxAll w first.cells es
    ⟨rest.cells, first.edgeVisits + rest.edgeVisits,
      first.tests + rest.tests, first.writes + rest.writes⟩

theorem relax_counts (w : E → Nat) (q : Cells n E) (v : Fin n) (e : E) :
    (relax w q v e).edgeVisits = 1 ∧ (relax w q v e).tests ≤ 1 ∧
      (relax w q v e).writes ≤ (relax w q v e).tests := by
  simp only [relax]
  split
  · split <;> simp
  · simp

theorem relaxAll_counts (w : E → Nat) (q : Cells n E) (es : List (Fin n × E)) :
    (relaxAll w q es).edgeVisits = es.length ∧
    (relaxAll w q es).tests ≤ es.length ∧
    (relaxAll w q es).writes ≤ (relaxAll w q es).tests := by
  induction es generalizing q with
  | nil => simp [relaxAll]
  | cons ve es ih =>
    rcases ve with ⟨v,e⟩
    have old := ih (relax w q v e).cells
    have first := relax_counts w q v e
    simp only [relaxAll, List.length_cons]
    omega

@[simp] theorem relaxAll_active (w : E → Nat) (q : Cells n E)
    (es : List (Fin n × E)) (x : Fin n) :
    (read (relaxAll w q es).cells x).active = (read q x).active := by
  induction es generalizing q with
  | nil => rfl
  | cons ve es ih => simp [relaxAll, ih]

theorem relaxAll_key_le (w : E → Nat) (q : Cells n E)
    (es : List (Fin n × E)) (x : Fin n) :
    (read (relaxAll w q es).cells x).key ≤ (read q x).key := by
  induction es generalizing q with
  | nil => exact le_rfl
  | cons ve es ih => exact (ih _).trans (relax_key_le w q ve.1 x ve.2)

theorem relaxAll_target_le (w : E → Nat) (q : Cells n E) (es : List (Fin n × E))
    (v : Fin n) (e : E) (he : (v,e) ∈ es) (ha : (read q v).active = true) :
    (read (relaxAll w q es).cells v).key ≤ (w e : Key) := by
  induction es generalizing q with
  | nil => simp at he
  | cons ve es ih =>
    rcases ve with ⟨u,f⟩
    rcases List.mem_cons.mp he with h | he
    · cases h
      exact (relaxAll_key_le w _ es v).trans (relax_target_le w q v e ha)
    · exact ih (relax w q u f).cells he (by simpa using ha)

theorem relaxAll_origin (w : E → Nat) (q : Cells n E) (es : List (Fin n × E))
    (x : Fin n) :
    read (relaxAll w q es).cells x = read q x ∨
      ∃ e, (x,e) ∈ es ∧ read (relaxAll w q es).cells x = ⟨true, w e, some e⟩ := by
  induction es generalizing q with
  | nil => exact Or.inl rfl
  | cons ve es ih =>
    rcases ve with ⟨v,e⟩
    rcases ih (relax w q v e).cells with hold | ⟨f,hf,hcell⟩
    · rcases relax_changed w q v x e with hs | ⟨rfl,hs⟩
      · exact Or.inl (hold.trans hs)
      · exact Or.inr ⟨e, by simp, hold.trans hs⟩
    · exact Or.inr ⟨f, by simp [hf], hcell⟩

end CLRS.MST.ExecutablePrim.ArrayPrim
