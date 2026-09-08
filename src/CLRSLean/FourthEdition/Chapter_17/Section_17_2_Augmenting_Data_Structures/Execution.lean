import CLRSLean.FourthEdition.Chapter_17.Section_17_2_Augmenting_Data_Structures

/-!
# Cached augmentation maintenance during insertion

The execution below reads cached child fields; it never calls {lit}`realAug`.
Each constructed node performs and counts one {lit}`combine`. Each successful
rotation performs and counts two such constructions and one rotation.
Insertion follows one search path and uses these rotation primitives in its
balancer. The returned counters belong to that same execution. Comparisons,
allocation, bit arithmetic, and reconstruction of persistent tree nodes are
not separate units in these augmentation-maintenance counters.

Refinement to the legacy recomputing insertion requires {lit}`WellAugmented`.
This module measures insertion and rotations, not deletion.
-/
namespace CLRS.Chapter14.AugmentationExecution
open CLRS.Chapter13 (Color RBTree)
open AugmentedRBTree

variable {α β : Type} [Inhabited β]

/-- Result and the primitive calls made while producing it. -/
structure Run (α β : Type) where
  tree : AugmentedRBTree α β
  combineCalls : Nat
  rotations : Nat
  deriving Repr

def pure (t : AugmentedRBTree α β) : Run α β := ⟨t, 0, 0⟩

def mapTree (f : AugmentedRBTree α β → AugmentedRBTree α β) (r : Run α β) : Run α β :=
  { r with tree := f r.tree }

/-- One local field recomputation, using only cached child fields. -/
def make (aug : Augmentation α β) (c : Color) (l : Run α β) (k : α)
    (r : Run α β) : Run α β :=
  ⟨.node c l.tree k (aug.combine k (storedAug aug l.tree) (storedAug aug r.tree)) r.tree,
    l.combineCalls + r.combineCalls + 1, l.rotations + r.rotations⟩

/-- The two changed nodes are rebuilt once each. A failed rotation is free. -/
def rotateLeft (aug : Augmentation α β) (t : Run α β) : Run α β :=
  match t.tree with
  | .node c a x _ (.node d b y _ e) =>
      let rotated := make aug d (make aug c (pure a) x (pure b)) y (pure e)
      ⟨rotated.tree, t.combineCalls + rotated.combineCalls, t.rotations + 1⟩
  | _ => t

def rotateRight (aug : Augmentation α β) (t : Run α β) : Run α β :=
  match t.tree with
  | .node c (.node d a x _ b) y _ e =>
      let rotated := make aug d (pure a) x (make aug c (pure b) y (pure e))
      ⟨rotated.tree, t.combineCalls + rotated.combineCalls, t.rotations + 1⟩
  | _ => t

/-- Color changes do not recompute a field. -/
def blackenLeft : AugmentedRBTree α β → AugmentedRBTree α β
  | .empty => .empty
  | .node c l k a r => .node c (repaintRoot .black l) k a r

def blackenRight : AugmentedRBTree α β → AugmentedRBTree α β
  | .empty => .empty
  | .node c l k a r => .node c l k a (repaintRoot .black r)

/-- Single and double rotations are actual calls to the primitives above. -/
def balanceLeft (aug : Augmentation α β) (l : AugmentedRBTree α β) (y : α)
    (r : AugmentedRBTree α β) : Run α β :=
  match l with
  | .node .red (.node .red _ _ _ _) _ _ _ =>
      rotateRight aug (make aug .black (pure (blackenLeft l)) y (pure r))
  | .node .red _ _ _ (.node .red _ _ _ _) =>
      rotateRight aug (make aug .black
        (mapTree blackenLeft (rotateLeft aug (pure l))) y (pure r))
  | _ => make aug .black (pure l) y (pure r)

def balanceRight (aug : Augmentation α β) (l : AugmentedRBTree α β) (y : α)
    (r : AugmentedRBTree α β) : Run α β :=
  match r with
  | .node .red (.node .red _ _ _ _) _ _ _ =>
      rotateLeft aug (make aug .black (pure l) y
        (mapTree blackenRight (rotateRight aug (pure r))))
  | .node .red _ _ _ (.node .red _ _ _ _) =>
      rotateLeft aug (make aug .black (pure l) y (pure (blackenRight r)))
  | _ => make aug .black (pure l) y (pure r)

/-- Add calls already performed in a recursive child, without rerunning it. -/
def after (earlier : Run α β) (next : Run α β) : Run α β :=
  ⟨next.tree, earlier.combineCalls + next.combineCalls, earlier.rotations + next.rotations⟩

def insertFixup (aug : Augmentation α β) (lt : α → α → Bool) (x : α) :
    AugmentedRBTree α β → Run α β
  | .empty => make aug .red (pure .empty) x (pure .empty)
  | .node c l y a r =>
      if lt x y then
        let child := insertFixup aug lt x l
        if c = .black then after child (balanceLeft aug child.tree y r)
        else make aug .red child y (pure r)
      else if lt y x then
        let child := insertFixup aug lt x r
        if c = .black then after child (balanceRight aug l y child.tree)
        else make aug .red (pure l) y child
      else pure (.node c l y a r)

def insert (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) : Run α β :=
  mapTree repaintBlack (insertFixup aug lt x t)

theorem make_refines (aug : Augmentation α β) (c : Color) (l r : Run α β) (k : α)
    (hl : WellAugmented aug l.tree) (hr : WellAugmented aug r.tree) :
    (make aug c l k r).tree = mk aug c l.tree k r.tree := by
  simp only [make, mk, storedAug_eq_realAug_of_wellAugmented aug hl,
    storedAug_eq_realAug_of_wellAugmented aug hr]

private theorem stored_node (aug : Augmentation α β) (c : Color)
    (l : AugmentedRBTree α β) (k : α) (a : β) (r : AugmentedRBTree α β) :
    storedAug aug (.node c l k a r) = a := rfl

theorem balanceLeft_refines (aug : Augmentation α β) (l r : AugmentedRBTree α β) (k : α)
    (hl : WellAugmented aug l) (hr : WellAugmented aug r) :
    (balanceLeft aug l k r).tree = AugmentedRBTree.balanceLeft aug l k r := by
  unfold balanceLeft
  split <;> (try simp_all only [WellAugmented]) <;> simp_all [AugmentedRBTree.balanceLeft, rotateLeft, rotateRight, make,
    mapTree, pure, blackenLeft, repaintRoot, mk, stored_node, realAug, storedAug_eq_realAug_of_wellAugmented]

theorem balanceRight_refines (aug : Augmentation α β) (l r : AugmentedRBTree α β) (k : α)
    (hl : WellAugmented aug l) (hr : WellAugmented aug r) :
    (balanceRight aug l k r).tree = AugmentedRBTree.balanceRight aug l k r := by
  unfold balanceRight
  split <;> (try simp_all only [WellAugmented]) <;> simp_all [AugmentedRBTree.balanceRight, rotateLeft, rotateRight, make,
    mapTree, pure, blackenRight, repaintRoot, mk, stored_node, realAug, storedAug_eq_realAug_of_wellAugmented]

theorem insertFixup_refines (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) (h : WellAugmented aug t) :
    (insertFixup aug lt x t).tree = AugmentedRBTree.insertFixup aug lt x t := by
  induction t with
  | empty => rfl
  | node c l y a r ihl ihr =>
    have hl := h.1
    have hr := h.2.1
    have il := ihl hl
    have ir := ihr hr
    have wl : WellAugmented aug (insertFixup aug lt x l).tree := by
      rw [il]; exact wellAugmented_insertFixup aug lt x hl
    have wr : WellAugmented aug (insertFixup aug lt x r).tree := by
      rw [ir]; exact wellAugmented_insertFixup aug lt x hr
    simp only [insertFixup, AugmentedRBTree.insertFixup]
    split
    · split
      · simp only [after]
        rw [balanceLeft_refines aug _ _ _ wl hr, il]
      · rw [make_refines aug _ _ _ _ wl hr, il]; rfl
    · split
      · split
        · simp only [after]
          rw [balanceRight_refines aug _ _ _ hl wr, ir]
        · rw [make_refines aug _ _ _ _ hl wr, ir]; rfl
      · rfl

theorem insert_refines (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) (h : WellAugmented aug t) :
    (insert aug lt x t).tree = AugmentedRBTree.insert aug lt x t := by
  simp only [insert, mapTree, AugmentedRBTree.insert, insertFixup_refines aug lt x t h]

theorem insert_wellAugmented (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) (h : WellAugmented aug t) :
    WellAugmented aug (insert aug lt x t).tree := by
  rw [insert_refines aug lt x t h]
  exact wellAugmented_insert aug lt x h

/-- The cached implementation erases to the existing functional RB insertion. -/
theorem insert_toRB (aug : Augmentation Nat β) (x : Nat) (t : AugmentedRBTree Nat β)
    (h : WellAugmented aug t) :
    toRB (insert aug natLt x t).tree = RBTree.insert x (toRB t) := by
  rw [insert_refines aug natLt x t h, AugmentedRBTree.toRB_insert]

/-- A rotation either returns the original run or adds exactly two combines and one rotation. -/
theorem rotateLeft_counts (aug : Augmentation α β) (t : Run α β) :
    rotateLeft aug t = t ∨
      ((rotateLeft aug t).combineCalls = t.combineCalls + 2 ∧
       (rotateLeft aug t).rotations = t.rotations + 1) := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => exact Or.inl rfl
  | node c l x v r =>
    cases r with
    | empty => exact Or.inl rfl
    | node d b y w e => exact Or.inr ⟨rfl, rfl⟩

theorem rotateRight_counts (aug : Augmentation α β) (t : Run α β) :
    rotateRight aug t = t ∨
      ((rotateRight aug t).combineCalls = t.combineCalls + 2 ∧
       (rotateRight aug t).rotations = t.rotations + 1) := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => exact Or.inl rfl
  | node c l x v r =>
    cases l with
    | empty => exact Or.inl rfl
    | node d a x w b => exact Or.inr ⟨rfl, rfl⟩

theorem rotateLeft_wellAugmented (aug : Augmentation α β) (t : Run α β)
    (h : WellAugmented aug t.tree) : WellAugmented aug (rotateLeft aug t).tree := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => trivial
  | node c l x v r =>
    cases r with
    | empty => exact h
    | node d b y w e =>
      simp_all [rotateLeft, make, pure, WellAugmented, realAug,
        storedAug_eq_realAug_of_wellAugmented]

theorem rotateRight_wellAugmented (aug : Augmentation α β) (t : Run α β)
    (h : WellAugmented aug t.tree) : WellAugmented aug (rotateRight aug t).tree := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => trivial
  | node c l y v r =>
    cases l with
    | empty => exact h
    | node d a x w b =>
      simp_all [rotateRight, make, pure, WellAugmented, realAug,
        storedAug_eq_realAug_of_wellAugmented]

/-- Erasure identifies each counted rotation with the ordinary RB primitive. -/
theorem rotateLeft_toRB (aug : Augmentation Nat β) (t : Run Nat β) :
    toRB (rotateLeft aug t).tree = RBTree.rotateLeft (toRB t.tree) := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => rfl
  | node c l x v r => cases r <;> rfl

theorem rotateRight_toRB (aug : Augmentation Nat β) (t : Run Nat β) :
    toRB (rotateRight aug t).tree = RBTree.rotateRight (toRB t.tree) := by
  rcases t with ⟨t, cc, rr⟩
  cases t with
  | empty => rfl
  | node c l x v r => cases l <;> rfl

/-- Generic-key structural height; cache values do not affect it. -/
def height : AugmentedRBTree α β → Nat
  | .empty => 0
  | .node _ l _ _ r => max (height l) (height r) + 1

theorem balanceLeft_counts (aug : Augmentation α β) (l r : AugmentedRBTree α β) (k : α) :
    (balanceLeft aug l k r).combineCalls ≤ 5 ∧ (balanceLeft aug l k r).rotations ≤ 2 := by
  unfold balanceLeft
  split <;> simp [rotateLeft, rotateRight, make, pure, mapTree, blackenLeft, repaintRoot]

theorem balanceRight_counts (aug : Augmentation α β) (l r : AugmentedRBTree α β) (k : α) :
    (balanceRight aug l k r).combineCalls ≤ 5 ∧ (balanceRight aug l k r).rotations ≤ 2 := by
  unfold balanceRight
  split <;> simp [rotateLeft, rotateRight, make, pure, mapTree, blackenRight, repaintRoot]

theorem insertFixup_counts (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) :
    (insertFixup aug lt x t).combineCalls ≤ 5 * height t + 1 ∧
      (insertFixup aug lt x t).rotations ≤ 2 * height t := by
  induction t with
  | empty => simp [insertFixup, make, pure, height]
  | node c l y a r il ir =>
    have hleft := Nat.le_max_left (height l) (height r)
    have hright := Nat.le_max_right (height l) (height r)
    simp only [insertFixup, height]
    split
    · split
      · have hb := balanceLeft_counts aug (insertFixup aug lt x l).tree r y
        simp only [after]
        omega
      · simp only [make, pure]
        omega
    · split
      · split
        · have hb := balanceRight_counts aug l (insertFixup aug lt x r).tree y
          simp only [after]
          omega
        · simp only [make, pure]
          omega
      · simp [pure]

theorem insert_counts (aug : Augmentation α β) (lt : α → α → Bool) (x : α)
    (t : AugmentedRBTree α β) :
    (insert aug lt x t).combineCalls ≤ 5 * height t + 1 ∧
      (insert aug lt x t).rotations ≤ 2 * height t :=
  insertFixup_counts aug lt x t

omit [Inhabited β] in
theorem height_eq_toRB (t : AugmentedRBTree Nat β) : height t = RBTree.height (toRB t) := by
  induction t with
  | empty => rfl
  | node c l y a r il ir => simp [height, toRB, RBTree.height, il, ir, Nat.add_comm]

/-- The bound applies to the actual cached execution's combine counter. -/
theorem insert_combineCalls_log_bound (aug : Augmentation Nat β) (lt : Nat → Nat → Bool)
    (x : Nat) (t : AugmentedRBTree Nat β) (hs : RBTree.RedBlackShape (toRB t)) :
    (insert aug lt x t).combineCalls ≤ 10 * Nat.log 2 (RBTree.size (toRB t) + 1) + 1 := by
  have hc := (insert_counts aug lt x t).1
  rw [height_eq_toRB] at hc
  have hh := RBTree.height_log_bound (toRB t) hs
  omega

theorem insert_rotations_log_bound (aug : Augmentation Nat β) (lt : Nat → Nat → Bool)
    (x : Nat) (t : AugmentedRBTree Nat β) (hs : RBTree.RedBlackShape (toRB t)) :
    (insert aug lt x t).rotations ≤ 4 * Nat.log 2 (RBTree.size (toRB t) + 1) := by
  have hc := (insert_counts aug lt x t).2
  rw [height_eq_toRB] at hc
  have hh := RBTree.height_log_bound (toRB t) hs
  omega

/-- Constant charges per counted combine and rotation, on the same run. -/
def maintenanceCost (combineCharge rotationCharge : Nat) (r : Run α β) : Nat :=
  combineCharge * r.combineCalls + rotationCharge * r.rotations

theorem insert_maintenanceCost_log_bound (aug : Augmentation Nat β) (lt : Nat → Nat → Bool)
    (x : Nat) (t : AugmentedRBTree Nat β) (hs : RBTree.RedBlackShape (toRB t))
    (combineCharge rotationCharge : Nat) :
    maintenanceCost combineCharge rotationCharge (insert aug lt x t) ≤
      combineCharge * (10 * Nat.log 2 (RBTree.size (toRB t) + 1) + 1) +
      rotationCharge * (4 * Nat.log 2 (RBTree.size (toRB t) + 1)) := by
  exact Nat.add_le_add
    (Nat.mul_le_mul_left _ (insert_combineCalls_log_bound aug lt x t hs))
    (Nat.mul_le_mul_left _ (insert_rotations_log_bound aug lt x t hs))

end CLRS.Chapter14.AugmentationExecution
