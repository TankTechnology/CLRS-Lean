import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CLRS

namespace SearchList

variable {α : Type} [DecidableEq α]

/-- `a` is strictly before `b` in the list `L` (both elements present). -/
def before (a b : α) (L : List α) : Prop :=
  b ∈ L ∧ a ∈ L.takeWhile (fun c => decide (c ≠ b))

instance before_decidable (a b : α) (L : List α) : Decidable (before a b L) :=
  inferInstanceAs (Decidable (b ∈ L ∧ a ∈ L.takeWhile (fun c => decide (c ≠ b))))

/-- 0-based position of `x` in `L`: the number of elements strictly before it. -/
def position (x : α) (L : List α) : ℕ :=
  (L.toFinset.filter (fun y => before y x L)).card

/-- Inversion distance: the number of unordered element pairs whose relative order
    differs between the two lists.  Equivalently, the minimum number of adjacent
    swaps needed to reorder one list into the other. -/
def invDist (L₁ L₂ : List α) : ℕ :=
  (L₁.toFinset.sum fun a =>
    (L₁.toFinset.filter (fun b => before a b L₁ ∧ before b a L₂)).card)

/-- The cost of servicing one request `x` by scanning from the front: the
    1-based position. -/
def scanCost (x : α) (L : List α) : ℕ := position x L + 1

/-- The cost of servicing one request `x` with MOVE-TO-FRONT: scanning to the
    position and then swapping `x` to the front (`2·position + 1`). -/
def mtfCost (x : α) (L : List α) : ℕ := 2 * position x L + 1

/-- Move-to-front: after accessing `x`, bring it to the front of the list. -/
def moveToFront (x : α) (L : List α) : List α := x :: L.erase x

/-- A list-update strategy: given the current list and the request, the next list. -/
abbrev Strategy (α : Type) [DecidableEq α] := List α → α → List α

/-- Potential function: twice the inversion distance between the two lists. -/
def potential (L₁ L₂ : List α) : ℕ := 2 * invDist L₁ L₂

/-- Cost of a general strategy processing request `x` from list `L` to list `L'`:
    the scan cost plus the inversion distance of the rearrangement. -/
def strategyCost (x : α) (L L' : List α) : ℕ := scanCost x L + invDist L L'

/-- Total cost of MOVE-TO-FRONT over a request sequence. -/
def mtfTotalCost : List α → List α → ℕ
  | [], _ => 0
  | x :: σ, L => mtfCost x L + mtfTotalCost σ (moveToFront x L)

/-- Total cost of a strategy over a request sequence. -/
def strategyTotalCost (A : Strategy α) : List α → List α → ℕ
  | [], _ => 0
  | x :: σ, L => strategyCost x L (A L x) + strategyTotalCost A σ (A L x)

/-- Final list after running MOVE-TO-FRONT over a request sequence. -/
def mtfRun : List α → List α → List α
  | [], L => L
  | x :: σ, L => mtfRun σ (moveToFront x L)

/-- Final list after running a strategy over a request sequence. -/
def strategyRun (A : Strategy α) : List α → List α → List α
  | [], L => L
  | x :: σ, L => strategyRun A σ (A L x)

-- ========== basic lemmas about `before` ==========

/-- Recursion rule for `before`. -/
lemma before_cons (a b x : α) (L : List α) :
    before a b (x :: L) ↔ x ≠ b ∧ b ∈ L ∧ (a = x ∨ before a b L) := by
  constructor
  · intro h
    rcases h with ⟨hb, ha⟩
    have hxb : x ≠ b := by
      intro hx
      subst x
      simp [before] at ha
    have hbL : b ∈ L := by
      rcases (List.mem_cons.mp hb) with hb' | hb''
      · exact (hxb hb'.symm).elim
      · exact hb''
    have hxneq : decide (x ≠ b) = true := decide_eq_true hxb
    refine ⟨hxb, hbL, ?_⟩
    · unfold List.takeWhile at ha
      rw [hxneq] at ha
      rw [List.mem_cons] at ha
      rcases ha with ha | hat
      · exact Or.inl ha
      · exact Or.inr ⟨hbL, hat⟩
  · intro h
    rcases h with ⟨hxb, hbL, hdisj⟩
    have hxneq : decide (x ≠ b) = true := decide_eq_true hxb
    have hbcons : b ∈ x :: L := by
      rw [List.mem_cons]
      exact Or.inr hbL
    rcases hdisj with ha | hab
    · subst a
      unfold before
      constructor
      · exact hbcons
      · unfold List.takeWhile
        rw [hxneq]
        exact (List.mem_cons_self : x ∈ x :: (L.takeWhile (fun c => decide (c ≠ b))))
    · unfold before
      constructor
      · exact hbcons
      · unfold List.takeWhile
        rw [hxneq]
        rw [List.mem_cons]
        exact Or.inr hab.2

/-- `before` is irreflexive. -/
lemma before_irrefl (a : α) (L : List α) : ¬ before a a L := by
  induction L with
  | nil => simp [before]
  | cons x rest ih =>
      intro h
      rw [before_cons] at h
      rcases h with ⟨hxa, ha, hdisj⟩
      rcases hdisj with heq | hrest
      · exact hxa heq.symm
      · exact ih hrest

/-- `before` implies both elements are present. -/
lemma before_mem_left {a b : α} {L : List α} (h : before a b L) : a ∈ L := by
  induction L with
  | nil => simp [before] at h
  | cons x rest ih =>
      rw [before_cons] at h
      rcases h with ⟨hxb, hb, hdisj⟩
      rcases hdisj with heq | hrest
      · simp [heq]
      · exact List.mem_cons_of_mem x (ih hrest)

/-- `before` is asymmetric. -/
lemma before_asymm {a b : α} {L : List α} (h : before a b L) : ¬ before b a L := by
  induction L with
  | nil => simp [before] at h
  | cons x rest ih =>
      intro hba
      rw [before_cons] at h hba
      rcases h with ⟨hxb, hb, hdisj⟩
      rcases hba with ⟨hxa, ha, hdisj'⟩
      rcases hdisj with heq | hab
      · subst a
        exact hxa rfl
      · rcases hdisj' with heq' | hba'
        · subst b
          exact hxb rfl
        · exact ih hab hba'

/-- `before` implies the second element is present. -/
lemma before_mem_right {a b : α} {L : List α} (h : before a b L) : b ∈ L := h.1

/-- For distinct elements of a list, exactly one of `before a b L` or `before b a L`
    holds (trichotomy): scanning from the front, whichever of `a`, `b` comes first is
    the one that is `before` the other. -/
lemma before_or_before {a b : α} {L : List α} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    before a b L ∨ before b a L := by
  induction L with
  | nil => simp [before] at ha
  | cons x rest ih =>
      by_cases hxa : x = a
      · subst a
        left
        simp [before, hb, hab]
      · by_cases hxb : x = b
        · subst b
          right
          simp [before, ha, hab]
        · have ha' : a ∈ rest := by
            simp [hxa, hxb, ha]
          have hb' : b ∈ rest := by
            simp [hxa, hxb, hb]
          rcases ih ha' hb' hab with hab' | hba'
          · left
            simp [before, hxa, hxb] at hab' ⊢
            exact hab'
          · right
            simp [before, hxa, hxb] at hba' ⊢
            exact hba'

/-- Consequence of trichotomy: if `b` is not before `a`, then `a` is before `b`. -/
lemma before_of_not_before {a b : α} {L : List α} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b)
    (hn : ¬ before b a L) : before a b L := by
  rcases before_or_before ha hb hab with h | h
  · exact h
  · exact (hn h).elim

/-- `a ∈ L.takeWhile (· ≠ b)` is unchanged by erasing an element `x` that is neither
    `a` nor `b`. -/
lemma mem_takeWhile_ne_erase (b x : α) (L : List α) {a : α} (hax : a ≠ x) (hbx : b ≠ x) :
    a ∈ (L.erase x).takeWhile (fun c => decide (c ≠ b)) ↔
      a ∈ L.takeWhile (fun c => decide (c ≠ b)) := by
  induction L with
  | nil => simp
  | cons y rest ih =>
      by_cases hya : a = y
      · subst a
        -- a is the head; both sides are true unless y == b, in which case both false.
        by_cases hyb : y = b
        · subst b
          simp [hyb, hbx]  -- hbx gives x ≠ y; takeWhile = [] on both sides
        · simp [hyb]  -- y :: rest, a = y ∈ it on both sides
      · by_cases hyx : y = x
        · subst x
          -- (y :: rest).erase y = rest
          simp [hyx, hya, hbx]
        · by_cases hyb : y = b
          · subst b
            simp [hyb]
          · simp [hya, hyx, hyb, ih]

/-- `before` is invariant under move-to-front of an element distinct from both. -/
lemma before_moveToFront_iff {a x b : α} {L : List α} (hax : a ≠ x) (hbx : b ≠ x) (hx : x ∈ L) :
    before a b (moveToFront x L) ↔ before a b L := by
  unfold moveToFront
  -- before a b (x :: L.erase x) ↔ before a b L
  have hb' : b ∈ x :: L.erase x ↔ b ∈ L.erase x := by simp [hbx]
  have htw : a ∈ (x :: L.erase x).takeWhile (fun c => decide (c ≠ b)) ↔
      a ∈ (L.erase x).takeWhile (fun c => decide (c ≠ b)) := by
    simp [hbx, hax]
  rw [before]
  rw [hb', htw]
  rw [mem_takeWhile_ne_erase b x L hax hbx]
  rfl

/-- After moving `x` to the front, `x` is before every other element of the list. -/
lemma before_x_front {x b : α} {L : List α} (hb : b ∈ L) (hxb : x ≠ b) :
    before x b (moveToFront x L) := by
  unfold moveToFront
  simp [before, hb, hxb]

/-- Nothing is before the element moved to the front. -/
lemma not_before_x_front {x b : α} (L : List α) : ¬ before b x (moveToFront x L) := by
  unfold moveToFront
  simp [before]

/-- The element set of a list is unchanged by moving an element of the list to the
    front. -/
lemma toFinset_moveToFront {x : α} {L : List α} (hx : x ∈ L) :
    (moveToFront x L).toFinset = L.toFinset := by
  unfold moveToFront
  rw [List.toFinset_cons]
  simp [hx]

/-- The moved element is at the front after move-to-front. -/
lemma mem_moveToFront (x : α) (L : List α) : x ∈ moveToFront x L := by
  unfold moveToFront
  simp

/-- Move-to-front of an element already in the list preserves membership of every
    other element. -/
lemma mem_moveToFront_of_ne {x y : α} {L : List α} (hxy : x ≠ y) (hy : y ∈ L) :
    y ∈ moveToFront x L := by
  unfold moveToFront
  simp [hxy, hy]

/-- The position of the moved element after move-to-front is zero. -/
lemma position_moveToFront (x : α) (L : List α) : position x (moveToFront x L) = 0 := by
  unfold position
  simp [not_before_x_front]

/-- `position` is the number of elements of `L` strictly before `x`. -/
lemma position_eq_card {x : α} {L : List α} :
    position x L = (L.toFinset.filter (fun y => before y x L)).card := rfl

/-- Elements before `x` in both lists: the inversion pairs newly created or destroyed
    when move-to-front brings `x` forward. -/
def commonBefore (x : α) (L M : List α) : ℕ :=
  (L.toFinset.filter (fun y => before y x L ∧ before y x M)).card

/-- The number of elements before `x` in both lists is at most the number before it in
    the second. -/
lemma commonBefore_le_position {x : α} {L M : List α} (hperm : L.toFinset = M.toFinset) :
    commonBefore x L M ≤ position x M := by
  unfold commonBefore position
  rw [← hperm]
  apply Finset.card_le_card
  intro y hy
  simp at hy ⊢
  exact hy.1.2

/-- Number of pairs `(a, b)` from `L₁` (with `b ≠ a`) such that `a` is before `b` in
    `L₁` and `b` before `a` in `L₂`: the row of `a` in the inversion matrix. -/
def invFrom (a : α) (L₁ L₂ : List α) : ℕ :=
  (L₁.toFinset.filter (fun b => before a b L₁ ∧ before b a L₂)).card

/-- `invDist` is the sum of its rows. -/
lemma invDist_eq_sum_invFrom (L₁ L₂ : List α) :
    invDist L₁ L₂ = ∑ a ∈ L₁.toFinset, invFrom a L₁ L₂ := rfl

/-- The row of `a` does not change under move-to-front of `x ≠ a`, except that the
    `b = x` entry disappears (as `x` is now at the front). -/
lemma invFrom_ne_moveToFront {a x : α} {L M : List α} (hax : a ≠ x) (hx : x ∈ L)
    (hperm : L.toFinset = M.toFinset) :
    invFrom a (moveToFront x L) M + (if before a x L ∧ before x a M then 1 else 0) =
      invFrom a L M := by
  unfold invFrom
  -- Rows a (≠ x): the b ≠ x entries are invariant; b = x is counted in L but not L'.
  rw [← hperm]
  have hmem : a ∈ L.toFinset := by
    -- a is in the set only if a ∈ L; but we need a ∈ L to apply before lemmas
    sorry

/-- The row of `x` after move-to-front counts exactly the elements before `x` in `M`. -/
lemma invFrom_x_moveToFront {x : α} {L M : List α} (hperm : L.toFinset = M.toFinset) :
    invFrom x (moveToFront x L) M = position x M := by
  unfold invFrom position
  rw [← hperm]
  apply Finset.card_congr
  · intro b hb
    exact hb
  · intro b hb
    -- before x b (moveToFront x L) ∧ before b x M
    have hmem : b ∈ M.toFinset := by
      simpa [← hperm] using hb
    sorry

/-- The row of `x` before move-to-front misses exactly the `commonBefore` pairs. -/
lemma invFrom_x_eq {x : α} {L M : List α} (hxL : x ∈ L) (hxM : x ∈ M) :
    invFrom x L M + commonBefore x L M = position x M := by
  unfold invFrom commonBefore position
  sorry

/-- Inversion distance between a list and itself is zero. -/
lemma invDist_self_zero (L : List α) : invDist L L = 0 := by
  unfold invDist
  simp [before_irrefl]

end SearchList

end CLRS
