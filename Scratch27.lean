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
  -- Rows a (≠ x): the `b ≠ x` columns are invariant (before_moveToFront_iff), and the
  -- `b = x` column is dropped because nothing precedes the moved front element.
  have hfilter :
      (moveToFront x L).toFinset.filter
          (fun b => before a b (moveToFront x L) ∧ before b a M) =
        (L.toFinset.erase x).filter (fun b => before a b L ∧ before b a M) := by
    rw [toFinset_moveToFront hx]
    ext b
    simp only [Finset.mem_filter]
    by_cases hbx : b = x
    · subst b
      simp [not_before_x_front]
    · simp [hbx, before_moveToFront_iff hax hbx hx]
  rw [hfilter]
  -- The erased column contributes exactly the `(a, x)` entry back.
  have hxS : x ∈ L.toFinset := by simpa using hx
  have hsplit :
      (L.toFinset.filter (fun b => before a b L ∧ before b a M)).card =
        ((L.toFinset.erase x).filter (fun b => before a b L ∧ before b a M)).card +
          (if before a x L ∧ before x a M then 1 else 0) := by
    by_cases hP : before a x L ∧ before x a M
    · have hxfilter : x ∈ L.toFinset.filter (fun b => before a b L ∧ before b a M) := by
        simp [hP, hxS]
      have hsplit' :
          L.toFinset.filter (fun b => before a b L ∧ before b a M) =
            insert x ((L.toFinset.erase x).filter (fun b => before a b L ∧ before b a M)) := by
        ext b
        by_cases hbx : b = x
        · subst b
          simp [hP, hxS]
        · simp [hbx]
      rw [hsplit']
      rw [Finset.card_insert_of_notMem]
      · simp [hP]
      · intro hmem
        rw [Finset.mem_filter] at hmem
        simp at hmem
        exact hmem.1 rfl
    · have hsplit' :
          L.toFinset.filter (fun b => before a b L ∧ before b a M) =
            (L.toFinset.erase x).filter (fun b => before a b L ∧ before b a M) := by
        ext b
        by_cases hbx : b = x
        · subst b
          simp [hP]
        · simp [hbx]
      rw [hsplit']
      simp [hP]
  rw [hsplit]

/-- The row of `x` after move-to-front counts exactly the elements before `x` in `M`. -/
lemma invFrom_x_moveToFront {x : α} {L M : List α} (hperm : L.toFinset = M.toFinset) :
    invFrom x (moveToFront x L) M = position x M := by
  unfold invFrom position
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_filter]
  constructor
  · intro hb
    rcases hb with ⟨hb1, hb2, hb3⟩
    -- `before b x M` already forces `b ∈ M`.
    exact ⟨by simpa using before_mem_left hb3, hb3⟩
  · intro hb
    rcases hb with ⟨hb1, hb3⟩
    have hbx : x ≠ b := by
      intro hxeq
      subst b
      exact before_irrefl x M hb3
    have hbL : b ∈ L := by
      have : b ∈ M.toFinset := by simpa using (before_mem_left hb3 : b ∈ M)
      simpa [hperm] using this
    exact ⟨by simpa using mem_moveToFront_of_ne hbx hbL,
      before_x_front hbL hbx, hb3⟩

/-- The row of `x` before move-to-front misses exactly the `commonBefore` pairs: the
    elements before `x` in `M` are split by trichotomy into those also before `x` in `L`
    (the `commonBefore` pairs) and those that `x` precedes in `L` (the `invFrom` row). -/
lemma invFrom_x_eq {x : α} {L M : List α} (hperm : L.toFinset = M.toFinset)
    (hxL : x ∈ L) (hxM : x ∈ M) :
    invFrom x L M + commonBefore x L M = position x M := by
  unfold invFrom commonBefore position
  rw [← hperm]
  -- Split `position x M` over `M.toFinset` by whether each element precedes `x` in `L`.
  have hsplit :
      (L.toFinset.filter (fun b => before b x M)).card =
        (L.toFinset.filter (fun b => before b x L ∧ before b x M)).card +
          (L.toFinset.filter (fun b => ¬ before b x L ∧ before b x M)).card := by
    have hdisj : Disjoint (L.toFinset.filter (fun b => before b x L ∧ before b x M))
        (L.toFinset.filter (fun b => ¬ before b x L ∧ before b x M)) := by
      rw [Finset.disjoint_left]
      intro b hb1 hb2
      simp at hb1 hb2
      exact hb1.1 hb2.1
    have hunion : (L.toFinset.filter (fun b => before b x L ∧ before b x M)) ∪
        (L.toFinset.filter (fun b => ¬ before b x L ∧ before b x M)) =
        L.toFinset.filter (fun b => before b x M) := by
      ext b
      simp
      by_cases h : before b x L
      · simp [h]
      · simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- `¬ before b x L` is `before x b L` for the elements before `x` in `M` (trichotomy).
  have hnot :
      (L.toFinset.filter (fun b => ¬ before b x L ∧ before b x M)) =
        (L.toFinset.filter (fun b => before x b L ∧ before b x M)) := by
    ext b
    simp only [Finset.mem_filter]
    by_cases hbL : b ∈ L.toFinset
    · by_cases hbM : before b x M
      · have hb : b ∈ L := by simpa using hbL
        have hbne : b ≠ x := by
          intro hb
          subst b
          exact before_irrefl x M hbM
        have hxM' : x ∈ M := by
          have : x ∈ L.toFinset := by simpa using hxL
          simpa [hperm] using this
        have haM : b ∈ M := by
          have : b ∈ L.toFinset := by simpa using hb
          simpa [hperm] using this
        rcases before_or_before haM hxM' hbne with hm | hxm
        · simp [hm, before_asymm hm]
        · simp [hxm, before_asymm hxm]
      · simp [hbM]
    · simp [hbL]
  rw [hsplit, hnot]
  rw [Nat.add_comm]

/-- The position of `x` splits into the elements before `x` in both lists and those that
    `x` precedes in `M` — the pairs whose inversion is destroyed by move-to-front. -/
lemma position_eq_common_add_removed {x : α} {L M : List α} (hxL : x ∈ L)
    (hperm : L.toFinset = M.toFinset) :
    position x L =
      commonBefore x L M +
        (L.toFinset.filter (fun a => before a x L ∧ before x a M)).card := by
  unfold position commonBefore
  have hsplit :
      (L.toFinset.filter (fun a => before a x L)).card =
        (L.toFinset.filter (fun a => before a x L ∧ before a x M)).card +
          (L.toFinset.filter (fun a => before a x L ∧ ¬ before a x M)).card := by
    have hdisj : Disjoint (L.toFinset.filter (fun a => before a x L ∧ before a x M))
        (L.toFinset.filter (fun a => before a x L ∧ ¬ before a x M)) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      simp at ha1 ha2
      exact ha1.2 ha2.2
    have hunion : (L.toFinset.filter (fun a => before a x L ∧ before a x M)) ∪
        (L.toFinset.filter (fun a => before a x L ∧ ¬ before a x M)) =
        L.toFinset.filter (fun a => before a x L) := by
      ext a
      simp
      by_cases h : before a x M
      · simp [h]
      · simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hnot :
      (L.toFinset.filter (fun a => before a x L ∧ ¬ before a x M)) =
        (L.toFinset.filter (fun a => before a x L ∧ before x a M)) := by
    ext a
    simp only [Finset.mem_filter]
    by_cases haL : a ∈ L.toFinset
    · by_cases hax : before a x L
      · have ha : a ∈ L := by simpa using haL
        have hane : a ≠ x := by
          intro hxeq
          subst a
          exact before_irrefl x L hax
        have hxM' : x ∈ M := by
          have : x ∈ L.toFinset := by simpa using hxL
          simpa [hperm] using this
        have haM : a ∈ M := by
          have : a ∈ L.toFinset := by simpa using ha
          simpa [hperm] using this
        rcases before_or_before haM hxM' hane with hm | hxm
        · simp [hm, before_asymm hm]
        · simp [hxm, before_asymm hxm]
      · simp [hax]
    · simp [haL]
  rw [hsplit, hnot]

/--
**Phase-1 potential change.**  Moving `x` to the front of `L`, with the other list `M`
held fixed, changes the inversion distance by `2·commonBefore x L M − position x L`
(stated in the truncation-free form).  This is the engine of the move-to-front
amortized analysis: the amortized cost of the move is roughly `1 + 4·commonBefore`.
-/
lemma invDist_moveToFront_add_pos {x : α} {L M : List α} (hxL : x ∈ L) (hxM : x ∈ M)
    (hperm : L.toFinset = M.toFinset) :
    invDist (moveToFront x L) M + position x L = invDist L M + 2 * commonBefore x L M := by
  let S : Finset α := L.toFinset
  let L' : List α := moveToFront x L
  let ind : α → ℕ := fun a => (if before a x L ∧ before x a M then 1 else 0)
  let removed : ℕ := (S.filter (fun a => before a x L ∧ before x a M)).card
  let pos : ℕ := (S.filter (fun a => before a x L)).card
  have hxS : x ∈ S := by simpa [S] using hxL
  have hL'toS : L'.toFinset = S := by
    dsimp [L', S]
    exact toFinset_moveToFront hxL
  -- Row relations of the inversion matrix under move-to-front.
  have hrow_ne : ∀ a, a ≠ x →
      (S.filter (fun b => before a b L' ∧ before b a M)).card + ind a =
      (S.filter (fun b => before a b L ∧ before b a M)).card := by
    intro a ha
    have h := invFrom_ne_moveToFront (a := a) ha hxL hperm
    dsimp [ind, L', S] at h ⊢
    rw [hL'toS] at h ⊢
    exact h
  have hrow_x :
      (S.filter (fun b => before x b L' ∧ before b x M)).card =
        (S.filter (fun b => before x b L ∧ before b x M)).card + commonBefore x L M := by
    have h1 := invFrom_x_moveToFront (x := x) hperm
    have h2 := invFrom_x_eq hperm hxL hxM
    have h1' : (S.filter (fun b => before x b L' ∧ before b x M)).card = position x M := by
      dsimp [L', S] at h1 ⊢
      rw [hL'toS] at h1 ⊢
      exact h1
    have h2' : (S.filter (fun b => before x b L ∧ before b x M)).card + commonBefore x L M =
        position x M := by
      dsimp [S] at h2 ⊢
      exact h2
    rw [h1']
    exact h2'.symm
  -- `removed` collects the destroyed inversions, summed over the rows `a ≠ x`.
  have hrem : removed = (S.erase x).sum ind := by
    have hindx : ind x = 0 := by
      dsimp [ind]
      simp [before_irrefl x L]
    calc
      removed = S.sum ind := by
        dsimp [removed, ind]
        rw [Finset.sum_boole]
      _ = (S.erase x).sum ind + ind x := by
        rw [← Finset.sum_erase_add S ind hxS]
      _ = (S.erase x).sum ind := by
        rw [hindx]
  -- `position x L` splits into the destroyed inversions and the common-before pairs.
  have hpos : pos = commonBefore x L M + removed := by
    have h := position_eq_common_add_removed hxL hperm
    dsimp [pos, removed, S] at h ⊢
    exact h
  -- The row-sum identity: moving `x` to the front removes the `removed` inversions and
  -- adds `position x M` of them back (the elements before `x` in `M`).
  have hmid : invDist L' M + removed = invDist L M + commonBefore x L M := by
    let row' : α → ℕ := fun a => (S.filter (fun b => before a b L' ∧ before b a M)).card
    let row : α → ℕ := fun a => (S.filter (fun b => before a b L ∧ before b a M)).card
    calc
      invDist L' M + removed = (S.sum row') + removed := by
        congr 1
        unfold invDist
        rw [hL'toS]
        dsimp [row']
        rfl
      _ = ((S.erase x).sum row' + row' x) + (S.erase x).sum ind := by
        rw [Finset.sum_erase_add S row' hxS]
        rw [hrem]
      _ = ((S.erase x).sum row' + (S.erase x).sum ind) + row' x := by
        omega
      _ = (S.erase x).sum (fun a => row' a + ind a) + row' x := by
        rw [← Finset.sum_add_distrib]
      _ = (S.erase x).sum row + (row x + commonBefore x L M) := by
        have hcong : (S.erase x).sum (fun a => row' a + ind a) = (S.erase x).sum row := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha' : a ∈ S.erase x := ha
          have hane : a ≠ x := by
            intro hxeq
            subst a
            exact (Finset.mem_erase.mp ha').1 rfl
          exact hrow_ne a hane
        rw [hcong, hrow_x]
      _ = (S.sum row) + commonBefore x L M := by
        rw [← Finset.sum_erase_add S row hxS]
        omega
      _ = invDist L M + commonBefore x L M := by
        congr 1
        unfold invDist
        dsimp [row, S]
  -- Put the pieces together.
  have htarget : invDist L' M + pos = invDist L M + 2 * commonBefore x L M := by
    omega
  dsimp [pos, S] at htarget
  unfold position at htarget ⊢
  exact htarget

/--
**Triangle inequality for the inversion distance.**  For three lists over the same
element set, the inversion distance between the first and the third is at most the
sum of the two intermediate distances.  Phase 2 of the amortized analysis uses the
case `L₁ = L'` (MTF's new list), `L₂ = M`, `L₃ = M'` (OPT's list before and after):
OPT's rearrangement of `M` can increase the potential by at most `2 · invDist M M'`.
-/
lemma invDist_triangle {L₁ L₂ L₃ : List α} (h12 : L₁.toFinset = L₂.toFinset)
    (h23 : L₂.toFinset = L₃.toFinset) :
    invDist L₁ L₃ ≤ invDist L₁ L₂ + invDist L₂ L₃ := by
  let S : Finset α := L₁.toFinset
  let r13 : α → ℕ := fun a => (S.filter (fun b => before a b L₁ ∧ before b a L₃)).card
  let r12 : α → ℕ := fun a => (S.filter (fun b => before a b L₁ ∧ before b a L₂)).card
  let r23 : α → ℕ := fun a => (S.filter (fun b => before a b L₂ ∧ before b a L₃)).card
  have hrow_le : ∀ a ∈ S, r13 a ≤ r12 a + r23 a := by
    intro a haS
    have hsplit : r13 a =
        (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ before b a L₂)).card +
          (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ ¬ before b a L₂)).card := by
      have hdisj : Disjoint (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ before b a L₂))
          (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ ¬ before b a L₂)) := by
        rw [Finset.disjoint_left]
        intro b hb1 hb2
        simp at hb1 hb2
        exact hb1.2.2 hb2.2.2
      have hunion : (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ before b a L₂)) ∪
          (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ ¬ before b a L₂)) =
          S.filter (fun b => before a b L₁ ∧ before b a L₃) := by
        ext b
        simp
        by_cases h : before b a L₂
        · simp [h]
        · simp [h]
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have h1 : (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ before b a L₂)).card ≤ r12 a := by
      apply Finset.card_le_card
      intro b hb
      simp [r12] at hb ⊢
      exact ⟨hb.1, hb.2.1, hb.2.2.2⟩
    have h2 : (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ ¬ before b a L₂)).card ≤ r23 a := by
      apply Finset.card_le_card
      intro b hb
      simp [r23] at hb ⊢
      rcases hb with ⟨hbS, hbal1, hba3, hnb2⟩
      have hb2 : b ∈ L₂ := by
        have : b ∈ L₃ := before_mem_left hba3
        have : b ∈ L₃.toFinset := by simpa using this
        have : b ∈ L₂.toFinset := by simpa [h23] using this
        simpa using this
      have ha2 : a ∈ L₂ := by
        have : a ∈ L₁ := before_mem_right hbal1
        have : a ∈ L₁.toFinset := by simpa using this
        have : a ∈ L₂.toFinset := by simpa [h12] using this
        simpa using this
      have hbne : b ≠ a := by
        intro hba
        subst b
        exact before_irrefl a L₃ hba3
      rcases before_or_before hb2 ha2 hbne with hba2 | hab2
      · exact (hnb2 hba2).elim
      · exact ⟨hbS, hab2, hba3⟩
    calc
      r13 a = (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ before b a L₂)).card +
          (S.filter (fun b => before a b L₁ ∧ before b a L₃ ∧ ¬ before b a L₂)).card := hsplit
      _ ≤ r12 a + r23 a := Nat.add_le_add h1 h2
  calc
    invDist L₁ L₃ = S.sum r13 := by
      unfold invDist
      dsimp [S]
    _ ≤ S.sum (fun a => r12 a + r23 a) := by
      exact Finset.sum_le_sum hrow_le
    _ = S.sum r12 + S.sum r23 := by
      rw [Finset.sum_add_distrib]
    _ = invDist L₁ L₂ + invDist L₂ L₃ := by
      congr 1
      · unfold invDist
        dsimp [r12, S]
      · unfold invDist
        dsimp [r23, S]
        rw [h12]

/--
**MOVE-TO-FRONT is 4-competitive, per request (amortized).**  For a request `x`, with
MTF's list `L` and OPT's list `M` permutations of the same set, after MTF moves `x`
to the front (list `moveToFront x L`) and OPT moves to `M'`, the amortized cost of
MTF's move — its actual cost plus the change in the potential `2 · invDist` — is at
most `4` times OPT's cost for the request, plus the previous potential.
-/
theorem mtf_step_four_competitive (x : α) (L M M' : List α)
    (hxL : x ∈ L) (hxM : x ∈ M) (hperm : L.toFinset = M.toFinset)
    (hperm' : (moveToFront x L).toFinset = M'.toFinset) :
    mtfCost x L + 2 * invDist (moveToFront x L) M' ≤
      4 * strategyCost x M M' + 2 * invDist L M := by
  have hL' : (moveToFront x L).toFinset = L.toFinset := toFinset_moveToFront hxL
  have htri := invDist_triangle (L₁ := moveToFront x L) (L₂ := M) (L₃ := M')
    (hL'.trans hperm) hperm'
  calc
    mtfCost x L + 2 * invDist (moveToFront x L) M' ≤
        2 * position x L + 1 + 2 * invDist (moveToFront x L) M + 2 * invDist M M' := by
      unfold mtfCost
      nlinarith [htri]
    _ = 1 + 2 * invDist L M + 4 * commonBefore x L M + 2 * invDist M M' := by
      have h1 := invDist_moveToFront_add_pos hxL hxM hperm
      nlinarith [h1]
    _ ≤ 4 * (position x M + 1 + invDist M M') + 2 * invDist L M := by
      have hC := commonBefore_le_position (x := x) (L := L) (M := M) hperm
      nlinarith [hC, Nat.zero_le (invDist M M')]
    _ = 4 * strategyCost x M M' + 2 * invDist L M := by
      unfold strategyCost scanCost
      ring

/-- Move-to-front of an element of `L` preserves membership of every element of `L`. -/
lemma mem_moveToFront_all {x : α} {L : List α} : ∀ y ∈ L, y ∈ moveToFront x L := by
  intro y hy
  by_cases hxy : x = y
  · subst y
    exact mem_moveToFront x L
  · exact mem_moveToFront_of_ne hxy hy

/--
**MOVE-TO-FRONT is 4-competitive over a request sequence.**  Against any list-update
strategy `A` that keeps its list a permutation of the initial set, running MOVE-TO-FRONT
from the same initial list `L` costs at most `4` times the strategy's cost plus the
initial potential `2 · invDist L L = 0` (the additive term is zero when both start
from the same list).  This is Theorem 27.2 in CLRS §27.2.
-/
theorem mtf_four_competitive (A : Strategy α) (σ L M : List α)
    (hperm : L.toFinset = M.toFinset)
    (hreq : ∀ x ∈ σ, x ∈ L)
    (hA : ∀ L x, x ∈ L → (A L x).toFinset = L.toFinset) :
    mtfTotalCost σ L ≤ 4 * strategyTotalCost A σ M + 2 * invDist L M := by
  induction σ generalizing L M with
  | nil =>
      intro hperm hreq hA
      simp [mtfTotalCost, strategyTotalCost]
  | cons x σ' ih =>
      intro hperm hreq hA
      have hxL : x ∈ L := hreq x (by simp)
      have hxM : x ∈ M := by
        have : x ∈ L.toFinset := by simpa using hxL
        have : x ∈ M.toFinset := by simpa [hperm] using this
        simpa using this
      let L' : List α := moveToFront x L
      let M' : List α := A M x
      have hperm' : L'.toFinset = M'.toFinset := by
        dsimp [L', M']
        rw [toFinset_moveToFront hxL, hA M x hxM]
        exact hperm
      have hreq' : ∀ y ∈ σ', y ∈ L' := by
        intro y hy
        have hyL : y ∈ L := hreq y (by simp [hy])
        simpa [L'] using mem_moveToFront_all hyL
      have hstep := mtf_step_four_competitive x L M M' hxL hxM hperm (by simpa [L'] using hperm')
      have hrec := ih L' M' hperm' hreq' hA
      have hcombo : mtfCost x L + mtfTotalCost σ' L' ≤
          4 * strategyCost x M M' + 4 * strategyTotalCost A σ' M' + 2 * invDist L M := by
        nlinarith [hstep, hrec]
      unfold mtfTotalCost strategyTotalCost
      dsimp [L', M']
      nlinarith [hcombo]

/-- Inversion distance between a list and itself is zero. -/
lemma invDist_self_zero (L : List α) : invDist L L = 0 := by
  unfold invDist
  simp [before_irrefl]

end SearchList

end CLRS

#print axioms CLRS.SearchList.mtf_four_competitive
#print axioms CLRS.SearchList.mtf_step_four_competitive
