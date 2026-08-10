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

end SearchList

end CLRS
