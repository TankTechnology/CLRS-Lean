import Mathlib

/-!
# Counted scan queue

Minimum extraction traverses an explicit queue and returns the remaining queue
without its selected minimum. Its counter counts actual candidate visits.
This is a linear scan queue, with no binary-heap logarithmic bound claimed.
-/

noncomputable section
namespace CLRS.Chapter24.JohnsonExecution

/-- Scan a list queue, returning its minimum and the remaining queue.
Each nonempty recursive frame records one actual candidate visit. -/
def extractMin (d : α → WithTop ℝ) : List α → Option (α × List α) × Nat
  | [] => (none, 0)
  | x :: xs =>
      let tail := extractMin d xs
      match tail.1 with
      | none => (some (x, []), tail.2 + 1)
      | some (y, ys) =>
          if d x ≤ d y then (some (x, xs), tail.2 + 1)
          else (some (y, x :: ys), tail.2 + 1)

@[simp] theorem extractMin_visits (d : α → WithTop ℝ) (xs : List α) :
    (extractMin d xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [extractMin]
    split
    · simp [ih]
    · split <;> simp [ih]

@[simp] theorem extractMin_none (d : α → WithTop ℝ) (xs : List α) :
    (extractMin d xs).1 = none ↔ xs = [] := by
  cases xs with
  | nil => simp [extractMin]
  | cons x xs =>
    simp only [extractMin]
    split
    · simp
    · split <;> simp

theorem extractMin_spec (d : α → WithTop ℝ) (xs : List α) {u rest}
    (h : (extractMin d xs).1 = some (u, rest)) :
    xs.Perm (u :: rest) ∧ ∀ v ∈ xs, d u ≤ d v := by
  induction xs generalizing u rest with
  | nil => simp [extractMin] at h
  | cons x xs ih =>
    simp only [extractMin] at h
    split at h
    · rename_i ht
      have he := (extractMin_none d xs).mp ht
      subst xs
      have he : (x, []) = (u, rest) := Option.some.inj h
      cases he
      exact ⟨.refl _, by simp⟩
    · rename_i y ys ht
      obtain ⟨hp, hm⟩ := ih ht
      split at h
      · rename_i hxy
        have he : (x, xs) = (u, rest) := Option.some.inj h
        cases he
        refine ⟨.refl _, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact le_rfl
        · exact le_trans hxy (hm v hv)
      · rename_i hxy
        have he : (y, x :: ys) = (u, rest) := Option.some.inj h
        cases he
        refine ⟨(List.Perm.cons x hp).trans (.swap u x ys), ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact le_of_lt (lt_of_not_ge hxy)
        · exact hm v hv

/-- Build the explicit unsettled queue, counting each enumerated vertex. -/
def initialQueue (s : Fin n) : (k : Nat) → k ≤ n → List (Fin n) × Nat
  | 0, _ => ([], 0)
  | k + 1, hk =>
      let rest := initialQueue s k (by omega)
      let v : Fin n := ⟨k, by omega⟩
      (if v = s then rest.1 else v :: rest.1, rest.2 + 1)

@[simp] theorem initialQueue_visits (s : Fin n) (k : Nat) (hk : k ≤ n) :
    (initialQueue s k hk).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [initialQueue, ih]

theorem initialQueue_mem (s : Fin n) (k : Nat) (hk : k ≤ n) (v : Fin n) :
    v ∈ (initialQueue s k hk).1 ↔ v.val < k ∧ v ≠ s := by
  induction k with
  | zero => simp [initialQueue]
  | succ k ih =>
    simp only [initialQueue]
    split
    · rename_i he
      rw [ih]
      constructor
      · intro h; exact ⟨by omega, h.2⟩
      · rintro ⟨hv, hvs⟩
        refine ⟨?_, hvs⟩
        have hne : v.val ≠ k := by
          intro heq
          apply hvs
          exact (Fin.ext heq).trans he
        omega
    · rename_i he
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hv, hvs⟩)
        · exact ⟨by simp, he⟩
        · exact ⟨by omega, hvs⟩
      · rintro ⟨hv, hvs⟩
        by_cases heq : v.val = k
        · left; exact Fin.ext heq
        · right; exact ⟨by omega, hvs⟩

theorem initialQueue_nodup (s : Fin n) (k : Nat) (hk : k ≤ n) :
    (initialQueue s k hk).1.Nodup := by
  induction k with
  | zero => simp [initialQueue]
  | succ k ih =>
    simp only [initialQueue]
    split
    · exact ih _
    · rw [List.nodup_cons]
      exact ⟨by simp [initialQueue_mem], ih _⟩

theorem initialQueue_length_le (s : Fin n) (k : Nat) (hk : k ≤ n) :
    (initialQueue s k hk).1.length ≤ k := by
  induction k with
  | zero => simp [initialQueue]
  | succ k ih =>
    have hh := ih (by omega)
    simp only [initialQueue]
    split
    · exact Nat.le_trans hh (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ hh

end CLRS.Chapter24.JohnsonExecution
