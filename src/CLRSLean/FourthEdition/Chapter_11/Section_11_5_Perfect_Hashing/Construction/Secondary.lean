import CLRSLean.FourthEdition.Chapter_11.Section_11_5_Perfect_Hashing

/-!
# Executed finite secondary perfect-hash construction

Every candidate runs a collision check, initializes its secondary slot array,
and places its local key indices. The returned ledger counts hash evaluations,
equality comparisons, slot initialization, and indexed writes. Supplied finite
traces stop on success; exhaustion executes a deterministic injective fallback.
Thus the actual attempts equal the existing {lit}`failedTrials + 1` statistic.

Hashes act on local indices {lit}`Fin n`. Hash-family sampling and representation
costs are outside this indexed-operation model. The finite expectation concerns
uniform full assignments, and is not a theorem about an unbounded retry process.
-/

namespace CLRS.Chapter11.PerfectConstruction

/-- Hash equality tests, charged for two hash evaluations and one comparison. -/
def differsFrom (a : α → β) [DecidableEq β] (x : α) : List α → Bool × Nat
  | [] => (true, 0)
  | y :: ys =>
      if a x = a y then (false, 3)
      else let rest := differsFrom a x ys; (rest.1, rest.2 + 3)

theorem differsFrom_correct (a : α → β) [DecidableEq β] (x : α) (xs : List α) :
    (differsFrom a x xs).1 = true ↔ ∀ y ∈ xs, a x ≠ a y := by
  induction xs with
  | nil => simp [differsFrom]
  | cons y ys ih => by_cases h : a x = a y <;> simp [differsFrom, h, ih]

theorem differsFrom_work_le (a : α → β) [DecidableEq β] (x : α) (xs : List α) :
    (differsFrom a x xs).2 ≤ 3 * xs.length := by
  induction xs with
  | nil => simp [differsFrom]
  | cons y ys ih => simp only [differsFrom]; split <;> simp_all; omega

/-- Check all distinct input positions, stopping at the first duplicate hash. -/
def checkDistinct (a : α → β) [DecidableEq β] : List α → Bool × Nat
  | [] => (true, 0)
  | x :: xs =>
      let head := differsFrom a x xs
      if head.1 then
        let tail := checkDistinct a xs
        (tail.1, head.2 + tail.2)
      else (false, head.2)

theorem checkDistinct_correct (a : α → β) [DecidableEq β] (xs : List α) :
    (checkDistinct a xs).1 = true ↔ (xs.map a).Nodup := by
  induction xs with
  | nil => simp [checkDistinct]
  | cons x xs ih =>
      simp only [checkDistinct]
      split
      next h =>
        have hh := (differsFrom_correct a x xs).mp h
        simp only [List.map_cons, List.nodup_cons, List.mem_map]
        constructor
        · intro ht
          exact ⟨by rintro ⟨y, hy, he⟩; exact hh y hy he.symm, ih.mp ht⟩
        · intro ht; exact ih.mpr ht.2
      next h =>
        simp only [Bool.false_eq_true, List.map_cons, List.nodup_cons, false_iff]
        intro hn
        apply h
        apply (differsFrom_correct a x xs).mpr
        intro y hy he
        exact hn.1 (List.mem_map.mpr ⟨y, hy, he.symm⟩)

theorem checkDistinct_work_le (a : α → β) [DecidableEq β] (xs : List α) :
    (checkDistinct a xs).2 ≤ 3 * xs.length ^ 2 := by
  induction xs with
  | nil => simp [checkDistinct]
  | cons x xs ih =>
      have hh := differsFrom_work_le a x xs
      simp only [checkDistinct]
      split <;> simp only [List.length_cons] <;> nlinarith

abbrev Hash (n : Nat) := Fin n → Fin (n ^ 2)

theorem check_hash_correct {n : Nat} (a : Hash n) :
    (checkDistinct a (List.finRange n)).1 = true ↔ collisionFree a := by
  rw [checkDistinct_correct, List.nodup_map_iff_inj_on (List.nodup_finRange n)]
  simp [collisionFree]

/-- Initialize actual empty secondary slots, counting each array push. -/
def emptySlots (α : Type*) : Nat → Array (Option α) × Nat
  | 0 => (#[], 0)
  | m + 1 => let prev := emptySlots α m; (prev.1.push none, prev.2 + 1)

@[simp] theorem emptySlots_array (α : Type*) (m : Nat) :
    (emptySlots α m).1 = Array.replicate m none := by
  induction m with
  | zero => simp [emptySlots]
  | succ m ih => simp [emptySlots, ih, Array.replicate_succ]

@[simp] theorem emptySlots_work (α : Type*) (m : Nat) : (emptySlots α m).2 = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [emptySlots, ih]

/-- Place each key in its selected slot. A step charges a hash evaluation and
an indexed write; initialization and collision checks are counted separately. -/
def place {n : Nat} (a : Hash n) : List (Fin n) → Array (Option (Fin n)) →
    Array (Option (Fin n)) × Nat
  | [], out => (out, 0)
  | i :: is, out =>
      let rest := place a is out
      (rest.1.setIfInBounds (a i).val (some i), rest.2 + 2)

@[simp] theorem place_size {n : Nat} (a : Hash n) (xs : List (Fin n)) (out : Array (Option (Fin n))) :
    (place a xs out).1.size = out.size := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [place, ih]

@[simp] theorem place_work {n : Nat} (a : Hash n) (xs : List (Fin n)) (out : Array (Option (Fin n))) :
    (place a xs out).2 = 2 * xs.length := by
  induction xs with
  | nil => simp [place]
  | cons i xs ih => simp [place, ih]; omega

/-- Each slot contains the first input key assigned there, or its initial value. -/
theorem place_get {n : Nat} (a : Hash n) (xs : List (Fin n))
    (out : Array (Option (Fin n))) (s : Nat) (hs : s < out.size) :
    (place a xs out).1[s]'(by simpa using hs) =
      (xs.find? (fun i => (a i).val == s)).orElse (fun _ => out[s]) := by
  induction xs with
  | nil => simp [place]
  | cons i xs ih =>
      simp only [place]
      rw [Array.getElem_setIfInBounds (by simpa using hs)]
      by_cases he : (a i).val = s <;> simp [he, List.find?, ih, Bool.beq_eq_decide_eq]

structure Attempt (n : Nat) where
  hash : Hash n
  slots : Array (Option (Fin n))
  success : Bool
  work : Nat

/-- An actual collision check followed by secondary-array placement. -/
def attempt {n : Nat} (a : Hash n) : Attempt n :=
  let checked := checkDistinct a (List.finRange n)
  let initial := emptySlots (Fin n) (n ^ 2)
  let filled := place a (List.finRange n) initial.1
  ⟨a, filled.1, checked.1, checked.2 + initial.2 + filled.2⟩

@[simp] theorem attempt_hash {n : Nat} (a : Hash n) : (attempt a).hash = a := rfl
@[simp] theorem attempt_size {n : Nat} (a : Hash n) : (attempt a).slots.size = n ^ 2 := by
  simp [attempt]

@[simp] theorem attempt_success {n : Nat} (a : Hash n) :
    (attempt a).success = true ↔ collisionFree a := check_hash_correct a

theorem attempt_work_le {n : Nat} (a : Hash n) : (attempt a).work ≤ 6 * n ^ 2 := by
  have h := checkDistinct_work_le a (List.finRange n)
  have hn : n ≤ n ^ 2 := by nlinarith
  simpa only [attempt, emptySlots_work, place_work, List.length_finRange] using
    (show (checkDistinct a (List.finRange n)).2 + n ^ 2 + 2 * n ≤ 6 * n ^ 2 by
      simp only [List.length_finRange] at h
      nlinarith)

theorem attempt_get {n : Nat} (a : Hash n) (s : Nat) (hs : s < n ^ 2) :
    (attempt a).slots[s]'(by simpa using hs) =
      (List.finRange n).find? (fun i => (a i).val == s) := by
  have h := place_get a (List.finRange n) (emptySlots (Fin n) (n ^ 2)).1 s (by simpa using hs)
  simpa [attempt] using h

theorem attempt_stores {n : Nat} (a : Hash n) (ha : collisionFree a) (i : Fin n) :
    (attempt a).slots[(a i).val]'(by simp) = some i := by
  rw [attempt_get a _ (a i).isLt]
  cases h : (List.finRange n).find? (fun j => (a j).val == (a i).val) with
  | none =>
      have hh := List.find?_eq_none.mp h i (by simp)
      simp at hh
  | some j =>
      have hh := List.find?_some h
      have he : a j = a i := Fin.ext (by simpa using hh)
      rw [ha j i he]

/-- The terminal assignment is explicitly injective, including the empty domain. -/
def fallback (n : Nat) : Hash n := fun i =>
  ⟨i.val, lt_of_lt_of_le i.isLt (by nlinarith : n ≤ n ^ 2)⟩

theorem fallback_injective (n : Nat) : collisionFree (fallback n) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (n ^ 2) => x.val) hij)

structure Build (n : Nat) where
  selected : Attempt n
  attempts : Nat
  work : Nat

/-- Try supplied candidates in order; after their exhaustion execute one
explicit injective fallback. Every returned table therefore succeeds. -/
def build {n : Nat} : List (Hash n) → Build n
  | [] => let final := attempt (fallback n); ⟨final, 1, final.work⟩
  | a :: as =>
      let trial := attempt a
      if trial.success then ⟨trial, 1, trial.work⟩
      else let rest := build as; ⟨rest.selected, rest.attempts + 1, trial.work + rest.work⟩

theorem build_success {n : Nat} (as : List (Hash n)) : (build as).selected.success = true := by
  induction as with
  | nil => simpa [build] using (attempt_success (fallback n)).mpr (fallback_injective n)
  | cons a as ih =>
      simp only [build]
      split
      · assumption
      · exact ih

theorem build_work_le {n : Nat} (as : List (Hash n)) :
    (build as).work ≤ 6 * n ^ 2 * (build as).attempts := by
  induction as with
  | nil => simpa [build] using attempt_work_le (fallback n)
  | cons a as ih =>
      have h := attempt_work_le a
      simp only [build]
      split <;> simp only <;> nlinarith

def failedPrefix {n : Nat} : List (Hash n) → Nat
  | [] => 0
  | a :: as => if (attempt a).success then 0 else failedPrefix as + 1

theorem build_attempts {n : Nat} (as : List (Hash n)) :
    (build as).attempts = failedPrefix as + 1 := by
  induction as with
  | nil => simp [build, failedPrefix]
  | cons a as ih => simp only [build, failedPrefix]; split <;> simp_all


lemma failedTrials_cons {n t : Nat} (A : Fin (t + 1) → Hash n) :
    failedTrials A = if collisionFree (A 0) then 0 else
      failedTrials (fun j : Fin t => A j.succ) + 1 := by
  classical
  rw [failedTrials_eq_sum, Fin.sum_univ_succ]
  have htail (k : Fin t) :
      (∀ j : Fin (k.succ.val + 1),
        ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.succ.isLt) j))) ↔
      (¬ collisionFree (A 0) ∧ ∀ j : Fin (k.val + 1),
        ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j).succ)) := by
    rw [Fin.forall_fin_succ]
    rfl
  have hzero :
      (∀ j : Fin ((0 : Fin (t + 1)).val + 1),
        ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt (0 : Fin (t + 1)).isLt) j))) ↔
      ¬ collisionFree (A 0) := by
    constructor
    · intro hh
      exact hh 0
    · intro hh j
      have hj : Fin.castLE (Nat.succ_le_of_lt (0 : Fin (t + 1)).isLt) j = 0 := by
        apply Fin.ext
        have h := j.isLt
        change j.val < 1 at h
        change j.val = 0
        omega
      rw [hj]
      exact hh
  simp_rw [htail, hzero]
  by_cases h : collisionFree (A 0)
  · have hh : collisionFree (A 0) ↔ True := iff_true_intro h
    simp only [hh, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero,
      zero_add, ite_true]
  · simp only [h, not_false_eq_true, true_and, ite_true, ite_false]
    rw [failedTrials_eq_sum]
    omega

theorem failedPrefix_ofFn {n t : Nat} (A : Fin t → Hash n) :
    failedPrefix (List.ofFn A) = failedTrials A := by
  classical
  induction t with
  | zero => simp [List.ofFn_zero, failedPrefix, failedTrials]
  | succ t ih =>
      rw [List.ofFn_succ, failedPrefix, failedTrials_cons]
      simp only [attempt_success, ih]

def buildTrace {n : Nat} : {t : Nat} → (Fin t → Hash n) → Build n
  | 0, _ => build []
  | _ + 1, A =>
      let current := attempt (A 0)
      if current.success then ⟨current, 1, current.work⟩
      else
        let rest := buildTrace (fun j => A j.succ)
        ⟨rest.selected, rest.attempts + 1, current.work + rest.work⟩

theorem buildTrace_eq {n t : Nat} (A : Fin t → Hash n) :
    buildTrace A = build (List.ofFn A) := by
  induction t with
  | zero => simp [buildTrace]
  | succ t ih => simp [buildTrace, List.ofFn_succ, build, ih]

/-- The legacy finite trial random variable is the exact attempt count of
finite sampling followed by the terminal injective fallback. -/
theorem buildTrace_attempts {n t : Nat} (A : Fin t → Hash n) :
    (buildTrace A).attempts = trialsUntilCollisionFree A := by
  rw [buildTrace_eq, build_attempts, failedPrefix_ofFn, trialsUntilCollisionFree]

theorem buildTrace_work_le {n t : Nat} (A : Fin t → Hash n) :
    (buildTrace A).work ≤ 6 * n ^ 2 * trialsUntilCollisionFree A := by
  simpa [← buildTrace_attempts A, buildTrace_eq] using build_work_le (List.ofFn A)

open CLRS.Probability

/-- Expected measured secondary work over the stated finite SUHA trace space. -/
theorem expected_buildTrace_work_le {n t : Nat} (hn : 2 ≤ n) :
    fintypeExpect (fun A : Fin t → Hash n => ((buildTrace A).work : ℝ)) ≤
      12 * (n : ℝ) ^ 2 := by
  classical
  calc
    fintypeExpect (fun A : Fin t → Hash n => ((buildTrace A).work : ℝ)) ≤
        fintypeExpect (fun A : Fin t → Hash n =>
          6 * (n : ℝ) ^ 2 * (trialsUntilCollisionFree A : ℝ)) := by
      apply fintypeExpect_mono
      intro A
      exact_mod_cast buildTrace_work_le A
    _ = (6 * (n : ℝ) ^ 2) *
        fintypeExpect (fun A : Fin t → Hash n => (trialsUntilCollisionFree A : ℝ)) :=
      fintypeExpect_const_mul _ _
    _ ≤ (6 * (n : ℝ) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (perfectHash_expected_trials_le_two hn) (by positivity)
    _ = _ := by ring


/-- Every selected result is a real executed secondary attempt. -/
theorem build_selected_eq {n : Nat} (as : List (Hash n)) :
    (build as).selected = attempt (build as).selected.hash := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [build]; split <;> first | rfl | exact ih

theorem build_hash_injective {n : Nat} (as : List (Hash n)) :
    collisionFree (build as).selected.hash := by
  have h := build_success as
  rw [build_selected_eq] at h
  exact attempt_success _ |>.mp h

theorem attempt_only {n : Nat} (a : Hash n) (s : Nat) (i : Fin n)
    (h : (attempt a).slots[s]?.join = some i) : (a i).val = s := by
  by_cases hs : s < n ^ 2
  · have hsize : s < (attempt a).slots.size := by simpa using hs
    rw [Array.getElem?_eq_getElem hsize, Option.join_some, attempt_get a s hs] at h
    have hh := List.find?_some h
    simpa using hh
  · have hsize : ¬ s < (attempt a).slots.size := by simpa using hs
    simp [Array.getElem?_eq_none (Nat.le_of_not_gt hsize)] at h

/-- Package the constructed array as a one-bucket perfect table. All key slots
come from the returned placement execution, rather than from a specification search. -/
def tableOfBuild {n : Nat} (as : List (Hash n)) : PerfectHashTable (Fin n) 1 where
  keys := Finset.univ
  prim := fun _ => 0
  sec := fun _ i => ((build as).selected.hash i).val
  table := fun _ s => (build as).selected.slots[s]?.join
  sec_inj := by
    intro j x y hx hy hpx hpy hs
    exact build_hash_injective as x y (Fin.ext hs)
  table_stores_keys := by
    intro i hi
    rw [build_selected_eq]
    have hs := attempt_stores (build as).selected.hash (build_hash_injective as) i
    simp only [attempt_hash]
    rw [Array.getElem?_eq_getElem (by simp), Option.join_some]
    exact hs
  table_only_keys := by
    intro j s i hi
    refine ⟨by simp, Subsingleton.elim _ _, ?_⟩
    rw [build_selected_eq] at hi
    exact attempt_only _ s i hi

/-- The successful finite builder has a verified membership-query interface. -/
theorem tableOfBuild_search {n : Nat} (as : List (Hash n)) (i : Fin n) :
    perfectSearch (tableOfBuild as) i := by
  rw [perfectSearch_iff_mem]
  simp [tableOfBuild]


theorem build_work_le_small {n : Nat} (hn : n ≤ 1) (as : List (Hash n)) :
    (build as).work ≤ 6 * n ^ 2 := by
  cases as with
  | nil => simpa [build] using attempt_work_le (fallback n)
  | cons a as =>
      have hc : collisionFree a := by
        intro i j hij
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      have hs := (attempt_success a).mpr hc
      simpa only [build, hs, Bool.true_eq, ↓reduceIte] using attempt_work_le a

/-- Empty and singleton buckets are handled directly; the SUHA retry bound is
needed only for buckets with at least two keys. -/
theorem expected_buildTrace_work_le_all (n t : Nat) :
    fintypeExpect (fun A : Fin t → Hash n => ((buildTrace A).work : ℝ)) ≤
      12 * (n : ℝ) ^ 2 := by
  classical
  by_cases hn : 2 ≤ n
  · exact expected_buildTrace_work_le hn
  haveI : Nonempty (Fin t → Hash n) := ⟨fun _ => fallback n⟩
  calc
    fintypeExpect (fun A : Fin t → Hash n => ((buildTrace A).work : ℝ)) ≤
        fintypeExpect (fun _ : Fin t → Hash n => 6 * (n : ℝ) ^ 2) := by
      apply fintypeExpect_mono
      intro A
      rw [buildTrace_eq]
      exact_mod_cast build_work_le_small (by omega : n ≤ 1) (List.ofFn A)
    _ = 6 * (n : ℝ) ^ 2 := fintypeExpect_const Fintype.card_ne_zero _
    _ ≤ _ := by nlinarith [sq_nonneg (n : ℝ)]



end CLRS.Chapter11.PerfectConstruction
