import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S1_ComputationDAG

/-!
# 26.1 S5. Spawn trees and parallel loops

Spawn/sync trees and the balanced parallel-loop model, with work, span, and
depth bounds.
-/

namespace CLRS
namespace Chapter27

/-! ## Spawn trees

The spawn/sync structure of a parallel divide-and-conquer computation.
A `spawn` node models one spawn/sync pair and contributes unit work and
unit critical-path overhead; a `seq` node is sequential composition. -/

inductive SpawnTree : Type where
  | leaf (w : ℕ) : SpawnTree
  | seq (t1 t2 : SpawnTree) : SpawnTree
  | spawn (t1 t2 : SpawnTree) : SpawnTree
deriving Repr

namespace SpawnTree

/-- The work of a spawn tree: leaf weights plus unit cost per spawn node. -/
def work : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => work t1 + work t2
  | spawn t1 t2 => work t1 + work t2 + 1

/-- The span of a spawn tree: sequential spans add; spawned children run in
parallel, so their spans take the maximum, plus unit spawn overhead. -/
def span : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => span t1 + span t2
  | spawn t1 t2 => max (span t1) (span t2) + 1

/-- T∞ ≤ T₁ for spawn trees. -/
theorem span_le_work : ∀ t : SpawnTree, t.span ≤ t.work
  | leaf w => Nat.le_refl w
  | seq t1 t2 => Nat.add_le_add (span_le_work t1) (span_le_work t2)
  | spawn t1 t2 => by
      have h1 := span_le_work t1
      have h2 := span_le_work t2
      simp only [span, work]
      omega

end SpawnTree

/-! ## Parallel loops

A parallel loop over `n` iterations is modeled as a balanced binary spawn
tree, matching the textbook's Θ(log n) overhead analysis. -/

/-- The spawn tree for a parallel loop with `n` iterations of weight `w`
each: a balanced binary spawn tree with `n` leaves. -/
def parallelLoopTree (n w : ℕ) : SpawnTree :=
  if n ≤ 1 then
    .leaf (n * w)
  else
    .spawn (parallelLoopTree (n / 2) w) (parallelLoopTree (n - n / 2) w)
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem parallelLoopTree_of_le_one {n w : ℕ} (hn : n ≤ 1) :
    parallelLoopTree n w = .leaf (n * w) := by
  rw [parallelLoopTree]
  simp [hn]

theorem parallelLoopTree_unfold {n w : ℕ} (hn : 2 ≤ n) :
    parallelLoopTree n w =
      .spawn (parallelLoopTree (n / 2) w) (parallelLoopTree (n - n / 2) w) := by
  rw [parallelLoopTree]
  simp [show ¬n ≤ 1 by omega]

/-- The work of a parallel loop: `n` iterations of weight `w` plus one unit
per internal spawn node (`n - 1` of them). -/
theorem parallelLoop_work {n : ℕ} (hn : 1 ≤ n) (w : ℕ) :
    (parallelLoopTree n w).work + 1 = n * w + n := by
  revert hn w
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn w
      by_cases h1 : n ≤ 1
      · have : n = 1 := by omega
        subst this
        simp [parallelLoopTree_of_le_one, SpawnTree.work]
      · rw [parallelLoopTree_unfold (by omega), SpawnTree.work]
        have h1 := ih (n / 2) (by omega) (by omega) w
        have h2 := ih (n - n / 2) (by omega) (by omega) w
        have hsum : n / 2 * w + (n - n / 2) * w = n * w := by
          rw [← Nat.add_mul]
          congr 1
          omega
        omega

/-- The spawn depth of the balanced parallel-loop tree: `0` for `n ≤ 1`,
else one more than the deeper of the two halves. -/
def parallelLoopDepth (n : ℕ) : ℕ :=
  if n ≤ 1 then
    0
  else
    max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) + 1
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem parallelLoopDepth_of_le_one {n : ℕ} (hn : n ≤ 1) :
    parallelLoopDepth n = 0 := by
  rw [parallelLoopDepth]
  simp [hn]

theorem parallelLoopDepth_unfold {n : ℕ} (hn : 2 ≤ n) :
    parallelLoopDepth n =
      max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) + 1 := by
  rw [parallelLoopDepth]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span of the parallel-loop tree: one iteration's weight plus the
balanced halving depth. -/
theorem parallelLoop_span (n w : ℕ) :
    (parallelLoopTree n w).span =
      if n ≤ 1 then n * w else w + parallelLoopDepth n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [parallelLoopTree_of_le_one hn, if_pos hn]
        rfl
      · rw [parallelLoopTree_unfold (by omega), if_neg hn, SpawnTree.span,
          parallelLoopDepth_unfold (by omega)]
        rw [ih (n / 2) (by omega), ih (n - n / 2) (by omega)]
        by_cases h1 : n / 2 ≤ 1 <;> by_cases h2 : n - n / 2 ≤ 1
        · rw [if_pos h1, if_pos h2, parallelLoopDepth_of_le_one h1,
            parallelLoopDepth_of_le_one h2]
          have e1 : n / 2 * w = w := by
            have : n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          have e2 : (n - n / 2) * w = w := by
            have : n - n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e1, e2]
          simp
        · rw [if_pos h1, if_neg h2, parallelLoopDepth_of_le_one h1]
          have e1 : n / 2 * w = w := by
            have : n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e1]
          omega
        · rw [if_neg h1, if_pos h2, parallelLoopDepth_of_le_one h2]
          have e2 : (n - n / 2) * w = w := by
            have : n - n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e2]
          omega
        · rw [if_neg h1, if_neg h2]
          omega

/-- The depth is logarithmic: `n ≤ 2 ^ depth`. -/
theorem parallelLoopDepth_pow (n : ℕ) : n ≤ 2 ^ parallelLoopDepth n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [parallelLoopDepth_of_le_one hn, pow_zero]
        omega
      · rw [parallelLoopDepth_unfold (by omega), pow_succ]
        have h1 := ih (n / 2) (by omega)
        have h2 := ih (n - n / 2) (by omega)
        have hmax :
            2 ^ max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) =
              max (2 ^ parallelLoopDepth (n / 2))
                (2 ^ parallelLoopDepth (n - n / 2)) := by
          rcases le_total (parallelLoopDepth (n / 2))
            (parallelLoopDepth (n - n / 2)) with h | h
          · rw [max_eq_right h,
              max_eq_right (Nat.pow_le_pow_right (by norm_num) h)]
          · rw [max_eq_left h,
              max_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
        rw [hmax]
        rcases le_total (2 ^ parallelLoopDepth (n / 2))
          (2 ^ parallelLoopDepth (n - n / 2)) with h | h
        · rw [max_eq_right h]
          omega
        · rw [max_eq_left h]
          omega

/-- The balanced parallel-loop depth is bounded by one more than the
base-two floor logarithm on every input. -/
theorem parallelLoopDepth_le_log (n : ℕ) :
    parallelLoopDepth n ≤ Nat.log 2 n + 1 := by
  have hdepth_clog : parallelLoopDepth n ≤ Nat.clog 2 n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n ≤ 1
        · rw [parallelLoopDepth_of_le_one hn]
          exact Nat.zero_le _
        · have hfloor := ih (n / 2) (by omega)
          have hceil := ih (n - n / 2) (by omega)
          have hfloor_le_ceil : n / 2 ≤ n - n / 2 := by omega
          have hhalf : (n + 2 - 1) / 2 = n - n / 2 := by omega
          rw [parallelLoopDepth_unfold (by omega),
            Nat.clog_of_two_le (by norm_num) (by omega), hhalf]
          exact Nat.add_le_add_right
            (max_le (hfloor.trans (Nat.clog_mono_right 2 hfloor_le_ceil)) hceil) 1
  apply hdepth_clog.trans
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact (Nat.lt_pow_succ_log_self (by norm_num) n).le

/-- The balanced parallel-loop span is at most one iteration's weight plus
one more than the base-two floor logarithm, on every input. -/
theorem parallelLoop_span_le_log (n w : ℕ) :
    (parallelLoopTree n w).span ≤ w + Nat.log 2 n + 1 := by
  rw [parallelLoop_span]
  by_cases hn : n ≤ 1
  · rw [if_pos hn]
    interval_cases n <;> simp
  · rw [if_neg hn]
    exact Nat.add_le_add_left (parallelLoopDepth_le_log n) w

example : parallelLoopDepth 0 = 0 := by native_decide

example : parallelLoopDepth 1 = 0 := by native_decide

example : parallelLoopDepth 2 = 1 := by native_decide

example : parallelLoopDepth 3 = 2 := by native_decide

example : parallelLoopDepth 8 = 3 := by native_decide

example : parallelLoopDepth 9 = 4 := by native_decide

example : (parallelLoopTree 9 3).span ≤ 3 + Nat.log 2 9 + 1 :=
  parallelLoop_span_le_log 9 3


end Chapter27
end CLRS
