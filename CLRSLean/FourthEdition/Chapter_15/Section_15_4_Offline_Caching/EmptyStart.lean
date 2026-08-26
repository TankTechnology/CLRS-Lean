import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S3_Optimality

/-!
# Empty-start boundary for offline caching

The core eviction trace starts from a nonempty cache because every fault must
name a resident page to evict.  This module isolates the compulsory first miss:
under the core transition semantics an empty cache becomes the singleton
containing the first request, independently of the policy.  Thereafter the
existing exchange theorem applies unchanged.

For a capacity greater than one, the deterministic compulsory-fill phase is
represented separately by {lit}`compulsoryFillCost`; once a nonempty resident set is
handed to the eviction phase, adding the same fill cost preserves optimality.
-/

namespace CLRS.Caching

open Finset

/-- Shift from an empty cache and from the first-page singleton agrees after request 0. -/
theorem cacheSeq_empty_eq_singleton_after_first
    (π : Policy) (p : Page) (rest : List Page) (t : Nat) :
    cacheSeq π ∅ (p :: rest) (t + 1) =
      cacheSeq π {p} (p :: rest) (t + 1) := by
  induction t with
  | zero => simp [cacheSeq, Policy.step]
  | succ t ih =>
      change π.step (t + 1) (cacheSeq π ∅ (p :: rest) (t + 1))
          ((p :: rest).getD (t + 1) 0) =
        π.step (t + 1) (cacheSeq π {p} (p :: rest) (t + 1))
          ((p :: rest).getD (t + 1) 0)
      rw [ih]

theorem faultAt_empty_zero (π : Policy) (p : Page) (rest : List Page) :
    faultAt π ∅ (p :: rest) 0 = 1 := by
  simp [faultAt, cacheSeq]

theorem faultAt_singleton_zero (π : Policy) (p : Page) (rest : List Page) :
    faultAt π {p} (p :: rest) 0 = 0 := by
  simp [faultAt, cacheSeq]

theorem faultAt_empty_eq_singleton_succ
    (π : Policy) (p : Page) (rest : List Page) (t : Nat) :
    faultAt π ∅ (p :: rest) (t + 1) =
      faultAt π {p} (p :: rest) (t + 1) := by
  unfold faultAt
  rw [cacheSeq_empty_eq_singleton_after_first]

/-- Every policy pays exactly one additional compulsory miss when starting empty. -/
theorem misses_empty_eq_singleton_add_one
    (π : Policy) (p : Page) (rest : List Page) :
    misses π ∅ (p :: rest) = misses π {p} (p :: rest) + 1 := by
  have hempty :
      misses π ∅ (p :: rest) =
        1 + ∑ t ∈ Finset.range rest.length,
          faultAt π ∅ (p :: rest) (t + 1) := by
    unfold misses
    rw [show (p :: rest).length = rest.length + 1 by simp,
      sum_range_shift]
    rw [faultAt_empty_zero]
  have hsingleton :
      misses π {p} (p :: rest) =
        ∑ t ∈ Finset.range rest.length,
          faultAt π {p} (p :: rest) (t + 1) := by
    unfold misses
    rw [show (p :: rest).length = rest.length + 1 by simp,
      sum_range_shift]
    rw [faultAt_singleton_zero, zero_add]
  rw [hempty, hsingleton]
  have hsum :
      (∑ t ∈ Finset.range rest.length,
          faultAt π ∅ (p :: rest) (t + 1)) =
        ∑ t ∈ Finset.range rest.length,
          faultAt π {p} (p :: rest) (t + 1) := by
    apply Finset.sum_congr rfl
    intro t _
    exact faultAt_empty_eq_singleton_succ π p rest t
  rw [hsum, Nat.add_comm]

/--
Farthest-in-future is optimal from the literal empty cache in the core
transition semantics; the empty request list and the compulsory first miss are
both covered.
-/
theorem fifo_optimal_from_empty (π : Policy) (σ : List Page) :
    misses (fifoPolicy σ) ∅ σ ≤ misses π ∅ σ := by
  cases σ with
  | nil => simp [misses]
  | cons p rest =>
      rw [misses_empty_eq_singleton_add_one (fifoPolicy (p :: rest)) p rest,
        misses_empty_eq_singleton_add_one π p rest]
      exact Nat.add_le_add_right
        (fifo_optimal π {p} (p :: rest) (by simp)) 1

/-- Cost decomposition after a policy-independent compulsory-fill phase. -/
def compulsoryFillCost
    (fillMisses : Nat) (π : Policy) (resident : Finset Page)
    (remaining : List Page) : Nat :=
  fillMisses + misses π resident remaining

/--
Adding a common compulsory-fill cost does not change the optimal eviction
policy for the remaining requests.  This is the capacity-independent bridge
used when a textbook cache is filled before the first eviction.
-/
theorem fifo_optimal_after_compulsory_fill
    (fillMisses : Nat) (π : Policy) (resident : Finset Page)
    (remaining : List Page) (hresident : resident.Nonempty) :
    compulsoryFillCost fillMisses (fifoPolicy remaining) resident remaining ≤
      compulsoryFillCost fillMisses π resident remaining := by
  unfold compulsoryFillCost
  exact Nat.add_le_add_left (fifo_optimal π resident remaining hresident) fillMisses

end CLRS.Caching
