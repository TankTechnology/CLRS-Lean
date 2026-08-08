import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S2_Farthest_In_Future

/-!
# S3. Optimality of the farthest-in-future policy

Basic sanity lemmas for the farthest-in-future (Belady) eviction policy of
CLRS §15.4: it always evicts a resident page and preserves the cache size.

Main results:

- `fifo_evicts_resident`: the FIF policy evicts a resident page
- `fifo_step_size`: a FIF step preserves the cache size

Current gaps:

- The optimality theorem (`fifo_optimal`: no eviction policy — even offline —
  has fewer misses than the farthest-in-future policy, CLRS Theorem 15.5)
  remains to be formalized: the classical exchange argument transforms an
  optimal policy at a fault into one that evicts the farthest-in-future page
  by simulating the two caches between the fault and the evicted page's next
  request.  This requires a suffix-simulation induction over the request
  sequence that is deferred.
-/

namespace CLRS

namespace Caching

open Finset

/-- The farthest-in-future policy always evicts a resident page. -/
lemma fifo_evicts_resident (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hp : p ∉ C) (hC : C.Nonempty) :
    (fifoPolicy σ).evict i C p ∈ C :=
  (fifoPolicy σ).evict_mem i C p hp hC

/-- A step of the farthest-in-future policy preserves the cache size. -/
lemma fifo_step_size (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hC : C.Nonempty) :
    ((fifoPolicy σ).step i C p).card = C.card :=
  step_card (fifoPolicy σ) i C p hC

/--
A **schedule** for the request list `σ` is a decision function
`d : ℕ → Page` giving, for every position `s`, the page to evict at that
position.  The schedule's run `schedCache d C₀ σ` starts from `C₀`: a hit
keeps the cache, a fault evicts `d s` (an eviction of an absent page is a
no-op, so schedules need not be reduced) and loads the requested page.
-/
def schedCache (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) : ℕ → Finset Page
  | 0 => C₀
  | s + 1 => if σ.getD s 0 ∈ schedCache d C₀ σ s then schedCache d C₀ σ s
             else insert (σ.getD s 0) ((schedCache d C₀ σ s).erase (d s))

/-- Whether position `s` is a miss for the schedule `d` from `C₀` on `σ`
(`0` or `1`). -/
def schedFaultAt (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) (s : ℕ) : ℕ :=
  if σ.getD s 0 ∈ schedCache d C₀ σ s then 0 else 1

/-- The number of misses of the schedule `d` from `C₀` on `σ`. -/
def schedMisses (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) : ℕ :=
  ∑ s ∈ Finset.range σ.length, schedFaultAt d C₀ σ s

/-- The schedule induced by a policy: at position `s` it evicts exactly the
page the policy evicts in its own run. -/
def policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) : ℕ → Page :=
  fun s => π.evict s (cacheSeq π C₀ σ s) (σ.getD s 0)

/-- The run of a policy's schedule is the policy's own run. -/
lemma schedCache_policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) (s : ℕ) :
    schedCache (policySchedule π C₀ σ) C₀ σ s = cacheSeq π C₀ σ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      unfold schedCache
      rw [ih]
      cases s with
      | zero => rfl
      | succ s' =>
          unfold cacheSeq
          rfl

/-- A policy and its schedule incur the same number of misses. -/
lemma schedMisses_policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) :
    schedMisses (policySchedule π C₀ σ) C₀ σ = misses π C₀ σ := by
  unfold schedMisses misses faultAt
  apply Finset.sum_congr rfl
  intro s hs
  unfold schedFaultAt
  rw [schedCache_policySchedule]

end Caching

end CLRS
