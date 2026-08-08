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

/--
The cache and decision of the **exchange schedule** for the first fault
where `d` and the farthest-in-future policy disagree (position `t`,
request `p`, `d` evicting `q`, the policy evicting `q'`): it agrees with
`d` before `t`, evicts `q'` at `t` (so its cache agrees with the
farthest-in-future run through `t+1`), and afterwards follows `d` except
that it never evicts a page that `d` keeps while the exchange schedule
lacks it: when `d` evicts `q'` it evicts `q` instead, and when `d` hits a
request of `q` or `q'` that the exchange schedule misses, it evicts a
page that `d` does not have (a multi-set element of its own cache
relative to `d`'s, preferring pages other than `q'`), so that no bad
event (a fault where `d` hits) is created.  The pair (cache, decision) is
computed jointly by structural recursion.
-/
noncomputable def exchangeScheduleCore (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) : ℕ → Finset Page × Page
  | 0 => (C₀, d 0)
  | s + 1 =>
      let prev := exchangeScheduleCore d t q q' σ C₀ s
      let r : Page := σ.getD s 0
      let Csucc : Finset Page :=
        if r ∈ prev.1 then prev.1 else insert r (prev.1.erase prev.2)
      let Cd : Finset Page := schedCache d C₀ σ (s + 1)
      let M : Finset Page := Csucc \ Cd
      let r' : Page := σ.getD (s + 1) 0
      let decision : Page :=
        if s + 1 < t then d (s + 1)
        else if s + 1 = t then q'
        else if d (s + 1) = q' then (if q' ∈ Csucc then q' else q)
        else if (r' = q' ∨ r' = q) ∧ r' ∈ Cd then
          if h : (M.filter (fun x => x ≠ q')).Nonempty then Classical.choose h
          else if h : M.Nonempty then Classical.choose h
          else 0
        else if d (s + 1) ∈ Csucc then d (s + 1)
        else if h : M.Nonempty then Classical.choose h
        else 0
      (Csucc, decision)

/-- The decision function of the exchange schedule. -/
noncomputable def exchangeSchedule (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) : ℕ → Page :=
  fun s => (exchangeScheduleCore d t q q' σ C₀ s).2

/-- The exchange schedule's run is the cache component of the core. -/
lemma schedCache_exchangeScheduleCore (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) (s : ℕ) :
    schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s =
      (exchangeScheduleCore d t q q' σ C₀ s).1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      unfold schedCache
      rw [ih]
      cases s with
      | zero => rfl
      | succ s' =>
          unfold exchangeScheduleCore
          rfl

end Caching

end CLRS
