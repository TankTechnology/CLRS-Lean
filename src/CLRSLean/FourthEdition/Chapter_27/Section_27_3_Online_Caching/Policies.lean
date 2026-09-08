import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching

/-!
# Inhabited paging policies with auxiliary state

The legacy finite-set interface describes memoryless policies. The new Policy
interface has arbitrary internal state and exposes only its resident set.
A hit preserves residency, but may update history. The transition receives
only the current state and request, so it cannot inspect future requests.
Capacity is an invariant of every state in its state type. An offline schedule
instead receives a request trace and may choose its evictions from that trace.
-/
namespace CLRS.OnlineCaching
variable {Page : Type} [DecidableEq Page] {k : Nat}

/-- A concrete memoryless policy: retain a hit, flush to the request on a miss. -/
def flushAlgorithm (hk : 0 < k) : Algorithm Page k where
  step C p := if p ∈ C then C else {p}
  step_loads := by intro C p; split <;> simp_all
  step_subset := by intro C p; split <;> simp_all
  step_size := by intro C p hC; split <;> simp_all; omega
  step_hit := by intro C p _ hp; simp [hp]

/-- Positive-capacity policy space is inhabited even on the k+1 page universe. -/
theorem algorithm_nonempty (hk : 0 < k) : Nonempty (Algorithm Page k) := ⟨flushAlgorithm hk⟩

structure Policy (Page : Type) [DecidableEq Page] (k : Nat) where
  State : Type
  cache : State → Finset Page
  initial : State
  initial_empty : cache initial = ∅
  step : State → Page → State
  size : ∀ s, (cache s).card ≤ k
  loads : ∀ s p, p ∈ cache (step s p)
  subset : ∀ s p, cache (step s p) ⊆ insert p (cache s)
  hit : ∀ s p, p ∈ cache s → cache (step s p) = cache s

namespace Policy
variable (A : Policy Page k)

def run : A.State → List Page → A.State
  | s, [] => s
  | s, p :: ps => run (A.step s p) ps

def misses : A.State → List Page → Nat
  | _, [] => 0
  | s, p :: ps => (if p ∈ A.cache s then 0 else 1) + misses (A.step s p) ps

@[simp] theorem run_append (s : A.State) (xs ys : List Page) :
    A.run s (xs ++ ys) = A.run (A.run s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons p xs ih => simp [run, ih]

@[simp] theorem misses_append (s : A.State) (xs ys : List Page) :
    A.misses s (xs ++ ys) = A.misses s xs + A.misses (A.run s xs) ys := by
  induction xs generalizing s with
  | nil => simp [misses, run]
  | cons p xs ih => simp [misses, run, ih, Nat.add_assoc]

theorem zero_subset (s : A.State) (xs : List Page) (h : A.misses s xs = 0) :
    xs.toFinset ⊆ A.cache s := by
  induction xs generalizing s with
  | nil => simp
  | cons p xs ih =>
    have hp : p ∈ A.cache s := by
      by_contra hn
      simp [misses, hn] at h
    have ht : A.misses (A.step s p) xs = 0 := by simpa [misses, hp] using h
    have hs := ih (A.step s p) ht
    rw [A.hit s p hp] at hs
    simpa using Finset.insert_subset_iff.mpr ⟨hp, hs⟩

theorem resident_fault (s : A.State) (p : Page) (xs : List Page)
    (hp : p ∈ A.cache s) (hx : k ≤ (xs.toFinset.erase p).card) :
    1 ≤ A.misses s xs := by
  by_contra hn
  have hz : A.misses s xs = 0 := by omega
  have hs := A.zero_subset s xs hz
  have hc : (xs.toFinset.erase p).card ≤ ((A.cache s).erase p).card :=
    Finset.card_le_card (Finset.erase_subset_erase p hs)
  rw [Finset.card_erase_of_mem hp] at hc
  have hpos := Finset.card_pos.mpr ⟨p,hp⟩
  have hb := A.size s
  omega
end Policy

/-- LRU stores recency order as well as residency. -/
structure LRUState (Page : Type) (k : Nat) where
  recency : List Page
  nodup : recency.Nodup
  size : recency.length ≤ k

theorem lruStep_length_le (hk : 0 < k) (L : List Page) (p : Page) (hL : L.length ≤ k) :
    (lruStep k L p).length ≤ k := by
  unfold lruStep
  split_ifs with hp hl
  · have heq := (List.perm_cons_erase hp).length_eq
    simpa only [← heq] using hL
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons, List.length_dropLast]; omega

def lruPolicy (hk : 0 < k) : Policy Page k where
  State := LRUState Page k
  cache s := s.recency.toFinset
  initial := ⟨[], by simp, by simp⟩
  initial_empty := rfl
  step s p := ⟨lruStep k s.recency p, lruStep_nodup k _ p s.nodup,
    lruStep_length_le hk _ p s.size⟩
  size s := by simpa [toFinset_card_of_nodup s.nodup] using s.size
  loads s p := by simp [lruStep]; split_ifs <;> simp
  subset s p := by
    intro q hq
    simp only [List.mem_toFinset, mem_lruStep] at hq
    split_ifs at hq with hp hl
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hq)
    · simpa using hq
    · rcases hq with rfl | hq
      · simp
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_of_mem_dropLast hq))
  hit s p hp := by
    ext q
    simp only [List.mem_toFinset] at hp ⊢
    simp [mem_lruStep, hp]

/-- The stateful LRU policy's misses are those of the original list execution. -/
theorem lruPolicy_misses (hk : 0 < k) (s : LRUState Page k) (xs : List Page) :
    (lruPolicy hk).misses s xs = lruMissesGo k s.recency xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons p xs ih =>
    change (if p ∈ s.recency.toFinset then 0 else 1) +
      (lruPolicy hk).misses ((lruPolicy hk).step s p) xs = _
    rw [ih]
    simp [lruMissesGo, lruPolicy]


end CLRS.OnlineCaching
