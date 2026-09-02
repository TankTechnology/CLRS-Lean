import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model

/-!
# S2. The farthest-in-future eviction

The greedy choice of the offline caching problem (CLRS §15.4): when a fault
occurs, evict the resident page whose next use is farthest in the future.
Pages never requested again count as farthest (`none`).  Ties are broken
arbitrarily (towards the left in the enumeration order of the cache).

Main results:

- `Farther`: the "at least as far in the future" order on next-use options
  (`none` = never again is the farthest)
- `farthestInFuture cache σ i`: the resident page whose next use at or after
  position `i` is farthest
- `mem_farthestInFuture`: the chosen page is resident
- `farthestInFuture_max`: no resident page has a farther next use
- `fifoPolicy σ`: the farthest-in-future eviction policy for `σ`
- `fifo_step_of_mem` / `fifo_step_fault`: the cache transition of the policy

Notation conventions used in this section:

- `C` : cache
- `σ` : request sequence
- `i` : position of the fault
-/

namespace CLRS

open Finset

namespace Caching

/--
`Farther a b` says that the next use `a` is at least as far in the future as
`b`: `none` (never requested again) is the farthest, and among `some i` /
`some j` the one with the larger position is farther (CLRS §15.4).
-/
def Farther (a b : Option ℕ) : Prop :=
  match a, b with
  | none, _ => True
  | some _, none => False
  | some i, some j => j ≤ i

/-- Farther-in-the-future is reflexive. -/
lemma farther_refl (a : Option ℕ) : Farther a a := by
  cases a <;> simp [Farther]

/-- Farther-in-the-future is transitive. -/
lemma farther_trans {a b c : Option ℕ} (hab : Farther a b) (hbc : Farther b c) :
    Farther a c := by
  cases a with
  | none => simp [Farther]
  | some i =>
      cases b with
      | none =>
          simp [Farther] at hab
      | some j =>
          cases c with
          | none =>
              simp [Farther] at hbc
          | some k =>
              simp [Farther] at hab hbc ⊢
              omega

/-- Farther-in-the-future is total. -/
lemma farther_total {a b : Option ℕ} (h : ¬ Farther a b) : Farther b a := by
  cases a with
  | none =>
      simp [Farther] at h
  | some i =>
      cases b with
      | none => simp [Farther]
      | some j =>
          simp [Farther] at h ⊢
          omega

/-- If `a` is at least as far as `b`, then either `a` is `none`, or both are
`some` with `b`'s position no later than `a`'s. -/
lemma farther_cases {a b : Option ℕ} (h : Farther a b) :
    a = none ∨ ∃ i j, a = some i ∧ b = some j ∧ j ≤ i := by
  cases a with
  | none => exact Or.inl rfl
  | some i =>
      cases b with
      | none =>
          simp [Farther] at h
      | some j => exact Or.inr ⟨i, j, rfl, rfl, by simpa [Farther] using h⟩

/-- `none` is at least as far as any next use. -/
lemma farther_none (a : Option ℕ) : Farther none a := by
  cases a <;> simp [Farther]

/-- The farther-in-the-future relation is decidable. -/
instance instDecidableFarther (a b : Option ℕ) : Decidable (Farther a b) := by
  unfold Farther
  cases a <;> cases b <;> infer_instance

/-- A concrete next use is never as far as `none`. -/
lemma not_farther_of_some_none {i : ℕ} : ¬ Farther (some i) none := by
  simp [Farther]

/-- The page in `l` whose next use under `f` is farthest in the future,
ties broken towards the left; junk value 0 on the empty list. -/
def farthestInList (f : Page → Option ℕ) : List Page → Page
  | [] => 0
  | p :: rest =>
      if rest = [] then p
      else
        let q := farthestInList f rest
        if Farther (f p) (f q) then p else q

/-- The page chosen by `farthestInList` is at least as far in the future as
every page of the list. -/
lemma farthestInList_spec (f : Page → Option ℕ) (l : List Page) :
    ∀ r ∈ l, Farther (f (farthestInList f l)) (f r) := by
  induction l with
  | nil => simp [farthestInList]
  | cons p rest ih =>
      by_cases hrest : rest = []
      · rw [hrest]
        intro r hr
        simp [farthestInList] at hr ⊢
        rw [← hr]
        exact farther_refl (f r)
      · by_cases hpq : Farther (f p) (f (farthestInList f rest))
        · intro r hr
          simp [farthestInList, hrest, hpq] at hr ⊢
          rcases hr with hr | hr
          · subst hr
            exact farther_refl (f r)
          · exact farther_trans hpq (ih r hr)
        · intro r hr
          simp [farthestInList, hrest, hpq] at hr ⊢
          rcases hr with rfl | hr
          · exact farther_total hpq
          · exact ih r hr

/-- On a nonempty list, `farthestInList` returns a page of the list. -/
lemma mem_farthestInList {f : Page → Option ℕ} {l : List Page} (hl : l ≠ []) :
    farthestInList f l ∈ l := by
  induction l with
  | nil => simp at hl
  | cons p rest ih =>
      by_cases hrest : rest = []
      · subst rest
        simp [farthestInList]
      · by_cases hpq : Farther (f p) (f (farthestInList f rest))
        · simp [farthestInList, hrest, hpq]
        · simpa [farthestInList, hrest, hpq, List.mem_cons] using (Or.inr (ih hrest))

/-- The resident page of `cache` whose next use at or after position `i` is
farthest in the future (pages never requested again count as farthest; ties
are broken arbitrarily).  Junk value 0 on the empty cache (CLRS §15.4). -/
noncomputable def farthestInFuture (cache : Finset Page) (σ : List Page) (i : ℕ) : Page :=
  farthestInList (fun p => nextUse σ (i + 1) p) cache.toList

/-- On a nonempty cache, `farthestInFuture` returns a resident page. -/
lemma mem_farthestInFuture {cache : Finset Page} {σ : List Page} {i : ℕ}
    (h : cache.Nonempty) :
    farthestInFuture cache σ i ∈ cache := by
  unfold farthestInFuture
  have hmem : farthestInList (fun p => nextUse σ (i + 1) p) cache.toList ∈ cache.toList := by
    apply mem_farthestInList
    rcases h with ⟨p, hp⟩
    have hp' : p ∈ cache.toList := by simpa [Finset.mem_toList] using hp
    exact List.ne_nil_of_mem hp'
  simpa [Finset.mem_toList] using hmem

/-- No resident page has a next use at or after position `i` that is farther
than that of `farthestInFuture cache σ i`. -/
lemma farthestInFuture_max {cache : Finset Page} {σ : List Page} {i : ℕ} {p : Page}
    (hp : p ∈ cache) :
    Farther (nextUse σ (i + 1) (farthestInFuture cache σ i)) (nextUse σ (i + 1) p) := by
  unfold farthestInFuture
  apply farthestInList_spec
  simpa [Finset.mem_toList] using hp

/--
The farthest-in-future eviction policy for the request list `σ` (the Belady
algorithm, CLRS §15.4): at a fault, evict the resident page whose next use is
farthest in the future.
-/
noncomputable def fifoPolicy (σ : List Page) : Policy where
  evict := fun i C p => farthestInFuture C σ i
  evict_mem := by
    intro i C p hp hC
    exact mem_farthestInFuture hC

/-- The farthest-in-future policy keeps the cache unchanged on a hit. -/
lemma fifo_step_of_mem (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page) (hp : p ∈ C) :
    (fifoPolicy σ).step i C p = C := by
  simp [Policy.step, hp]

/-- On a fault, the farthest-in-future policy evicts the farthest-in-future
page and loads the requested page. -/
lemma fifo_step_fault (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page) (hp : p ∉ C) :
    (fifoPolicy σ).step i C p = insert p (C.erase (farthestInFuture C σ i)) := by
  simp [Policy.step, fifoPolicy, hp]

end Caching

end CLRS
