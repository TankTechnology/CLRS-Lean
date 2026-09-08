import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Policies

/-!
# Valid offline paging schedules

A schedule records legal cache transitions for an entire request trace, with
its actual miss count. It can depend on the future. The existing phase-based
offline execution produces such a schedule, including every intermediate
capacity invariant; its comparison cost is therefore attainable.
-/
namespace CLRS.OnlineCaching
variable {Page : Type} [DecidableEq Page] {k : Nat}

inductive Schedule (k : Nat) : Finset Page → List Page → Finset Page → Nat → Prop
  | nil (C : Finset Page) (size : C.card ≤ k) : Schedule k C [] C 0
  | cons (C C' : Finset Page) (p : Page) (xs : List Page) (final : Finset Page) (cost : Nat)
      (size : C.card ≤ k) (loads : p ∈ C') (subset : C' ⊆ insert p C)
      (hit : p ∈ C → C' = C) (tail : Schedule k C' xs final cost) :
      Schedule k C (p :: xs) final ((if p ∈ C then 0 else 1) + cost)

namespace Schedule

theorem append {C D F : Finset Page} {xs ys : List Page} {a b : Nat}
    (hx : Schedule k C xs D a) (hy : Schedule k D ys F b) :
    Schedule k C (xs ++ ys) F (a + b) := by
  induction hx with
  | nil _ _ => simpa using hy
  | cons C C' p xs final cost hs hl hsub hh ht ih =>
    simpa [Nat.add_assoc] using cons C C' p (xs ++ ys) F (cost+b) hs hl hsub hh (ih hy)

end Schedule

theorem servePhase_schedule (phase C : Finset Page) (xs : List Page)
    (hC : C.card ≤ k) (hxs : xs.toFinset ⊆ phase) (hphase : phase.card ≤ k) :
    Schedule k C xs (servePhase phase C xs) (servePhaseMisses phase C xs) := by
  induction xs generalizing C with
  | nil => exact .nil C hC
  | cons p xs ih =>
    have hp := hxs (by simp : p ∈ (p::xs).toFinset)
    have ht : xs.toFinset ⊆ phase := by intro x hx; exact hxs (by simp [hx])
    exact .cons C (offlineStep phase C p) p xs _ _ hC
      (offlineStep_loads _ _ _) (offlineStep_subset _ _ _) (offlineStep_hit _ _ _)
      (ih _ (offlineStep_size _ _ _ hC hp hphase) ht)

theorem off_schedule (C : Finset Page) (ps : List (List Page)) (hC : C.card ≤ k)
    (hps : ∀ xs ∈ ps, xs.toFinset.card ≤ k) :
    Schedule k C ps.flatten (offCache C ps) (offMisses C ps) := by
  induction ps generalizing C with
  | nil => exact .nil C hC
  | cons xs ps ih =>
    have hx := hps xs (by simp)
    have hs := servePhase_schedule xs.toFinset C xs hC (by intro x h; exact h) hx
    have ht := ih (servePhase xs.toFinset C xs)
      (servePhase_card_le _ _ _ hC (by intro x h; exact h) hx)
      (by intro ys hy; exact hps ys (by simp [hy]))
    exact hs.append ht

theorem phases_capacity (hk : 0 < k) (xs : List Page) :
    ∀ ys ∈ phases k xs, ys.toFinset.card ≤ k := by
  classical
  have go : ∀ n (xs : List Page), xs.length = n → ∀ ys ∈ phases k xs, ys.toFinset.card ≤ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro xs hn ys hy
      by_cases hempty : xs = []
      · subst xs; simp [phases, WellFounded.fix_eq] at hy
      · rw [phases_cons_eq k xs hempty] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact firstPhase_distinct_le k xs hk
        · have hlen : (firstPhase k xs).2.length < n := by
            have hsplit := congrArg List.length (firstPhase_split k xs)
            have hp := List.length_pos_of_ne_nil (firstPhase_nonempty k xs hempty)
            simp only [List.length_append] at hsplit
            omega
          exact ih _ hlen _ rfl ys hy
  exact go xs.length xs rfl

/-- The phase comparator cost is realized by a legal empty-start offline schedule. -/
theorem offline_schedule_valid (hk : 0 < k) (xs : List Page) :
    Schedule k ∅ xs (offCache ∅ (phases k xs)) (offMisses ∅ (phases k xs)) := by
  simpa only [phases_join] using off_schedule (∅ : Finset Page) (phases k xs)
    (by simp) (phases_capacity hk xs)

/-- A policy's actual run supplies a legal schedule, including hidden-state policies. -/
theorem Policy.schedule (A : Policy Page k) (s : A.State) (xs : List Page) :
    Schedule k (A.cache s) xs (A.cache (A.run s xs)) (A.misses s xs) := by
  induction xs generalizing s with
  | nil => exact .nil _ (A.size s)
  | cons p xs ih =>
    exact .cons _ _ p xs _ _ (A.size s) (A.loads s p) (A.subset s p) (A.hit s p) (ih _)

end CLRS.OnlineCaching
