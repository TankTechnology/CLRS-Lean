import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Schedules

/-! # LRU competitiveness against every legal offline trace -/
namespace CLRS.OnlineCaching.Schedule
variable {Page : Type} [DecidableEq Page] {k : Nat}

theorem start_size {C F : Finset Page} {xs : List Page} {cost : Nat}
    (h : Schedule k C xs F cost) : C.card ≤ k := by cases h <;> assumption

theorem split {C F : Finset Page} (xs ys : List Page) {cost : Nat}
    (h : Schedule k C (xs ++ ys) F cost) :
    ∃ D a b, Schedule k C xs D a ∧ Schedule k D ys F b ∧ cost = a + b := by
  induction xs generalizing C cost with
  | nil => exact ⟨C,0,cost,.nil C h.start_size,h,by omega⟩
  | cons p xs ih =>
    cases h with
    | cons C C' p _ F cost hs hl hsub hh ht =>
      obtain ⟨D,a,b,ha,hb,heq⟩ := ih ht
      exact ⟨D,_,b,.cons C C' p xs D a hs hl hsub hh ha,hb,by omega⟩

theorem zero_subset {C F : Finset Page} {xs : List Page} {cost : Nat}
    (h : Schedule k C xs F cost) (hc : cost = 0) : xs.toFinset ⊆ C := by
  induction h with
  | nil => simp
  | cons C C' p xs F cost hs hl hsub hh ht ih =>
    have hp : p ∈ C := by by_contra hn; simp [hn] at hc
    have htail : cost = 0 := by simp [hp] at hc; exact hc
    have hxs := ih htail
    rw [hh hp] at hxs
    simpa using Finset.insert_subset_iff.mpr ⟨hp,hxs⟩

theorem resident_fault {C F : Finset Page} {xs : List Page} {cost : Nat}
    (h : Schedule k C xs F cost) (p : Page) (hp : p ∈ C)
    (hx : k ≤ (xs.toFinset.erase p).card) : 1 ≤ cost := by
  by_contra hn
  have hs := h.zero_subset (by omega)
  have hc := Finset.card_le_card (Finset.erase_subset_erase p hs)
  rw [Finset.card_erase_of_mem hp] at hc
  have hpos := Finset.card_pos.mpr ⟨p,hp⟩
  have hb := h.start_size
  omega

theorem singleton_loads {C F : Finset Page} {p : Page} {cost : Nat}
    (h : Schedule k C [p] F cost) : p ∈ F := by
  cases h with
  | cons C C' p xs F cost hs hl hsub hh ht => cases ht; exact hl

theorem phases_from_resident (hk : 0 < k) (p : Page) (rest : List Page)
    {C F : Finset Page} {cost : Nat} (h : Schedule k C rest F cost) (hp : p ∈ C) :
    (phases k (p :: rest)).length ≤ cost + 1 := by
  classical
  have go : ∀ n (rest : List Page), rest.length = n → ∀ p C F cost,
      Schedule k C rest F cost → p ∈ C → (phases k (p :: rest)).length ≤ cost + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rest hn p C F cost h hp
      let chunk := phaseGo k ({p} : Finset Page) rest
      have hsplit : chunk.1 ++ chunk.2 = rest := phaseGo_split k {p} rest
      cases ht : chunk.2 with
      | nil =>
        rw [phases_cons_eq k (p :: rest) (by simp)]
        change ((p :: chunk.1) :: phases k chunk.2).length ≤ _
        rw [ht]
        simp [phases, WellFounded.fix_eq]
      | cons q tail =>
        have hfp : firstPhase k (p :: rest) = (p :: chunk.1, chunk.2) := rfl
        have hm := firstPhase_maximal k (p :: rest) hk (by rw [hfp, ht]; simp)
        have hcard : (p :: chunk.1).toFinset.card = k := by simpa [hfp] using hm.1
        have hq : q ∉ (p :: chunk.1).toFinset :=
          firstPhase_fresh k (p :: rest) hk q tail (by rw [hfp]; exact ht)
        have hset : (chunk.1 ++ [q]).toFinset.erase p =
            (insert q (p :: chunk.1).toFinset).erase p := by
          ext x
          simp only [Finset.mem_erase, List.mem_toFinset, List.mem_append,
            Finset.mem_insert, List.mem_cons]
          tauto
        have hcount : ((chunk.1 ++ [q]).toFinset.erase p).card = k := by
          rw [hset, Finset.card_erase_of_mem (by simp), Finset.card_insert_of_notMem hq, hcard]
          omega
        have hrest : rest = (chunk.1 ++ [q]) ++ tail := by
          rw [ht] at hsplit
          simpa [List.append_assoc] using hsplit.symm
        rw [hrest] at h
        obtain ⟨D,a,b,ha,hb,hcost⟩ := split (chunk.1 ++ [q]) tail h
        have hfault := ha.resident_fault p hp hcount.ge
        obtain ⟨M,aa,ab,_,hlast,_⟩ := split chunk.1 [q] ha
        have hresident := hlast.singleton_loads
        have hlen : tail.length < n := by
          have := congrArg List.length hrest
          simp at this
          omega
        have hnext := ih tail.length hlen tail rfl q D F b hb hresident
        rw [phases_cons_eq k (p :: rest) (by simp)]
        change ((p :: chunk.1) :: phases k chunk.2).length ≤ _
        rw [ht]
        simp only [List.length_cons]
        omega
  exact go rest.length rest rfl p C F cost h hp

/-- Every legal trace, including a future-dependent offline schedule, obeys the phase lower bound. -/
theorem phases_le_cost (hk : 0 < k) {C F : Finset Page} {xs : List Page} {cost : Nat}
    (h : Schedule k C xs F cost) : (phases k xs).length ≤ cost + 1 := by
  cases h with
  | nil => simp [phases, WellFounded.fix_eq]
  | cons C C' p xs F cost hs hl hsub hh ht =>
    have hb := phases_from_resident hk p xs ht hl
    split <;> omega

/-- LRU's actual misses are k-competitive against every legal empty-start offline schedule. -/
theorem lru_k_competitive (hk : 0 < k) {F : Finset Page} {xs : List Page} {cost : Nat}
    (h : Schedule k ∅ xs F cost) : lruMissesGo k [] xs ≤ k * cost + k := by
  have hu := lru_miss_le_phases k [] xs hk (by simp)
  have hl := h.phases_le_cost hk
  nlinarith [Nat.mul_le_mul_left k hl]

end CLRS.OnlineCaching.Schedule
