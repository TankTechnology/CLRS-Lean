import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.OfflineCompetitive

/-!
# LRU against policies with arbitrary auxiliary state

Actual policy runs produce legal schedules. The offline trace theorem therefore
also proves the online result without replaying any requests or assuming that
hits leave auxiliary history unchanged.
-/
namespace CLRS.OnlineCaching.Policy
variable {Page : Type} [DecidableEq Page] {k : Nat}

theorem phases_from_resident (A : Policy Page k) (hk : 0 < k)
    (p : Page) (rest : List Page) (s : A.State) (hp : p ∈ A.cache s) :
    (phases k (p :: rest)).length ≤ A.misses s rest + 1 :=
  Schedule.phases_from_resident hk p rest (A.schedule s rest) hp

theorem phases_le_misses (A : Policy Page k) (hk : 0 < k) (s : A.State) (xs : List Page) :
    (phases k xs).length ≤ A.misses s xs + 1 := (A.schedule s xs).phases_le_cost hk

/-- LRU's actual list execution is k-competitive against every history-dependent policy. -/
theorem lru_k_competitive (A : Policy Page k) (hk : 0 < k) (xs : List Page) :
    (lruPolicy hk).misses (lruPolicy hk).initial xs ≤ k * A.misses A.initial xs + k := by
  rw [lruPolicy_misses]
  have hs := A.schedule A.initial xs
  rw [A.initial_empty] at hs
  exact hs.lru_k_competitive hk

end CLRS.OnlineCaching.Policy
