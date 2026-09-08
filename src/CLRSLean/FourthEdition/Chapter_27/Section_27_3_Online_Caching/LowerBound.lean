import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Policies

/-!
# Deterministic paging lower bound with real ratios and additive constants

The adversary observes only a policy's current resident set. Arbitrary hidden
history is permitted in the online policy. The offline comparator is the
existing trace-dependent phase schedule; it is not claimed to be an online
finite-set transition. Witness length grows with the additive constant.
-/
noncomputable section
namespace CLRS.OnlineCaching.Policy
variable {k : Nat} (A : Policy (Fin (k + 1)) k)

def adversary (s : A.State) : Nat → List (Fin (k + 1))
  | 0 => []
  | n + 1 =>
    let p := freshPage (A.cache s)
    p :: adversary (A.step s p) n

@[simp] theorem adversary_length (s : A.State) (n : Nat) :
    (A.adversary s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [adversary, ih]

@[simp] theorem adversary_misses (s : A.State) (n : Nat) :
    A.misses s (A.adversary s n) = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hp := freshPage_spec (A.cache s) (exists_page_not_mem _ (A.size s))
    simp [adversary, misses, hp, ih, Nat.add_comm]

/-- A history-dependent online policy misses every request of an arbitrary-length witness. -/
theorem caching_lower_bound (hk : 0 < k) (N : Nat) :
    ∃ xs : List (Fin (k + 1)), xs.length = N ∧ A.misses A.initial xs = N ∧
      offMisses ∅ (phases k xs) ≤ N / k + k + 1 := by
  refine ⟨A.adversary A.initial N, by simp, by simp, ?_⟩
  have h := offMisses_bound k (A.adversary A.initial N) hk
  have hp := phases_length_le k (A.adversary A.initial N) hk
  simp only [adversary_length] at hp
  omega

/-- Every real ratio below k fails, for every real additive constant.
The witness is nonempty and both runs begin with empty caches. -/
theorem no_real_competitive (hk : 0 < k) (c b : ℝ) (hc0 : 0 ≤ c) (hc : c < k) :
    ∃ xs : List (Fin (k + 1)), 0 < xs.length ∧
      c * (offMisses ∅ (phases k xs) : ℝ) + b < (A.misses A.initial xs : ℝ) := by
  have hgap : 0 < (k : ℝ) - c := sub_pos.mpr hc
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 ((c * ((k : ℝ) + 1) + b) / ((k : ℝ) - c)))
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
    exact_mod_cast this
  have hratio : (c * ((k : ℝ) + 1) + b) / ((k : ℝ) - c) < m :=
    (le_max_right _ _).trans_lt hm
  have hlarge : c * ((k : ℝ) + 1) + b < (m : ℝ) * ((k : ℝ) - c) :=
    (div_lt_iff₀ hgap).mp hratio
  obtain ⟨xs,hlen,hmiss,hoff⟩ := A.caching_lower_bound hk (k * m)
  have hdiv : k * m / k = m := Nat.mul_div_cancel_left m hk
  rw [hdiv] at hoff
  refine ⟨xs, by rw [hlen]; exact Nat.mul_pos hk hmpos, ?_⟩
  have hoffR : (offMisses ∅ (phases k xs) : ℝ) ≤ (m : ℝ) + k + 1 := by exact_mod_cast hoff
  have hscaled := mul_le_mul_of_nonneg_left hoffR hc0
  rw [hmiss]
  push_cast
  nlinarith

end CLRS.OnlineCaching.Policy
