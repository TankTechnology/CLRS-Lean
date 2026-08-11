import Mathlib

/-!
# S3. Simple-path extraction

Generic list theory bridging reachability proofs to vertex-simple paths:
a reflexive-transitive reachability proof unfolds to an explicit walk, every
walk contains a vertex-simple walk with the same endpoints, and distinct
endpoints force a simple path of length at least two.

Main results:

- `exists_isChain_of_reflTransGen`: reachability unfolds to an explicit walk
- `exists_nodup_isChain`: every walk contains a vertex-simple walk with the
  same endpoints
- `exists_nodup_path_of_reflTransGen`: a simple path with the same endpoints
  and length at least two
-/
namespace CLRS

namespace Matchings
/-! ## Simple-path extraction

A reflexive-transitive reachability proof contains a vertex-simple path with
the same endpoints.  This is the bridge between the reachability-based
`Flow.hasAugmentingPath` of §26.1 and the explicit alternating paths of this
section. -/

/-- A reflexive-transitive reachability proof unfolds to an explicit walk. -/
theorem exists_isChain_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ p : List α, p.IsChain r ∧ p[0]? = some a ∧ p[p.length - 1]? = some b := by
  induction h
  case refl =>
    exact ⟨[a], List.isChain_singleton a, rfl, rfl⟩
  case tail b' c' hab hbc ih =>
    obtain ⟨p, hp, h0, hlast⟩ := ih
    have hpne : p ≠ [] := fun h => by simp [h] at h0
    refine ⟨p ++ [c'], ?_, ?_, ?_⟩
    · rw [List.isChain_iff_getElem] at hp ⊢
      intro i hi
      have hlen : (p ++ [c']).length = p.length + 1 := by simp
      by_cases hi1 : i + 1 < p.length
      · rw [List.getElem_append_left (by omega), List.getElem_append_left hi1]
        exact hp i hi1
      · have hi2 : i + 1 = p.length := by rw [hlen] at hi; omega
        have hi0 : i < p.length := by omega
        rw [List.getElem_append_left hi0, List.getElem_append_right (by omega)]
        have hpi : p[i]? = some b' := by simpa [← hi2] using hlast
        have hpi' : p[i] = b' := by simpa [hi0] using hpi
        simpa [hpi', hi2] using hbc
    · simpa [hpne, List.length_pos_of_ne_nil] using h0
    · have hlen : (p ++ [c']).length = p.length + 1 := by simp
      rw [hlen]
      simp [List.getElem_append_right, hpne]

/-- Every walk contains a vertex-simple walk with the same endpoints. -/
theorem exists_nodup_isChain {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (p : List α) (hp : p.IsChain r) :
    ∃ q : List α, q.IsChain r ∧ q.Nodup ∧
      q[0]? = p[0]? ∧ q[q.length - 1]? = p[p.length - 1]? := by
  suffices aux : ∀ (n : ℕ) (p : List α), p.length ≤ n → p.IsChain r →
      ∃ q : List α, q.IsChain r ∧ q.Nodup ∧
        q[0]? = p[0]? ∧ q[q.length - 1]? = p[p.length - 1]? from
    aux p.length p le_rfl hp
  intro n
  induction n with
  | zero =>
    intro p hl hp
    simp at hl
    subst hl
    exact ⟨[], by simp, by simp, rfl, rfl⟩
  | succ n ih =>
    intro p hl hp
    by_cases hnd : p.Nodup
    · exact ⟨p, hp, hnd, rfl, rfl⟩
    · rw [List.nodup_iff_getElem?_ne_getElem?] at hnd
      push Not at hnd
      obtain ⟨i, j, hij, hj, heq⟩ := hnd
      have hi : i < p.length := by omega
      have hpi : p[i]? = some p[i] := List.getElem?_eq_getElem hi
      have hpj : p[j]? = some p[j] := List.getElem?_eq_getElem hj
      rw [hpi, hpj] at heq
      simp only [Option.some.injEq] at heq
      set q := p.take (i + 1) ++ p.drop (j + 1) with hq_def
      have hqlen : q.length = p.length - (j - i) := by
        simp [hq_def, List.length_append, List.length_take, List.length_drop, hi, hj]
        omega
      have hqchain : q.IsChain r := by
        rw [List.isChain_iff_getElem] at hp ⊢
        intro k hk
        rw [hqlen] at hk
        have htake : (p.take (i + 1)).length = i + 1 := by
          simp [List.length_take, hi]
        by_cases hk2 : k + 1 < i + 1
        · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
            List.getElem_take, List.getElem_take]
          exact hp k (by omega)
        · by_cases hk3 : k < i
          · omega
          · by_cases hk4 : k = i
            · subst hk4
              rw [List.getElem_append_left (by omega), List.getElem_take]
              rw [List.getElem_append_right (by omega), List.getElem_drop]
              simpa only [htake, heq, Nat.sub_self, Nat.add_zero] using hp j (by omega)
            · have hki : i + 1 ≤ k := by omega
              rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
                List.getElem_drop, List.getElem_drop]
              have he1 : j + 1 + (k - (i + 1)) = k + (j - i) := by omega
              have he2 : j + 1 + (k + 1 - (i + 1)) = k + (j - i) + 1 := by omega
              simpa only [htake, he1, he2] using hp (k + (j - i)) (by omega)
      obtain ⟨q', hq'c, hq'n, hq'0, hq'l⟩ := ih q (by rw [hqlen]; omega) hqchain
      refine ⟨q', hq'c, hq'n, ?_, ?_⟩
      · rw [hq'0]
        have h0 : q[0]? = p[0]? := by
          simp only [hq_def, List.getElem?_append, List.getElem?_take]
          simp [Nat.lt_add_one_iff, hi]
        exact h0
      · rw [hq'l]
        by_cases hjl : j + 1 < p.length
        · have hlast : q[q.length - 1]? = p[p.length - 1]? := by
            rw [hqlen]
            simp only [hq_def, List.getElem?_append, List.getElem?_take,
              List.getElem?_drop]
            have h1 : ¬ p.length - (j - i) - 1 < i + 1 := by omega
            simp [h1]
            congr 2
            omega
          exact hlast
        · have hjeq : j + 1 = p.length := by omega
          have hlast : q[q.length - 1]? = p[p.length - 1]? := by
            rw [hqlen]
            simp only [hq_def, List.getElem?_append, List.getElem?_take,
              List.getElem?_drop]
            have h1 : p.length - (j - i) - 1 < i + 1 := by omega
            simp [h1]
            have h2 : p.length - (j - i) - 1 = i := by omega
            rw [h2]
            have h3 : p.length - 1 = j := by omega
            rw [h3]
            simp [hi]
            rw [hpj]
            exact congrArg some heq
          exact hlast

/-- A reflexive-transitive reachability proof between distinct endpoints
contains a vertex-simple path of length at least two. -/
theorem exists_nodup_path_of_reflTransGen {α : Type*} [DecidableEq α] {r : α → α → Prop}
    {a b : α} (h : Relation.ReflTransGen r a b) (hab : a ≠ b) :
    ∃ q : List α, q.IsChain r ∧ q.Nodup ∧ 2 ≤ q.length ∧
      q[0]? = some a ∧ q[q.length - 1]? = some b := by
  obtain ⟨p, hpc, hp0, hpl⟩ := exists_isChain_of_reflTransGen h
  obtain ⟨q, hqc, hqn, hq0, hql⟩ := exists_nodup_isChain p hpc
  refine ⟨q, hqc, hqn, ?_, by rw [hq0, hp0], by rw [hql, hpl]⟩
  by_contra hlen
  push Not at hlen
  have hq0len : q.length = 0 ∨ q.length = 1 := by omega
  rcases hq0len with hq0len | hq1len
  · cases q with
    | nil => simp [hp0] at hq0
    | cons a l => simp at hq0len
  · have h1 : q[0]? = q[q.length - 1]? := by simp [hq1len]
    rw [hq0, hql] at h1
    rw [hp0, hpl] at h1
    exact hab (Option.some.inj h1)

end Matchings

end CLRS
