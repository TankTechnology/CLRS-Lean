import Mathlib
import CLRSLean.Chapter_32.Section_32_1_String_Model

/-! # Section 32.3 - String Matching with Finite Automata

CLRS §32.3: build a DFA that accepts exactly those texts ending with pattern `P`.

## Key theorems
- CLRS Lemma 32.3: `σ(xa) ≤ σ(x) + 1`
- CLRS Lemma 32.4: `σ(xa) = σ(P_σ(x) a)`
- Correctness: the DFA with `δ(q,a) = σ(P_q ++ [a])` accepts `T` iff `P` is a suffix of `T`.

Status: definitions and theorem statements complete; proofs deferred.
-/

namespace CLRS
namespace Chapter32

section SuffixLemmas
variable {α : Type}

lemma isSuffix_eq_drop {s t : Text α} (h : isSuffix s t) : s = t.drop (t.length - s.length) := by
  rcases h with ⟨p, hp⟩
  have hlen : p.length + s.length = t.length := by
    simpa [List.length_append] using congrArg List.length hp
  have h_sub : t.length - s.length = p.length := by omega
  calc
    s = (p ++ s).drop p.length := by simp
    _ = t.drop p.length := by rw [hp]
    _ = t.drop (t.length - s.length) := by rw [h_sub]

lemma suffix_unique {s s' t : Text α} (h : isSuffix s t) (h' : isSuffix s' t)
    (hlen : s.length = s'.length) : s = s' := by
  rw [isSuffix_eq_drop h, isSuffix_eq_drop h', hlen]

lemma suffix_append_right {s t u : Text α} (h : isSuffix s t) : isSuffix (s ++ u) (t ++ u) := by
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  calc
    p ++ (s ++ u) = (p ++ s) ++ u := by rw [List.append_assoc]
    _ = t ++ u := by rw [hp]

lemma suffix_trans {r s t : Text α} (hrs : isSuffix r s) (hst : isSuffix s t) :
    isSuffix r t := by
  rcases hrs with ⟨p, hp⟩
  rcases hst with ⟨q, hq⟩
  refine ⟨q ++ p, ?_⟩
  calc
    (q ++ p) ++ r = q ++ (p ++ r) := by rw [List.append_assoc]
    _ = q ++ s := by rw [hp]
    _ = t := hq

lemma suffix_dropLast {s t : Text α} {a : α} (h : isSuffix (s ++ [a]) (t ++ [a])) :
    isSuffix s t := by
  rcases h with ⟨p, hp⟩
  -- hp: p ++ (s ++ [a]) = t ++ [a]
  -- rewrite associativity: (p ++ s) ++ [a] = t ++ [a]
  -- take dropLast of both sides to cancel the trailing [a]
  have h_drop := congrArg (·.dropLast) hp
  -- simplify dropLast on both sides
  have h_left : (p ++ (s ++ [a])).dropLast = p ++ s := by simp
  have h_right : (t ++ [a]).dropLast = t := by simp
  rw [h_left, h_right] at h_drop
  exact ⟨p, h_drop⟩

lemma suffix_last_eq_of_append {s t : Text α} {a : α} (hSuf : isSuffix s (t ++ [a]))
    (hs_ne : s ≠ []) : s.getLast? = some a := by
  rcases hSuf with ⟨p, hp⟩
  have hlast : (t ++ [a]).getLast? = some a := by simp
  have := congrArg List.getLast? hp
  simp [hs_ne, hlast] at this ⊢
  exact this

lemma dropLast_take_eq_take_pred {P : Text α} {k : ℕ} (hk : 0 < k) (hkP : k ≤ P.length) :
    (P.take k).dropLast = P.take (k-1) := by
  have h_len : (P.take k).length = k := by simp [hkP]
  calc
    (P.take k).dropLast = (P.take k).take ((P.take k).length - 1) := by
      rw [List.dropLast_eq_take]
    _ = (P.take k).take (k - 1) := by rw [h_len]
    _ = P.take (k - 1) := by
      rw [List.take_take, min_eq_left (by omega : k - 1 ≤ k)]

lemma take_split_last_eq {P : Text α} {k : ℕ} {a : α} (hk : 0 < k) (hkP : k ≤ P.length)
    (h_last : (P.take k).getLast? = some a) : P.take k = P.take (k-1) ++ [a] := by
  rcases (List.getLast?_eq_some_iff.mp h_last) with ⟨ys, hys⟩
  -- hys: P.take k = ys ++ [a]
  have h_len_take : (P.take k).length = k := by
    simp [hkP]
  have h_len_ys : ys.length = k - 1 := by
    rw [hys] at h_len_take
    simp at h_len_take
    omega
  have h_ys_eq_take : ys = P.take (k-1) := by
    calc
      ys = (ys ++ [a]).take ys.length := by simp
      _ = (P.take k).take ys.length := by rw [hys]
      _ = (P.take k).take (k-1) := by rw [h_len_ys]
      _ = P.take (min (k-1) k) := by rw [List.take_take]
      _ = P.take (k-1) := by rw [min_eq_left (by omega)]
  calc
    P.take k = ys ++ [a] := hys
    _ = P.take (k-1) ++ [a] := by rw [h_ys_eq_take]

lemma suffix_of_append_append {u s v t : Text α} (h_eq : u ++ s = v ++ t)
    (hs_lt : s.length < t.length) : isSuffix s t := by
  have h_len_s_lt : s.length ≤ (v ++ t).length := by
    have : s.length ≤ (u ++ s).length := by simp
    rw [h_eq] at this
    exact this
  have h_drop := congrArg (fun l => l.drop (l.length - s.length)) h_eq
  -- LHS simplifies to s, RHS simplifies to t.drop (t.length - s.length)
  have h_left : (u ++ s).drop ((u ++ s).length - s.length) = s := by
    simp
  have h_right : (v ++ t).drop ((v ++ t).length - s.length) = t.drop (t.length - s.length) := by
    have h_len_vt : (v ++ t).length = v.length + t.length := by simp
    have h_ge : v.length ≤ v.length + t.length - s.length := by omega
    rw [h_len_vt, List.drop_append]
    rw [List.drop_eq_nil_of_le h_ge, List.nil_append]
    have h_sub : (v.length + t.length - s.length) - v.length = t.length - s.length := by omega
    rw [h_sub]
  rw [h_left, h_right] at h_drop
  -- h_drop: s = t.drop (t.length - s.length)
  refine ⟨t.take (t.length - s.length), ?_⟩
  calc
    t.take (t.length - s.length) ++ s = t.take (t.length - s.length) ++ t.drop (t.length - s.length) := by
      nth_rw 2 [h_drop]
    _ = t := by rw [List.take_append_drop]

end SuffixLemmas

open Classical

/-- suffixGo: largest k' ≤ k with P.take k' a suffix of x. -/
noncomputable def suffixGo {α : Type} (P : Text α) (x : Text α) : ℕ → ℕ
  | 0 => 0
  | k+1 =>
    if isSuffix (P.take (k+1)) x then k+1
    else suffixGo P x k

lemma suffixGo_le {α : Type} (P : Text α) (x : Text α) (k : ℕ) : suffixGo P x k ≤ k := by
  induction' k with m ih
  · rfl
  · unfold suffixGo
    split
    · rfl
    · omega

lemma suffixGo_satisfies {α : Type} (P : Text α) (x : Text α) (k : ℕ) :
    isSuffix (P.take (suffixGo P x k)) x := by
  induction' k with m ih
  · simp [suffixGo, isSuffix_empty]
  · unfold suffixGo
    split
    · rename_i h; exact h
    · exact ih

lemma suffixGo_maximal {α : Type} (P : Text α) (x : Text α) (k j : ℕ) (hkj : k ≤ j)
    (hSuf : isSuffix (P.take k) x) : k ≤ suffixGo P x j := by
  induction' j with m ih generalizing k
  · -- j = 0, so k = 0
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  · unfold suffixGo
    split
    · -- P.take (m+1) is a suffix → suffixGo returns m+1
      omega
    · -- P.take (m+1) is NOT a suffix → suffixGo returns suffixGo P x m
      have hkm : k ≤ m := by
        by_contra! h
        have hk_m1 : k = m + 1 := by omega
        subst hk_m1
        exact ‹¬ isSuffix (P.take (m+1)) x› hSuf
      exact ih k hkm hSuf

section SuffixFunction
variable {α : Type} (P : Text α)

open Classical

/-- σ(x): largest k ≤ |P| with P.take k a suffix of x. -/
noncomputable def suffixFn (x : Text α) : ℕ := suffixGo P x (P.length)

theorem suffixFn_le_length (x : Text α) : suffixFn P x ≤ P.length :=
  suffixGo_le P x (P.length)

theorem suffixFn_satisfies (x : Text α) : isSuffix (P.take (suffixFn P x)) x :=
  suffixGo_satisfies P x (P.length)

theorem suffixFn_maximal (x : Text α) (k : ℕ) (hk : k ≤ P.length)
    (hSuf : isSuffix (P.take k) x) : k ≤ suffixFn P x :=
  suffixGo_maximal P x k (P.length) hk hSuf

theorem suffixFn_correct (x : Text α) :
    isSuffix (P.take (suffixFn P x)) x ∧
    (∀ k, k ≤ P.length → isSuffix (P.take k) x → k ≤ suffixFn P x) :=
  And.intro (suffixFn_satisfies P x) (suffixFn_maximal P x)

theorem suffixFn_le_x_length (x : Text α) : suffixFn P x ≤ x.length := by
  have h := isSuffix_length_le (suffixFn_satisfies P x)
  simp [suffixFn_le_length P x] at h
  exact h

theorem suffixFn_self_prefix (q : ℕ) (hq : q ≤ P.length) : suffixFn P (P.take q) = q := by
  apply le_antisymm
  · have h := isSuffix_length_le (suffixFn_satisfies P (P.take q))
    simp [suffixFn_le_length P (P.take q), hq] at h
    exact h
  · apply suffixFn_maximal P (P.take q) q hq
    exact isSuffix_self _

@[simp] theorem suffixFn_nil_pattern (x : Text α) : suffixFn ([] : Text α) x = 0 := by
  simp [suffixFn, suffixGo]

end SuffixFunction

section CLRSLemmas
variable {α : Type} (P : Text α)

/-- CLRS Lemma 32.3: `σ(xa) ≤ σ(x) + 1`. -/
theorem suffixFn_cons_le_succ (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) ≤ suffixFn P x + 1 := by
  set k := suffixFn P (x ++ [a]) with hk
  set q := suffixFn P x with hq
  by_contra! h  -- h: q + 1 < k
  have hk_pos : 0 < k := by omega
  have hk_le_P : k ≤ P.length := suffixFn_le_length P (x ++ [a])
  -- By suffixFn_satisfies, P.take k is a suffix of x ++ [a]
  have h_suf : isSuffix (P.take k) (x ++ [a]) := suffixFn_satisfies P (x ++ [a])
  -- Since k > 0, P.take k ≠ [], so its last element is a
  have hne : P.take k ≠ [] := by
    intro h_empty
    have hlen : (P.take k).length = 0 := by simpa [h_empty]
    have hlen' : (P.take k).length = k := by simp [hk_le_P]
    rw [hlen'] at hlen
    omega
  have h_last : (P.take k).getLast? = some a :=
    suffix_last_eq_of_append h_suf hne
  -- Split P.take k = P.take (k-1) ++ [a]
  have h_split : P.take k = P.take (k-1) ++ [a] :=
    take_split_last_eq hk_pos hk_le_P h_last
  -- By suffix_dropLast, P.take (k-1) is a suffix of x
  have h_suf_pred : isSuffix (P.take (k-1)) x := by
    rw [h_split] at h_suf
    exact suffix_dropLast h_suf
  -- But then k-1 ≤ σ(x) by maximality, contradicting q+1 < k
  have hk1_le_q : k - 1 ≤ q :=
    suffixFn_maximal P x (k-1) (by
      -- need k-1 ≤ P.length
      omega
    ) h_suf_pred
  omega

/-- CLRS Lemma 32.4: `σ(xa) = σ(P_q a)` where `q = σ(x)`. -/
theorem suffixFn_append_eq (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) = suffixFn P (P.take (suffixFn P x) ++ [a]) := by
  set q := suffixFn P x with hq
  set r := suffixFn P (x ++ [a]) with hr
  set r' := suffixFn P (P.take q ++ [a]) with hr'
  have hq_le_P : q ≤ P.length := suffixFn_le_length P x
  have hr_le_P : r ≤ P.length := suffixFn_le_length P (x ++ [a])
  have hr'_le_P : r' ≤ P.length := suffixFn_le_length P (P.take q ++ [a])
  have hq_suf : isSuffix (P.take q) x := suffixFn_satisfies P x
  have hr_suf : isSuffix (P.take r) (x ++ [a]) := suffixFn_satisfies P (x ++ [a])
  have hr'_suf : isSuffix (P.take r') (P.take q ++ [a]) := suffixFn_satisfies P (P.take q ++ [a])
  have hr_le_q1 : r ≤ q + 1 := suffixFn_cons_le_succ P x a
  rcases hq_suf with ⟨u, hu⟩
  -- hu: u ++ P.take q = x
  apply le_antisymm
  · -- r ≤ r'
    -- Need: isSuffix (P.take r) (P.take q ++ [a])
    rcases hr_suf with ⟨v, hv⟩
    -- hv: v ++ P.take r = x ++ [a] = u ++ P.take q ++ [a]
    rw [← hu] at hv
    -- hv: v ++ P.take r = u ++ P.take q ++ [a]
    have h_suf_r : isSuffix (P.take r) (P.take q ++ [a]) := by
      rcases Nat.lt_or_eq_of_le hr_le_q1 with (h_lt | h_eq)
      · -- r < q + 1
        have h_len_lt : (P.take r).length < (P.take q ++ [a]).length := by
          have h1 : (P.take r).length = r := by simp [hr_le_P]
          have h2 : (P.take q ++ [a]).length = q + 1 := by simp [hq_le_P]
          rw [h1, h2]
          omega
        have hv' : v ++ P.take r = u ++ (P.take q ++ [a]) := by
          simpa [List.append_assoc] using hv
        exact suffix_of_append_append hv' h_len_lt
      · -- r = q + 1
        have h_len_eq : (P.take r).length = (P.take q ++ [a]).length := by
          have h1 : (P.take r).length = r := by simp [hr_le_P]
          have h2 : (P.take q ++ [a]).length = q + 1 := by simp [hq_le_P]
          rw [h1, h2, h_eq]
        -- v ++ P.take r = u ++ P.take q ++ [a] and lengths match, so drop v.length
        have h_v_len : v.length = u.length := by
          have h_total := congrArg List.length hv
          simp [h_len_eq] at h_total
          omega
        have h_eq_lists : P.take r = P.take q ++ [a] := by
          have h_drop := congrArg (fun l => l.drop v.length) hv
          simp [h_v_len] at h_drop
          exact h_drop
        -- From equality, it's trivially a suffix
        rw [h_eq_lists]
        exact isSuffix_self _
    exact suffixFn_maximal P (P.take q ++ [a]) r hr_le_P h_suf_r
  · -- r' ≤ r
    -- Need: isSuffix (P.take r') (x ++ [a])
    rcases hr'_suf with ⟨w, hw⟩
    -- hw: w ++ P.take r' = P.take q ++ [a]
    -- Then u ++ w ++ P.take r' = u ++ P.take q ++ [a] = x ++ [a]
    have h_suf_r' : isSuffix (P.take r') (x ++ [a]) := by
      refine ⟨u ++ w, ?_⟩
      calc
        (u ++ w) ++ P.take r' = u ++ (w ++ P.take r') := by rw [List.append_assoc]
        _ = u ++ (P.take q ++ [a]) := by rw [hw]
        _ = (u ++ P.take q) ++ [a] := by rw [List.append_assoc]
        _ = x ++ [a] := by rw [hu]
    exact suffixFn_maximal P (x ++ [a]) r' hr'_le_P h_suf_r'

end CLRSLemmas

section Automaton
variable {α : Type} (P : Text α)

noncomputable def delta (q : ℕ) (a : α) : ℕ := suffixFn P ((P.take q) ++ [a])
noncomputable def deltaStar (q : ℕ) : Text α → ℕ := List.foldl (delta P) q
noncomputable def accepts (T : Text α) : Prop := deltaStar P 0 T = P.length
def states : Finset ℕ := Finset.range (P.length + 1)
def initialState : ℕ := 0
def isAcceptingState (q : ℕ) : Prop := q = P.length

theorem delta_valid (q : ℕ) (a : α) (hq : q ≤ P.length) : delta P q a ≤ P.length := by
  unfold delta
  exact suffixFn_le_length P ((P.take q) ++ [a])

theorem deltaStar_valid (q : ℕ) (T : Text α) (hq : q ≤ P.length) : deltaStar P q T ≤ P.length := by
  induction' T with a T ih generalizing q
  · exact hq
  · unfold deltaStar; simp
    apply ih
    exact delta_valid P q a hq

@[simp] theorem deltaStar_append (q : ℕ) (T₁ T₂ : Text α) :
    deltaStar P q (T₁ ++ T₂) = deltaStar P (deltaStar P q T₁) T₂ := by
  simp [deltaStar]

@[simp] theorem deltaStar_nil (q : ℕ) : deltaStar P q [] = q := rfl

@[simp] theorem deltaStar_singleton (q : ℕ) (a : α) : deltaStar P q [a] = delta P q a := rfl

end Automaton

section Correctness
variable {α : Type} (P : Text α)

theorem deltaStar_eq_suffixFn_Pq (q : ℕ) (T : Text α) (hq : q ≤ P.length) :
    deltaStar P q T = suffixFn P (P.take q ++ T) := by
  induction' T using List.reverseRecOn with T a ih
  · -- T = []
    simp [deltaStar, suffixFn_self_prefix P q hq]
  · -- T = T ++ [a]
    rw [deltaStar_append P q T [a], deltaStar_singleton P (deltaStar P q T) a, delta]
    rw [ih]
    rw [← suffixFn_append_eq P (P.take q ++ T) a]
    simp [List.append_assoc]

theorem deltaStar_eq_suffixFn (T : Text α) : deltaStar P 0 T = suffixFn P T := by
  simpa using deltaStar_eq_suffixFn_Pq P 0 T (by simp)

/-- The DFA accepts `T` iff `P` is a suffix of `T`. -/
theorem accepts_iff_isSuffix (T : Text α) : accepts P T ↔ isSuffix P T := by
  constructor
  · intro h
    unfold accepts at h
    rw [deltaStar_eq_suffixFn P T] at h
    have h_satisfies : isSuffix (P.take (suffixFn P T)) T := suffixFn_satisfies P T
    rw [h] at h_satisfies
    simpa using h_satisfies
  · intro h
    have hP_take : P.take P.length = P := by simp
    have hlen : P.length ≤ P.length := le_refl _
    have h_max : P.length ≤ suffixFn P T :=
      suffixFn_maximal P T P.length hlen (by simpa [hP_take] using h)
    have h_le : suffixFn P T ≤ P.length := suffixFn_le_length P T
    have h_eq : suffixFn P T = P.length := by omega
    unfold accepts
    rw [deltaStar_eq_suffixFn P T, h_eq]

theorem accepts_empty_pattern (T : Text α) : accepts ([] : Text α) T := by
  simp [accepts, deltaStar_eq_suffixFn, suffixFn_nil_pattern]

theorem not_accepts_when_text_shorter (T : Text α) (hP : P ≠ []) (hLT : T.length < P.length) :
    ¬ accepts P T := by
  intro h_acc
  have h_suf : isSuffix P T := (accepts_iff_isSuffix P T).mp h_acc
  have h_len : P.length ≤ T.length := isSuffix_length_le h_suf
  omega

end Correctness

end Chapter32
end CLRS
