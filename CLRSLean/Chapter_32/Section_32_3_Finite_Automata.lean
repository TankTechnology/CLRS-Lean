import Mathlib
import CLRSLean.Chapter_32.Section_32_1_String_Model

/-! # Section 32.3 - String Matching with Finite Automata

CLRS §32.3: build a DFA that accepts exactly those texts ending with pattern `P`.

All proofs use a top-level `suffixGo` function with induction, avoiding
inline recursion.  The suffix-function (`σ`) is then defined as
`suffixGo P x (P.length)`.
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
  have h_assoc : (p ++ s) ++ [a] = t ++ [a] := by
    calc
      (p ++ s) ++ [a] = p ++ (s ++ [a]) := by simp
      _ = t ++ [a] := hp
  -- Drop the trailing [a] from both sides using dropLast
  have h_eq : p ++ s = t := by
    have hdrop := congrArg List.dropLast h_assoc
    simpa using hdrop
  exact ⟨p, h_eq⟩

lemma suffix_last_eq_of_append {s t : Text α} {a : α} (hSuf : isSuffix s (t ++ [a]))
    (hs_ne : s ≠ []) : s.getLast? = some a := by
  rcases hSuf with ⟨p, hp⟩
  have hlast : (t ++ [a]).getLast? = some a := by simp
  have := congrArg List.getLast? hp
  simp [hs_ne, hlast] at this ⊢
  exact this

/-- If 0 < k ≤ P.length and (P.take k).getLast? = some a, then
    P.take k = P.take (k-1) ++ [a]. -/
lemma take_k_eq_take_pred_cons_a {P : Text α} {k : ℕ} {a : α} (hk : 0 < k) (hkP : k ≤ P.length)
    (h_last : (P.take k).getLast? = some a) : P.take k = P.take (k-1) ++ [a] := by
  -- Use List.take_add_one to expand P.take k
  have : k = (k-1) + 1 := by omega
  rw [this, List.take_add_one]
  -- Goal: P.take (k-1) ++ P[k-1]?.toList = P.take (k-1) ++ [a]
  -- So we need P[k-1]?.toList = [a]
  -- i.e., P[k-1]? = some a
  have h_idx : k-1 < P.length := by omega
  -- From h_last, (P.take k).getLast? = some a, and k > 0
  -- Using List.getLast?_take: when k ≠ 0, it's P[k-1]?.or P.getLast?
  -- Since k-1 < P.length, P[k-1]? = some (P.get (k-1)), so .or = that
  have h_get : P[k-1]? = some a := by
    have h_getLast_take : (P.take k).getLast? = (P[k-1]?).or P.getLast? := by
      simp [List.getLast?_take, hk.ne']
    rw [h_getLast_take] at h_last
    -- h_last: (P[k-1]?).or P.getLast? = some a
    -- Since P[k-1]? = some _, .or returns that some
    have h_getIdx : P[k-1]? = some (P.get ⟨k-1, h_idx⟩) := by simp
    simp [h_getIdx] at h_last
    -- Now h_last: some (P.get ⟨k-1, h_idx⟩) = some a
    -- So P.get ⟨k-1, h_idx⟩ = a
    have h_eq_val : P.get ⟨k-1, h_idx⟩ = a := by
      simpa using h_last
    -- Hence P[k-1]? = some a
    simp [h_eq_val]
  rw [h_get]; simp

/-- If u++s = v++t and s is shorter than t, then s is a suffix of t. -/
lemma suffix_of_append_append {u s v t : Text α} (h_eq : u ++ s = v ++ t)
    (hs_lt : s.length < t.length) : isSuffix s t := by
  have hlen : (u ++ s).length = (v ++ t).length := by rw [h_eq]
  have hlen_sum : u.length + s.length = v.length + t.length := by
    simpa using hlen
  have huv : v.length < u.length := by omega
  have h_drop_t : (v ++ t).drop u.length = t.drop (u.length - v.length) := by
    rw [show u.length = v.length + (u.length - v.length) by omega]
    simp
  have h_eq_drop : s = t.drop (u.length - v.length) := by
    calc
      s = (u ++ s).drop u.length := by simp
      _ = (v ++ t).drop u.length := by rw [h_eq]
      _ = t.drop (u.length - v.length) := h_drop_t
  refine ⟨t.take (u.length - v.length), ?_⟩
  calc
    t.take (u.length - v.length) ++ s = t.take (u.length - v.length) ++ t.drop (u.length - v.length) := by rw [h_eq_drop]
    _ = t := by simp

/-- If s and t are both suffixes of u, and s is no longer than t, then s is a suffix of t. -/
lemma suffix_of_shorter_suffix {s t u : Text α} (hs : isSuffix s u) (ht : isSuffix t u)
    (hlen : s.length ≤ t.length) : isSuffix s t := by
  rcases hs with ⟨ps, hsu⟩
  rcases ht with ⟨pt, htu⟩
  -- hsu: ps ++ s = u, htu: pt ++ t = u
  -- So ps ++ s = pt ++ t
  have heq : ps ++ s = pt ++ t := calc
    ps ++ s = u := hsu
    _ = pt ++ t := by rw [htu]
  by_cases hlen_strict : s.length < t.length
  · exact suffix_of_append_append heq hlen_strict
  · have : s.length = t.length := by omega
    have heq' : s = t := by
      -- Prove s = t using the fact they're both suffixes with same length
      apply suffix_unique ⟨ps, hsu⟩ ⟨pt, htu⟩ this
    subst heq'
    exact isSuffix_self _

end SuffixLemmas

section SuffixFunction
variable {α : Type}

open Classical

/-- Top-level suffix-function iterator: largest k' ≤ k with P.take k' a suffix of x.
Iterates downward from k. -/
noncomputable def suffixGo (P x : Text α) (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if isSuffix (P.take k) x then k
  else suffixGo P x (k-1)
termination_by k

/-- `σ(x)` : largest k ≤ |P| with P.take k a suffix of x. -/
noncomputable def suffixFn (P x : Text α) : ℕ := suffixGo P x (P.length)

-- Three core lemmas about suffixGo, all proved by induction on k.

theorem suffixGo_le (P x : Text α) (k : ℕ) : suffixGo P x k ≤ k := by
  induction' k with k ih
  · simp [suffixGo]
  · rw [suffixGo]
    simp
    split
    · omega
    · -- ¬ isSuffix case: suffixGo P x k ≤ k+1
      omega

theorem suffixGo_satisfies (P x : Text α) (k : ℕ) : isSuffix (P.take (suffixGo P x k)) x := by
  induction' k with k ih
  · simp [suffixGo]
  · rw [suffixGo]
    simp
    split
    · -- isSuffix case: returns k+1
      rename_i hSuf
      -- Goal: isSuffix (P.take (k+1)) x = hSuf
      exact hSuf
    · -- ¬ isSuffix case: returns suffixGo P x k
      exact ih

theorem suffixGo_maximal (P x : Text α) (k j : ℕ) (hk : k ≤ j) (hSuf : isSuffix (P.take k) x) :
    k ≤ suffixGo P x j := by
  induction' j with j ih generalizing k
  · -- j = 0, so k = 0
    have : k = 0 := by omega
    subst this; unfold suffixGo; simp
  · -- j = j.succ
    unfold suffixGo
    simp
    split
    · -- isSuffix (P.take (j.succ)) x → suffixGo = j.succ
      omega
    · -- ¬ isSuffix (P.take (j.succ)) x → suffixGo = suffixGo P x j
      rename_i hNoSuf
      by_cases hkj : k = j.succ
      · subst hkj; exfalso; exact hNoSuf hSuf
      · have hk_le_j : k ≤ j := by omega
        exact ih hk_le_j hSuf

-- Now the suffixFn theorems are trivial corollaries.

theorem suffixFn_le_length (P x : Text α) : suffixFn P x ≤ P.length := by
  unfold suffixFn; apply suffixGo_le

theorem suffixFn_satisfies (P x : Text α) : isSuffix (P.take (suffixFn P x)) x := by
  unfold suffixFn; apply suffixGo_satisfies

theorem suffixFn_maximal (P x : Text α) (k : ℕ) (hk : k ≤ P.length)
    (hSuf : isSuffix (P.take k) x) : k ≤ suffixFn P x := by
  unfold suffixFn; apply suffixGo_maximal P x k (P.length) hk hSuf

theorem suffixFn_correct (P x : Text α) :
    isSuffix (P.take (suffixFn P x)) x ∧
    (∀ k, k ≤ P.length → isSuffix (P.take k) x → k ≤ suffixFn P x) :=
  And.intro (suffixFn_satisfies P x) (suffixFn_maximal P x)

theorem suffixFn_le_x_length (P x : Text α) : suffixFn P x ≤ x.length := by
  have hSuf := suffixFn_satisfies P x
  have hlen := isSuffix_length_le hSuf
  have h_take_len : (P.take (suffixFn P x)).length = suffixFn P x := by
    have hle := suffixFn_le_length P x
    simp [hle]
  omega

theorem suffixFn_self_prefix (P : Text α) (q : ℕ) (hq : q ≤ P.length) : suffixFn P (P.take q) = q := by
  apply le_antisymm
  · have := suffixFn_le_x_length P (P.take q)
    simp [hq] at this; exact this
  · apply suffixFn_maximal P (P.take q) q hq
    exact isSuffix_self _

@[simp] theorem suffixFn_nil_pattern (x : Text α) : suffixFn ([] : Text α) x = 0 := by
  unfold suffixFn suffixGo; simp

end SuffixFunction

section CLRSLemmas
variable {α : Type} (P : Text α)

/-- If P.take k is a suffix of x++[a] and 0 < k ≤ P.length,
    then P.take (k-1) is a suffix of x. -/
lemma suffix_pred_of_cons_a (x : Text α) (a : α) (k : ℕ) (hk : 0 < k) (hkP : k ≤ P.length)
    (hSuf : isSuffix (P.take k) (x ++ [a])) : isSuffix (P.take (k-1)) x := by
  have h_nonempty : P.take k ≠ [] := by
    intro hnil
    have : (P.take k).length = 0 := by simp [hnil]
    have : k = 0 := by simpa [hkP] using this
    omega
  have h_last : (P.take k).getLast? = some a :=
    suffix_last_eq_of_append hSuf h_nonempty
  have h_split : P.take k = P.take (k-1) ++ [a] :=
    take_k_eq_take_pred_cons_a hk hkP h_last
  rw [h_split] at hSuf
  exact suffix_dropLast hSuf

/-- CLRS Lemma 32.3: σ(xa) ≤ σ(x) + 1. -/
theorem suffixFn_cons_le_succ (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) ≤ suffixFn P x + 1 := by
  let σx := suffixFn P x
  let σxa := suffixFn P (x ++ [a])
  by_cases hσ : σxa ≤ σx + 1
  · exact hσ
  · -- Assume σxa > σx + 1, derive contradiction
    have hσxa_pos : 0 < σxa := by
      have : σx + 1 ≥ 1 := by omega
      omega
    have hσxa_le_m : σxa ≤ P.length := suffixFn_le_length P (x ++ [a])
    have hSuf : isSuffix (P.take σxa) (x ++ [a]) := suffixFn_satisfies P (x ++ [a])
    -- Then P.take (σxa-1) is a suffix of x
    have hSuf_pred : isSuffix (P.take (σxa - 1)) x :=
      suffix_pred_of_cons_a P x a σxa hσxa_pos hσxa_le_m hSuf
    -- By maximality of σx, σxa-1 ≤ σx
    have h_max : σxa - 1 ≤ σx := by
      have hle_pred : σxa - 1 ≤ P.length := by omega
      have hmax := suffixFn_maximal P x (σxa - 1) hle_pred hSuf_pred
      simpa [σx] using hmax
    -- But from our assumption σxa > σx + 1, we have σxa - 1 > σx, contradiction
    omega

/-- CLRS Lemma 32.4: σ(xa) = σ(P_q a) where q = σ(x). -/
theorem suffixFn_append_eq (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) = suffixFn P (P.take (suffixFn P x) ++ [a]) := by
  let q := suffixFn P x
  have hq_le : q ≤ P.length := suffixFn_le_length P x
  have hSuf_q : isSuffix (P.take q) x := suffixFn_satisfies P x
  apply le_antisymm
  · -- σ(xa) ≤ σ(P_q a)
    let k := suffixFn P (x ++ [a])
    have hk_le : k ≤ P.length := suffixFn_le_length P (x ++ [a])
    have hSuf_k : isSuffix (P.take k) (x ++ [a]) := suffixFn_satisfies P (x ++ [a])
    -- Lemma 32.3 gives k ≤ q+1
    have hk_le_qp1 : k ≤ q + 1 := by
      -- suffixFn_cons_le_succ gives the exact bound
      calc
        k = suffixFn P (x ++ [a]) := rfl
        _ ≤ suffixFn P x + 1 := suffixFn_cons_le_succ P x a
        _ = q + 1 := rfl
    by_cases hk0 : k = 0
    · subst hk0; omega
    · have hk_pos : 0 < k := by omega
      have hk_1_le_q : k - 1 ≤ q := by omega
      -- P.take k is suffix of x++[a], so P.take(k-1) is suffix of x
      have hSuf_pred : isSuffix (P.take (k-1)) x :=
        suffix_pred_of_cons_a P x a k hk_pos hk_le hSuf_k
      -- Both P.take(k-1) and P.take q are suffixes of x, with |P.take(k-1)| ≤ |P.take q|,
      -- so P.take(k-1) is a suffix of P.take q
      have hSuf_pred_q : isSuffix (P.take (k-1)) (P.take q) := by
        have h_take_q_suf_x : isSuffix (P.take q) x := hSuf_q
        have hlen_comp : (P.take (k-1)).length ≤ (P.take q).length := by
          have hk_1_le_m : k-1 ≤ P.length := by omega
          have hlen1 : (P.take (k-1)).length = k-1 := by simp [hk_1_le_m]
          have hlen2 : (P.take q).length = q := by simp [hq_le]
          rw [hlen1, hlen2]; omega
        exact suffix_of_shorter_suffix hSuf_pred h_take_q_suf_x hlen_comp
      -- Then P.take k = P.take(k-1) ++ [a] is a suffix of P.take q ++ [a]
      have hSuf_k_q_a : isSuffix (P.take k) (P.take q ++ [a]) := by
        -- Decompose P.take k = P.take (k-1) ++ [a]
        have h_nonempty : P.take k ≠ [] := by
          intro hnil
          have : (P.take k).length = 0 := by simp [hnil]
          have : k = 0 := by simpa [hk_le] using this
          omega
        have h_last : (P.take k).getLast? = some a :=
          suffix_last_eq_of_append hSuf_k h_nonempty
        have h_split : P.take k = P.take (k-1) ++ [a] :=
          take_k_eq_take_pred_cons_a hk_pos hk_le h_last
        rw [h_split]
        exact suffix_append_right hSuf_pred_q
      -- By maximality: k ≤ σ(P_q a)
      have hk_le_sigma : k ≤ suffixFn P (P.take q ++ [a]) :=
        suffixFn_maximal P (P.take q ++ [a]) k hk_le hSuf_k_q_a
      simpa [k] using hk_le_sigma
  · -- σ(P_q a) ≤ σ(xa)
    let r := suffixFn P (P.take q ++ [a])
    have hr_le : r ≤ P.length := suffixFn_le_length P (P.take q ++ [a])
    have hSuf_r : isSuffix (P.take r) (P.take q ++ [a]) := suffixFn_satisfies P (P.take q ++ [a])
    -- P.take q ++ [a] is a suffix of x ++ [a]
    have hSuf_q_a_xa : isSuffix (P.take q ++ [a]) (x ++ [a]) :=
      suffix_append_right hSuf_q
    -- By transitivity, P.take r is a suffix of x ++ [a]
    have hSuf_r_xa : isSuffix (P.take r) (x ++ [a]) :=
      suffix_trans hSuf_r hSuf_q_a_xa
    -- By maximality of σ(xa): r ≤ σ(xa)
    have hr_le_sigma : r ≤ suffixFn P (x ++ [a]) :=
      suffixFn_maximal P (x ++ [a]) r hr_le hSuf_r_xa
    simpa [r] using hr_le_sigma

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
  unfold delta; apply suffixFn_le_length

theorem deltaStar_valid (q : ℕ) (T : Text α) (hq : q ≤ P.length) : deltaStar P q T ≤ P.length := by
  induction' T with head tail ih generalizing q
  · unfold deltaStar; exact hq
  · unfold deltaStar
    simp
    have hq' : delta P q head ≤ P.length := delta_valid P q head hq
    apply ih hq'

@[simp] theorem deltaStar_append (q : ℕ) (T₁ T₂ : Text α) :
    deltaStar P q (T₁ ++ T₂) = deltaStar P (deltaStar P q T₁) T₂ := by
  simp [deltaStar]

@[simp] theorem deltaStar_nil (q : ℕ) : deltaStar P q [] = q := rfl

@[simp] theorem deltaStar_singleton (q : ℕ) (a : α) : deltaStar P q [a] = delta P q a := rfl

end Automaton

section Correctness
variable {α : Type} (P : Text α)

/-- Key invariant: δ*(q, T) = σ(P_q ++ T) for q ≤ |P|. -/
theorem deltaStar_eq_suffixFn_Pq (q : ℕ) (T : Text α) (hq : q ≤ P.length) :
    deltaStar P q T = suffixFn P (P.take q ++ T) := by
  induction' T with a tail ih generalizing q
  · -- T = []
    unfold deltaStar
    simp
    -- q = suffixFn P (P.take q)
    -- This is suffixFn_self_prefix
    exact (suffixFn_self_prefix P q hq).symm
  · -- T = a :: tail
    unfold deltaStar
    simp
    -- Goal: deltaStar P (delta P q a) tail = suffixFn P (P.take q ++ (a :: tail))
    -- delta P q a = suffixFn P (P.take q ++ [a])
    -- Let q' = delta P q a
    -- IH (with q'): deltaStar P q' tail = suffixFn P (P.take q' ++ tail)
    -- So LHS = suffixFn P (P.take q' ++ tail) where q' = suffixFn P (P.take q ++ [a])
    -- RHS = suffixFn P (P.take q ++ [a] ++ tail)
    -- We need: suffixFn P (P.take q' ++ tail) = suffixFn P (P.take q ++ [a] ++ tail)
    -- where q' = suffixFn P (P.take q ++ [a])
    -- By Lemma 32.4: suffixFn P (s ++ [a]) = suffixFn P (P.take (suffixFn P s) ++ [a])
    -- Here s = P.take q ++ tail ...? No, that's not exactly right.
    --
    -- Actually, let me prove a more general lemma:
    -- For any s t, suffixFn P (s ++ t) = suffixFn P (P.take (suffixFn P s) ++ t)
    -- This can be proved by induction on t using Lemma 32.4.
    -- Let me prove this as a helper lemma.

    -- Let q' = delta P q a = suffixFn P (P.take q ++ [a])
    have hq'_delta : delta P q a = suffixFn P (P.take q ++ [a]) := rfl
    rw [hq'_delta]
    let q' := suffixFn P (P.take q ++ [a])
    -- Need: deltaStar P q' tail = suffixFn P (P.take q ++ a :: tail)
    -- IH: deltaStar P q' tail = suffixFn P (P.take q' ++ tail)
    have hq'_le : q' ≤ P.length := suffixFn_le_length P (P.take q ++ [a])
    rw [ih hq'_le]
    -- Now: suffixFn P (P.take q' ++ tail) = suffixFn P (P.take q ++ [a] ++ tail)
    -- Let s := P.take q, t := [a] ++ tail
    -- Then: suffixFn P (s ++ t) = suffixFn P (P.take (suffixFn P s) ++ t) ... wait
    -- s = P.take q, suffixFn P s = q (by suffixFn_self_prefix)
    -- So P.take (suffixFn P s) = P.take q = s, trivial.
    -- But we need suffixFn P (s ++ [a] ++ tail) vs suffixFn P (P.take (suffixFn P (s++[a])) ++ tail)
    -- This is exactly the more general lemma I mentioned.
    --
    -- Lemma: ∀ s t, suffixFn P s ≤ P.length → suffixFn P (s ++ t) = suffixFn P (P.take (suffixFn P s) ++ t)
    -- Let me prove this inline by induction on t.
    
    -- Actually, it's simpler: use Lemma 32.4 iteratively.
    -- Lemma 32.4 says: suffixFn P (s ++ [a]) = suffixFn P (P.take (suffixFn P s) ++ [a])
    -- So: suffixFn P (P.take q ++ [a] ++ tail) 
    --   = suffixFn P ((P.take q ++ [a]) ++ tail)  (assoc)
    --   = suffixFn P (P.take q ++ ([a] ++ tail))
    -- If we can show that suffixFn P distributes over ++ in the right way, we're done.
    --
    -- OK, let me prove by induction on tail:
    -- Claim: suffixFn P (s ++ t) = suffixFn P (P.take (suffixFn P s) ++ t)
    -- for any s,t where s = P.take q for some q ≤ P.length
    --
    -- Base: t = []: suffixFn P (s ++ []) = suffixFn P s = suffixFn P (P.take (suffixFn P s) ++ [])
    --   = suffixFn P (P.take (suffixFn P s)) = suffixFn P s ... hmm this is circular
    --   Actually we need suffixFn_self_prefix: suffixFn P (P.take k) = k
    --   So P.take (suffixFn P s) is a prefix of length suffixFn P s...
    --   But suffixFn P (P.take (suffixFn P s)) = suffixFn P s (by suffixFn_self_prefix)
    --   So the base case is: suffixFn P s = suffixFn P (P.take (suffixFn P s)) = suffixFn P s ✓
    --
    -- Step: t = a :: tail'
    --   suffixFn P (s ++ a :: tail') = suffixFn P ((s ++ [a]) ++ tail')
    --   By IH (with s' = s ++ [a]): = suffixFn P (P.take (suffixFn P (s ++ [a])) ++ tail')
    --   By Lemma 32.4: suffixFn P (s ++ [a]) = suffixFn P (P.take (suffixFn P s) ++ [a])
    --   So = suffixFn P (P.take (suffixFn P (P.take (suffixFn P s) ++ [a])) ++ tail')
    --   Hmm, this is getting messy with nested P.take of suffixFn.
    --
    -- Let me try a different approach. The invariant is:
    -- deltaStar P q T = suffixFn P (P.take q ++ T)
    -- 
    -- We can prove this by a separate induction that uses the delta/δ definition directly:
    -- For the step case, we need:
    -- deltaStar P (suffixFn P (P.take q ++ [a])) tail = suffixFn P (P.take q ++ a :: tail)
    -- = suffixFn P ((P.take q ++ [a]) ++ tail)
    --
    -- This is exactly: deltaStar P (suffixFn P s') tail = suffixFn P (s' ++ tail)
    -- where s' = P.take q ++ [a]
    -- 
    -- So we need a lemma:
    -- Lemma: For any s, deltaStar P (suffixFn P s) T = suffixFn P (s ++ T)
    -- Wait, that's exactly what we're proving! So let me restructure.

    -- Let's prove the statement by induction on T directly, but use a stronger version
    -- where we generalize q. Let me try:

    -- Alternate proof: use the fact that δ(q,a) = σ(P_q a)
    -- And δ*(q, T) is the state after processing T starting from q.
    -- The invariant is: δ*(q, T) = σ(P_q T).
    --
    -- Base case T=[]: δ*(q, []) = q = σ(P_q) (since σ(P_q) = q by self_prefix)
    -- Inductive step T = a::tail:
    --   δ*(q, a::tail) = δ*(δ(q,a), tail) = δ*(σ(P_q a), tail)
    --   By IH: = σ(P_{σ(P_q a)} tail)
    --   By Lemma 32.4: σ((P_q) a tail) = σ(P_{σ(P_q a)} a tail) ... no
    --   Lemma 32.4: σ(s a) = σ(P_{σ(s)} a)
    --   So: σ(P_q a tail) = σ((P_q a) tail)
    --   And by IH: δ*(σ(P_q a), tail) = σ(P_{σ(P_q a)} tail)
    --   Wait, this is σ applied to the concatenation of P_{σ(P_q a)} and tail, not σ of the concatenation.

    -- Hmm, δ*(q', tail) = σ(P_q' tail) by IH. 
    -- So δ*(σ(P_q a), tail) = σ(P_{σ(P_q a)} tail)
    -- But we want σ((P_q a) tail) = σ(P_q ++ [a] ++ tail)
    -- These are not obviously equal.

    -- The issue is that σ is a function on strings, not a state transformer.
    -- Let me think differently.

    -- Actually, the key property is the following identity from CLRS:
    -- For any string w and character a: σ(wa) = σ(P_{σ(w)} a)
    -- This can be iterated: for any string T,
    -- σ(w T) = σ(P_{σ(w)} T)
    -- Let me state this as a lemma and prove it.
    sorry
  sorry

theorem deltaStar_eq_suffixFn (T : Text α) : deltaStar P 0 T = suffixFn P T := by
  -- Apply the above with q=0, noting P.take 0 = []
  have h := deltaStar_eq_suffixFn_Pq P 0 T (by omega)
  simp at h
  exact h

/-- The DFA accepts T iff P is a suffix of T. -/
theorem accepts_iff_isSuffix (T : Text α) : accepts P T ↔ isSuffix P T := by
  constructor
  · intro h; unfold accepts at h
    rw [deltaStar_eq_suffixFn P T] at h
    have h_satisfies := suffixFn_satisfies P T
    rw [h] at h_satisfies
    simpa using h_satisfies
  · intro h; unfold accepts
    rw [deltaStar_eq_suffixFn P T]
    apply le_antisymm
    · exact suffixFn_le_length P T
    · have hlen : P.length ≤ P.length := le_rfl
      have h_suf : isSuffix (P.take (P.length)) T := by simpa using h
      exact suffixFn_maximal P T (P.length) hlen h_suf

theorem accepts_empty_pattern (T : Text α) : accepts ([] : Text α) T := by
  unfold accepts
  -- For empty pattern, delta returns 0 always and deltaStar stays 0
  simp [delta, deltaStar, suffixFn_nil_pattern]

theorem not_accepts_when_text_shorter (T : Text α) (hP : P ≠ []) (hLT : T.length < P.length) :
    ¬ accepts P T := by
  intro h_accepts
  rcases (accepts_iff_isSuffix P T).mp h_accepts with ⟨u, hu⟩
  have hlen : T.length = u.length + P.length := by
    simpa using congrArg List.length hu
  omega

end Correctness

end Chapter32
end CLRS
