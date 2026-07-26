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
  have h_eq : (p ++ s) ++ [a] = t ++ [a] := by simpa [List.append_assoc] using hp
  have h_init : p ++ s = t := by
    have := congrArg (fun (l : Text α) => l.take (l.length - 1)) h_eq
    simp at this
    exact this
  exact ⟨p, h_init⟩

lemma suffix_last_eq_of_append {s t : Text α} {a : α} (hSuf : isSuffix s (t ++ [a]))
    (hs_ne : s ≠ []) : s.getLast? = some a := by
  rcases hSuf with ⟨p, hp⟩
  have hlast : (t ++ [a]).getLast? = some a := by simp
  have := congrArg List.getLast? hp
  simp [hs_ne, hlast] at this ⊢
  exact this

lemma dropLast_take_eq_take_pred {P : Text α} {k : ℕ} (hk : 0 < k) (hkP : k ≤ P.length) :
    (P.take k).dropLast = P.take (k-1) := by
  have hpos : k-1 < P.length := by omega
  have htake_succ : P.take k = P.take (k-1) ++ [P.get ⟨k-1, hpos⟩] := by
    have hk_eq : k = ((k-1) : ℕ).succ := by omega
    rw [hk_eq, List.take_succ]
    simp [hpos]
  rw [htake_succ]
  simp

lemma take_split_last_eq {P : Text α} {k : ℕ} {a : α} (hk : 0 < k) (hkP : k ≤ P.length)
    (h_last : (P.take k).getLast? = some a) : P.take k = P.take (k-1) ++ [a] := by
  have hne : P.take k ≠ [] := by
    intro h
    have hlen : (P.take k).length = 0 := by simp [h]
    have hlen_take : (P.take k).length = k := List.length_take_of_le hkP
    rw [hlen_take] at hlen
    omega
  have hgetLast : (P.take k).getLast hne = a := by
    have := (List.getLast?_eq_some_iff).mp h_last
    rcases this with ⟨hne', h⟩
    exact h
  have hsplit : P.take k = (P.take k).dropLast ++ [a] := by
    rw [List.dropLast_append_getLast hne, hgetLast]
  rw [hsplit, dropLast_take_eq_take_pred hk hkP]

lemma suffix_of_append_append {u s v t : Text α} (h_eq : u ++ s = v ++ t)
    (hs_lt : s.length < t.length) : isSuffix s t := by
  rcases List.append_eq_append_iff.mp h_eq with (⟨w, hv_eq, hrest⟩ | ⟨w, hu_eq, hrest⟩)
  · -- v = u ++ w ∧ s = w ++ t
    have hlen := congrArg List.length hrest
    simp [List.length_append] at hlen
    omega
  · -- u = v ++ w ∧ t = w ++ s
    exact ⟨w, hrest.symm⟩

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
  · have : k = 0 := by omega
    subst this; rfl
  · unfold suffixGo
    split
    · rename_i h; omega
    · rename_i h
      by_cases hkm : k ≤ m
      · apply ih hkm hSuf
      · have : k = m+1 := by omega
        subst this
        exfalso; exact h hSuf

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
  have hSuf := suffixFn_satisfies P x
  have hlen := isSuffix_length_le hSuf
  have h_take_len : (P.take (suffixFn P x)).length = suffixFn P x :=
    List.length_take_of_le (suffixFn_le_length P x)
  rw [h_take_len] at hlen
  exact hlen

theorem suffixFn_self_prefix (q : ℕ) (hq : q ≤ P.length) : suffixFn P (P.take q) = q := by
  apply le_antisymm
  · have hSuf := suffixFn_satisfies P (P.take q)
    have hlen := isSuffix_length_le hSuf
    have h_take1 : (P.take (suffixFn P (P.take q))).length = suffixFn P (P.take q) :=
      List.length_take_of_le (suffixFn_le_length P (P.take q))
    have h_take2 : (P.take q).length = q := List.length_take_of_le hq
    rw [h_take1, h_take2] at hlen
    exact hlen
  · apply suffixFn_maximal P (P.take q) q hq
    exact isSuffix_self (P.take q)

@[simp] theorem suffixFn_nil_pattern (x : Text α) : suffixFn ([] : Text α) x = 0 := by
  simp [suffixFn, suffixGo]

end SuffixFunction

section CLRSLemmas
variable {α : Type} (P : Text α)

/-- CLRS Lemma 32.3: `σ(xa) ≤ σ(x) + 1`. -/
theorem suffixFn_cons_le_succ (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) ≤ suffixFn P x + 1 := by
  set k := suffixFn P x
  set q := suffixFn P (x ++ [a])
  by_cases hqle : q ≤ k + 1
  · exact hqle
  · -- q > k + 1, derive contradiction
    have hq_gt : k + 1 < q := by omega
    have hq_pos : 0 < q := by omega
    have hSuf_q := suffixFn_satisfies P (x ++ [a])
    -- hSuf_q : isSuffix (P.take q) (x ++ [a])
    have hq_le_P : q ≤ P.length := suffixFn_le_length P (x ++ [a])
    have hne_q : P.take q ≠ [] := by
      intro h
      have hlen : (P.take q).length = 0 := by simp [h]
      have hlen_take : (P.take q).length = q := List.length_take_of_le hq_le_P
      rw [hlen_take] at hlen
      omega
    have h_last_a : (P.take q).getLast? = some a :=
      suffix_last_eq_of_append hSuf_q hne_q
    have h_split : P.take q = P.take (q-1) ++ [a] :=
      take_split_last_eq hq_pos hq_le_P h_last_a
    -- Now we have: isSuffix (P.take (q-1) ++ [a]) (x ++ [a])
    rw [h_split] at hSuf_q
    -- By suffix_dropLast:
    have hSuf_qminus1 : isSuffix (P.take (q-1)) x := suffix_dropLast hSuf_q
    -- So σ(x) ≥ q-1
    have h_qminus1_le_P : q-1 ≤ P.length := by omega
    have hk_le_qminus1 : q-1 ≤ k :=
      suffixFn_maximal P x (q-1) h_qminus1_le_P hSuf_qminus1
    omega

/-- CLRS Lemma 32.4: `σ(xa) = σ(P_q a)` where `q = σ(x)`. -/
theorem suffixFn_append_eq (x : Text α) (a : α) :
    suffixFn P (x ++ [a]) = suffixFn P (P.take (suffixFn P x) ++ [a]) := by
  set q := suffixFn P x
  have hqP : q ≤ P.length := suffixFn_le_length P x
  have hSuf_q : isSuffix (P.take q) x := suffixFn_satisfies P x
  
  -- Prove both directions using suffixFn_maximal
  apply le_antisymm
  · -- suffixFn P (x ++ [a]) ≤ suffixFn P (P.take q ++ [a])
    set r := suffixFn P (x ++ [a])
    have hrP : r ≤ P.length := suffixFn_le_length P (x ++ [a])
    have hSuf_r : isSuffix (P.take r) (x ++ [a]) := suffixFn_satisfies P (x ++ [a])
    have hr_le_q1 : r ≤ q + 1 := suffixFn_cons_le_succ P x a
    -- Need to show P.take r is a suffix of P.take q ++ [a]
    -- Then by suffixFn_maximal, r ≤ suffixFn P (P.take q ++ [a])
    by_cases hr_zero : r = 0
    · subst hr_zero; simp [suffixFn]
    · have hr_pos : 0 < r := by omega
      have hne_r : P.take r ≠ [] := by
        intro h; have hlen : (P.take r).length = 0 := by simp [h]
        have hlen_take : (P.take r).length = r := List.length_take_of_le hrP
        rw [hlen_take] at hlen; omega
      have h_last_a : (P.take r).getLast? = some a :=
        suffix_last_eq_of_append hSuf_r hne_r
      have h_split : P.take r = P.take (r-1) ++ [a] :=
        take_split_last_eq hr_pos hrP h_last_a
      rw [h_split] at hSuf_r
      -- isSuffix (P.take (r-1) ++ [a]) (x ++ [a])
      -- By suffix_dropLast: isSuffix (P.take (r-1)) x
      have hSuf_rm1_x : isSuffix (P.take (r-1)) x := suffix_dropLast hSuf_r
      -- Then by maximality of q: r-1 ≤ q
      have hrm1_le_P : r-1 ≤ P.length := by omega
      have hrm1_le_q : r-1 ≤ q :=
        suffixFn_maximal P x (r-1) hrm1_le_P hSuf_rm1_x
      -- Now we need: isSuffix (P.take r) (P.take q ++ [a])
      -- Key lemma: since r-1 ≤ q and both P.take (r-1) and P.take q are suffixes of x,
      -- P.take (r-1) must be a suffix of P.take q (CSL exercise 32.3-1).
      have h_suf_rm1_q : isSuffix (P.take (r-1)) (P.take q) := by
        rcases hSuf_q with ⟨y, hy⟩
        rcases hSuf_rm1_x with ⟨z, hz⟩
        have h_eq : y ++ P.take q = z ++ P.take (r-1) := by rw [hy, hz]
        rcases List.append_eq_append_iff.mp h_eq with (⟨w, hzw, hrest⟩ | ⟨w, hyw, hrest⟩)
        · -- z = y ++ w ∧ P.take q = w ++ P.take (r-1)
          exact ⟨w, hrest.symm⟩
        · -- y = z ++ w ∧ P.take (r-1) = w ++ P.take q
          have hlen := congrArg List.length hrest
          simp [List.length_append, List.length_take_of_le hqP, List.length_take_of_le hrm1_le_P] at hlen
          have : r-1 = q := by omega
          subst this
          exact isSuffix_self _
      rcases h_suf_rm1_q with ⟨u, hu⟩
      rw [h_split, hu]
      -- P.take r = P.take (r-1) ++ [a], P.take q = u ++ P.take (r-1)
      -- Then P.take q ++ [a] = u ++ P.take (r-1) ++ [a] = u ++ P.take r
      exact ⟨u, by simp [List.append_assoc]⟩
  · -- suffixFn P (P.take q ++ [a]) ≤ suffixFn P (x ++ [a])
    set s := suffixFn P (P.take q ++ [a])
    have hsP : s ≤ P.length := suffixFn_le_length P (P.take q ++ [a])
    have hSuf_s : isSuffix (P.take s) (P.take q ++ [a]) :=
      suffixFn_satisfies P (P.take q ++ [a])
    -- Since P.take q is a suffix of x, we have P.take q ++ [a] is a suffix of x ++ [a]
    have hSuf_q_a : isSuffix (P.take q ++ [a]) (x ++ [a]) :=
      suffix_append_right hSuf_q
    -- Then by transitivity, P.take s is a suffix of x ++ [a]
    have hSuf_s_xa : isSuffix (P.take s) (x ++ [a]) :=
      suffix_trans hSuf_s hSuf_q_a
    -- Then by suffixFn_maximal, s ≤ suffixFn P (x ++ [a])
    exact suffixFn_maximal P (x ++ [a]) s hsP hSuf_s_xa

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
  induction' T with a T' ih generalizing q
  · simp [deltaStar, hq]
  · rw [deltaStar, List.foldl_cons]
    apply ih (delta P q a) (delta_valid P q a hq)

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
  induction' T using List.reverseRecOn with T' a ih generalizing q
  · -- T = []
    simp [deltaStar]
    exact (suffixFn_self_prefix P q hq).symm
  · -- T = T' ++ [a]
    rw [deltaStar_append P q T' [a], deltaStar_singleton]
    unfold delta
    rw [ih hq]
    -- suffixFn P (P.take (suffixFn P (P.take q ++ T')) ++ [a])
    rw [← suffixFn_append_eq P (P.take q ++ T') a]
    -- suffixFn P ((P.take q ++ T') ++ [a])
    simp [List.append_assoc]

theorem deltaStar_eq_suffixFn (T : Text α) : deltaStar P 0 T = suffixFn P T := by
  simpa using deltaStar_eq_suffixFn_Pq P 0 T (by omega)

/-- The DFA accepts `T` iff `P` is a suffix of `T`. -/
theorem accepts_iff_isSuffix (T : Text α) : accepts P T ↔ isSuffix P T := by
  rw [accepts, deltaStar_eq_suffixFn P T]
  have hPle : P.length ≤ P.length := le_rfl
  constructor
  · intro h
    -- suffixFn P T = P.length
    -- suffixFn_satisfies: isSuffix (P.take (suffixFn P T)) T
    -- Since suffixFn P T = P.length, P.take (P.length) = P
    -- So isSuffix P T
    have hSuf := suffixFn_satisfies P T
    rw [h] at hSuf
    have : P.take (P.length) = P := by simp
    rw [this] at hSuf
    exact hSuf
  · intro h
    -- isSuffix P T
    -- By suffixFn_maximal: P.length ≤ suffixFn P T
    -- By suffixFn_le_length: suffixFn P T ≤ P.length
    -- So equality
    apply le_antisymm
    · exact suffixFn_le_length P T
    · apply suffixFn_maximal P T P.length hPle
      -- Need: isSuffix (P.take P.length) T
      -- P.take P.length = P
      simpa using h

theorem accepts_empty_pattern (T : Text α) : accepts ([] : Text α) T := by
  rw [accepts, deltaStar_eq_suffixFn ([] : Text α) T, suffixFn_nil_pattern]
  -- suffixFn [] T = 0 = [].length
  simp

theorem not_accepts_when_text_shorter (T : Text α) (hP : P ≠ []) (hLT : T.length < P.length) :
    ¬ accepts P T := by
  rw [accepts, deltaStar_eq_suffixFn P T]
  intro h
  -- suffixFn P T = P.length
  -- But suffixFn P T ≤ T.length < P.length, contradiction
  have hle := suffixFn_le_x_length P T
  rw [h] at hle
  omega

end Correctness

end Chapter32
end CLRS
