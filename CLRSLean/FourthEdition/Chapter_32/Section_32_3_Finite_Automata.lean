import Mathlib
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher

set_option maxHeartbeats 1000000

/-! # Section 32.3 — String Matching with Finite Automata

The finite-automaton string matcher (CLRS §32.3) builds a deterministic finite
automaton whose states are `0 … |P|`, with transition `δ(q, a) = σ(P_q a)`, the
length of the longest prefix of `P` that is a suffix of `P_q a` (here `σ` is the
*suffix function* of CLRS §32.3).  After preprocessing, scanning the text with
`δ` accepts a prefix exactly when the pattern is a suffix of that prefix, so a
shift is recorded whenever the state reaches `|P|`.

## Key definitions

- {lit}`suffixTest p t` — decidable "is `p` a suffix of `t`".
- {lit}`suffixLen P x` — the suffix function `σ(x)`.
- {lit}`delta P q a` — the transition `δ(q, a)`.
- {lit}`deltaStar P q t` — `δ` extended to a string.
- {lit}`dfaMatcher T P` — the all-occurrences automaton matcher.

## Main results

- Lemma 32.3 — `σ(xa) ≤ σ(x) + 1` (`suffixLen_snoc_le`).
- Lemma 32.4 — `σ(xa) = σ(P_{σ(x)} a)` (`suffixLen_snoc_eq`).
- Theorem `deltaStar_eq_suffixLen` — `δ*(q, T) = σ(P_q T)`.
- Theorem `deltaStar_accepts_iff_suffix` — `δ*(0, T) = |P| ↔ P` is a suffix of `T`.
- Theorem `dfaMatcher_correct` — `dfaMatcher` agrees with `naiveMatcher`.
- Theorem `transitionTable_lookup_eq_delta` — the finite-alphabet table lookup
  is exactly `δ`.

Notation conventions used in this section:

- `P` : the pattern
- `T` : the text
- `σ` : the suffix function (written `suffixLen P`)
-/
namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]

/-- Decidable "is `p` a suffix of `t`", computed by checking the trailing
substring. -/
def suffixTest (p t : Text α) : Bool :=
  if p.length ≤ t.length then (t.drop (t.length - p.length) == p) else false

/-- `suffixTest` decides `isSuffix`. -/
theorem suffixTest_eq_isSuffix (p t : Text α) :
    suffixTest p t = true ↔ isSuffix p t := by
  constructor
  · intro h
    unfold suffixTest at h
    split at h
    · next hlen =>
        have hdrop : t.drop (t.length - p.length) = p := beq_iff_eq.mp h
        refine ⟨t.take (t.length - p.length), ?_⟩
        simpa [hdrop] using (List.take_append_drop (t.length - p.length) t)
    · simp at h
  · intro h
    unfold suffixTest
    have hlen : p.length ≤ t.length := isSuffix_length_le h
    rw [if_pos hlen]
    have hdrop : p = t.drop (t.length - p.length) := by
      rcases h with ⟨s, hs⟩
      have hlen' : s.length + p.length = t.length := by
        simpa [List.length_append] using congrArg List.length hs
      calc
        p = (s ++ p).drop s.length := by simp
        _ = t.drop s.length := by rw [hs]
        _ = t.drop (t.length - p.length) := by
          congr 1
          omega
    rw [← hdrop]
    simp

/-- If `p` is a suffix of `t`, then `p = t.drop (t.length - p.length)`. -/
lemma isSuffix_eq_drop {p t : Text α} (h : isSuffix p t) : p = t.drop (t.length - p.length) := by
  rcases h with ⟨s, hs⟩
  have hlen : s.length + p.length = t.length := by
    simpa [List.length_append] using congrArg List.length hs
  calc
    p = (s ++ p).drop s.length := by simp
    _ = t.drop s.length := by rw [hs]
    _ = t.drop (t.length - p.length) := by
      congr 1
      omega

/-- `p` is a suffix of `t` → `p ++ u` is a suffix of `t ++ u`. -/
lemma suffix_append_right {p t u : Text α} (h : isSuffix p t) : isSuffix (p ++ u) (t ++ u) := by
  rcases h with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [← List.append_assoc, hs]

/-- If `y` and `z` are both suffixes of `x` and `z.length ≤ y.length`, then `z`
is a suffix of `y`. -/
lemma isSuffix_of_suffix_of_suffix {x y z : Text α} (hy : isSuffix y x) (hz : isSuffix z x)
    (hlen : z.length ≤ y.length) : isSuffix z y := by
  have hylen : y.length ≤ x.length := isSuffix_length_le hy
  have hzlen : z.length ≤ x.length := isSuffix_length_le hz
  rw [isSuffix_eq_drop hy, isSuffix_eq_drop hz]
  refine ⟨(x.drop (x.length - y.length)).take (y.length - z.length), ?_⟩
  rw [show List.drop (x.length - z.length) x = List.drop (y.length - z.length) (List.drop (x.length - y.length) x) by
    rw [List.drop_drop]
    congr 1
    omega]
  exact List.take_append_drop (y.length - z.length) (List.drop (x.length - y.length) x)

/-- The suffix function search: largest `k ≤ n` with `P.take k` a suffix of `x`. -/
def suffixLenAux (P x : Text α) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if suffixTest (P.take (n + 1)) x then n + 1 else suffixLenAux P x n

/-- The suffix function `σ(x)`: the largest `k ≤ |P|` with `P.take k` a suffix
of `x` (CLRS §32.3). -/
def suffixLen (P x : Text α) : ℕ :=
  suffixLenAux P x P.length

/-- `suffixLenAux` never exceeds its bound. -/
lemma suffixLenAux_le (P x : Text α) (n : ℕ) : suffixLenAux P x n ≤ n := by
  induction n with
  | zero => simp [suffixLenAux]
  | succ n ih =>
      by_cases ht : suffixTest (P.take (n + 1)) x
      · simp [suffixLenAux, ht]
      · simp [suffixLenAux, ht]; omega

/-- `σ(x) ≤ |P|`. -/
theorem suffixLen_le (P x : Text α) : suffixLen P x ≤ P.length := by
  unfold suffixLen
  exact suffixLenAux_le P x P.length

/-- `P.take (σ x)` is a suffix of `x`. -/
theorem suffixLen_satisfies (P x : Text α) : isSuffix (P.take (suffixLen P x)) x := by
  unfold suffixLen
  have hgo : ∀ n, suffixLenAux P x n = 0 ∨ suffixTest (P.take (suffixLenAux P x n)) x = true := by
    intro n
    induction n with
    | zero => left; simp [suffixLenAux]
    | succ n ih =>
        by_cases ht : suffixTest (P.take (n + 1)) x
        · right; simpa [suffixLenAux, ht] using ht
        · simpa [suffixLenAux, ht] using ih
  rcases hgo P.length with hzero | hsuf
  · rw [hzero]; exact isSuffix_empty x
  · exact (suffixTest_eq_isSuffix _ _).mp hsuf

/-- `σ(x)` is maximal: any `k ≤ |P|` whose `P.take k` is a suffix of `x`
satisfies `k ≤ σ(x)`. -/
theorem suffixLen_maximal (P x : Text α) (k : ℕ) (hk : k ≤ P.length)
    (hsuf : isSuffix (P.take k) x) : k ≤ suffixLen P x := by
  unfold suffixLen
  have ht : suffixTest (P.take k) x = true := (suffixTest_eq_isSuffix _ _).mpr hsuf
  have hgo : ∀ n, k ≤ n → k ≤ suffixLenAux P x n := by
    intro n hkn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hts : suffixTest (P.take (n + 1)) x
        · simp [suffixLenAux, hts]
          omega
        · have hklt : k < n + 1 := by
            by_cases hk_eq : k = n + 1
            · subst k; simpa [hts] using ht
            · omega
          have := ih (by omega)
          simpa [suffixLenAux, hts] using this
  exact hgo P.length hk

/-- `σ(x) ≤ |x|`. -/
theorem suffixLen_le_length (P x : Text α) : suffixLen P x ≤ x.length := by
  have hle := isSuffix_length_le (suffixLen_satisfies P x)
  have hlen : (P.take (suffixLen P x)).length = suffixLen P x := by
    rw [List.length_take]
    have : suffixLen P x ≤ P.length := suffixLen_le P x
    omega
  rwa [hlen] at hle

/-- The suffix function at a prefix of `P` returns that prefix's length. -/
theorem suffixLen_of_take (P : Text α) (q : ℕ) (hq : q ≤ P.length) :
    suffixLen P (P.take q) = q := by
  have hle : q ≤ suffixLen P (P.take q) :=
    suffixLen_maximal P (P.take q) q hq (isSuffix_self (P.take q))
  have hge : suffixLen P (P.take q) ≤ q := by
    have hle' := suffixLen_le_length P (P.take q)
    rw [List.length_take] at hle'
    omega
  omega

/-- If `P.take r` is a suffix of `x ++ [a]` with `0 < r`, then `P.take (r-1)`
is a suffix of `x`. -/
lemma suffix_dropLast_of_snoc (P x : Text α) (r : ℕ) (a : α) (hr : 0 < r) (hk : r ≤ P.length)
    (hsuf : isSuffix (P.take r) (x ++ [a])) : isSuffix (P.take (r - 1)) x := by
  rcases hsuf with ⟨s, hs⟩
  have hdropLast : (P.take r).dropLast = P.take (r - 1) := by
    rw [List.dropLast_eq_take]
    have hlen : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    rw [hlen, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  refine ⟨s, ?_⟩
  have hd : (s ++ P.take r).dropLast = (x ++ [a]).dropLast := by rw [hs]
  rw [List.dropLast_concat] at hd
  rw [List.dropLast_append] at hd
  have hne : (P.take r) ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he; rw [he] at hlenr; omega
  have hne' : (P.take r).isEmpty = false := by
    simpa [List.isEmpty_iff] using hne
  rw [if_neg hne'] at hd
  rw [hdropLast] at hd
  simp at hd
  exact hd.symm

/-- If `P.take r` is a suffix of `x ++ [a]` and `0 < r ≤ |P|`, then the last
character of `P.take r` is `a`. -/
lemma suffix_last_char_of_snoc (P x : Text α) (r : ℕ) (a : α)
    (hsuf : isSuffix (P.take r) (x ++ [a])) (hrpos : 0 < r) (hk : r ≤ P.length) :
    (P.take r).getLast? = some a := by
  rcases hsuf with ⟨s, hs⟩
  have hne : P.take r ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he; rw [he] at hlenr; omega
  calc
    (P.take r).getLast? = (s ++ P.take r).getLast? := by
      rw [List.getLast?_append]
      simp [hne]
    _ = (x ++ [a]).getLast? := by rw [hs]
    _ = some a := by rw [List.getLast?_concat]

/-- `P.take r = P.take (r-1) ++ [a]` when `(P.take r)` ends in `a`. -/
lemma take_eq_take_pred_append (P : Text α) (r : ℕ) (a : α) (hrpos : 0 < r) (hk : r ≤ P.length)
    (hchar : (P.take r).getLast? = some a) : P.take r = P.take (r - 1) ++ [a] := by
  have hne : P.take r ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he; rw [he] at hlenr; omega
  have hgetLast : (P.take r).getLast hne = a := by
    have := hchar
    rw [List.getLast?_eq_getLast hne] at this
    exact Option.some.inj this
  rw [← List.dropLast_append_getLast hne]
  rw [hgetLast]
  congr 1
  rw [List.dropLast_eq_take]
  have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
  rw [hlenr, List.take_take]
  rw [Nat.min_eq_left (by omega)]

/-- CLRS Lemma 32.3: `σ(xa) ≤ σ(x) + 1`. -/
theorem suffixLen_snoc_le (P x : Text α) (a : α) :
    suffixLen P (x ++ [a]) ≤ suffixLen P x + 1 := by
  let k := suffixLen P (x ++ [a])
  by_cases h0 : k = 0
  · omega
  · have hsuf : isSuffix (P.take k) (x ++ [a]) := suffixLen_satisfies P (x ++ [a])
    have hk : k ≤ P.length := suffixLen_le P (x ++ [a])
    have hpre : isSuffix (P.take (k - 1)) x := suffix_dropLast_of_snoc P x k a (Nat.pos_of_ne_zero h0) hk hsuf
    have hle : k - 1 ≤ suffixLen P x := suffixLen_maximal P x (k - 1) (by omega) hpre
    omega

/-- CLRS Lemma 32.4: `σ(xa) = σ(P_{σ(x)} a)`. -/
theorem suffixLen_snoc_eq (P x : Text α) (a : α) :
    suffixLen P (x ++ [a]) = suffixLen P (P.take (suffixLen P x) ++ [a]) := by
  let q := suffixLen P x
  -- direction 1: σ(P_q a) ≤ σ(x a)
  have hle₁ : suffixLen P (P.take q ++ [a]) ≤ suffixLen P (x ++ [a]) := by
    have hsufq : isSuffix (P.take q) x := suffixLen_satisfies P x
    have hsuf' : isSuffix (P.take q ++ [a]) (x ++ [a]) := suffix_append_right hsufq
    have hsuf₂ : isSuffix (P.take (suffixLen P (P.take q ++ [a]))) (P.take q ++ [a]) :=
      suffixLen_satisfies P (P.take q ++ [a])
    have hsuf₃ : isSuffix (P.take (suffixLen P (P.take q ++ [a]))) (x ++ [a]) :=
      isSuffix_of_suffix_of_suffix hsuf' hsuf₂ (isSuffix_length_le hsuf₂)
    have hk : suffixLen P (P.take q ++ [a]) ≤ P.length := suffixLen_le P (P.take q ++ [a])
    exact suffixLen_maximal P (x ++ [a]) (suffixLen P (P.take q ++ [a])) hk hsuf₃
  -- direction 2: σ(x a) ≤ σ(P_q a)
  have hle₂ : suffixLen P (x ++ [a]) ≤ suffixLen P (P.take q ++ [a]) := by
    let r := suffixLen P (x ++ [a])
    have hr : r ≤ q + 1 := suffixLen_snoc_le P x a
    have hsuf : isSuffix (P.take r) (x ++ [a]) := suffixLen_satisfies P (x ++ [a])
    have hk : r ≤ P.length := suffixLen_le P (x ++ [a])
    have hsufP : isSuffix (P.take r) (P.take q ++ [a]) := by
      by_cases hrq : r ≤ q
      · -- r ≤ q: P.take (r-1) suffix of x, hence suffix of P.take q; P[r-1] = a
        by_cases h0 : r = 0
        · rw [h0]; exact isSuffix_empty _
        · have hpre : isSuffix (P.take (r - 1)) x :=
            suffix_dropLast_of_snoc P x r a (Nat.pos_of_ne_zero h0) hk hsuf
          have hq : isSuffix (P.take q) x := suffixLen_satisfies P x
          have hpreq : isSuffix (P.take (r - 1)) (P.take q) :=
            isSuffix_of_suffix_of_suffix hq hpre (by omega)
          have hchar : (P.take r).getLast? = some a :=
            suffix_last_char_of_snoc P x r a hsuf (Nat.pos_of_ne_zero h0) hk
          have htake : P.take r = P.take (r - 1) ++ [a] :=
            take_eq_take_pred_append P r a (Nat.pos_of_ne_zero h0) hk hchar
          rw [htake]
          exact suffix_append_right hpreq
      · -- r = q + 1: P.take r = P.take q ++ [a]
        have hreq : r = q + 1 := by omega
        have hchar : (P.take (q + 1)).getLast? = some a := by
          have hsuf' : isSuffix (P.take (q + 1)) (x ++ [a]) := by simpa [hreq] using hsuf
          have hk' : q + 1 ≤ P.length := by omega
          exact suffix_last_char_of_snoc P x (q + 1) a hsuf' (by omega) hk'
        have htake : P.take r = P.take q ++ [a] := by
          rw [hreq]
          simpa using take_eq_take_pred_append P (q + 1) a (by omega) (by omega) hchar
        rw [htake]
        exact isSuffix_self _
    exact suffixLen_maximal P (P.take q ++ [a]) r hk hsufP
  omega

end Chapter32
end CLRS
