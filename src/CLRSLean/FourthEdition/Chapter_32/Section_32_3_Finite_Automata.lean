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

## Main results

- Lemma 32.3 — `σ(xa) ≤ σ(x) + 1` (`suffixLen_snoc_le`).
- Lemma 32.4 — `σ(xa) = σ(P_{σ(x)} a)` (`suffixLen_snoc_eq`).
- Theorem `deltaStar_eq_suffixLen` — `δ*(q, T) = σ(P_q T)`.
- Theorem `deltaStar_accepts_iff_suffix` — `δ*(0, T) = |P| ↔ P` is a suffix of `T`.
- `dfaMatcher` — the all-occurrences automaton matcher, with
  `dfaMatcher_sound`, `dfaMatcher_complete`, and `dfaMatcher_correct`
  (equivalence to `naiveMatcher`).
- `transitionTable`/`transitionLookup` — the finite-alphabet transition table,
  with `transitionLookup_eq_delta` (lookup is exactly `δ`).
- `dfaMatcherTable` — the table-driven matcher, refining `dfaMatcher`
  (`dfaMatcherTable_correct`).
- `transitionTableBuildCost_eq`/`dfaMatcherCost_eq` — preprocessing is
  `(|P| + 1)·|Σ|` and matching is `Θ(|T|)`.

Notation conventions used in this section:

- `P` : the pattern
- `T` : the text
- `σ` : the suffix function (written `suffixLen P`)
- `alphabet` : a finite list of the alphabet symbols used to build the table
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

/-- Suffix is transitive. -/
lemma suffix_trans {r s t : Text α} (hrs : isSuffix r s) (hst : isSuffix s t) : isSuffix r t := by
  rcases hrs with ⟨p, hp⟩
  rcases hst with ⟨q, hq⟩
  refine ⟨q ++ p, ?_⟩
  rw [List.append_assoc, hp, hq]

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
    rw [hlen, List.take_take, Nat.min_eq_left (by omega)]
  refine ⟨s, ?_⟩
  have hne : (P.take r) ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he
    have h0 : (P.take r).length = 0 := by simp [he]
    omega
  have hd : s ++ P.take (r - 1) = x := by
    have h1 : (s ++ P.take r).dropLast = (x ++ [a]).dropLast := by rw [hs]
    rw [List.dropLast_concat] at h1
    have h2 : (s ++ P.take r).dropLast = s ++ P.take (r - 1) := by
      rw [List.dropLast_append]
      by_cases h : (P.take r).isEmpty = true
      · have : P.take r = [] := (List.isEmpty_iff.mp h)
        exact (hne this).elim
      · simp [h, hdropLast]
    rw [h2] at h1
    exact h1
  exact hd

/-- If `P.take r` is a suffix of `x ++ [a]` and `0 < r ≤ |P|`, then the last
character of `P.take r` is `a`. -/
lemma suffix_last_char_of_snoc (P x : Text α) (r : ℕ) (a : α)
    (hsuf : isSuffix (P.take r) (x ++ [a])) (hrpos : 0 < r) (hk : r ≤ P.length) :
    (P.take r).getLast? = some a := by
  rcases hsuf with ⟨s, hs⟩
  have hne : P.take r ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he
    have h0 : (P.take r).length = 0 := by simp [he]
    omega
  have hlast : (s ++ P.take r).getLast? = some a := by
    rw [hs, List.getLast?_concat]
  have hrel : (s ++ P.take r).getLast? = (P.take r).getLast? := by
    rw [List.getLast?_append]
    rw [show (P.take r).getLast? = some ((P.take r).getLast hne) from List.getLast?_eq_getLast hne]
    simp
  rw [hrel] at hlast
  exact hlast

/-- `P.take r = P.take (r-1) ++ [a]` when `(P.take r)` ends in `a`. -/
lemma take_eq_take_pred_append (P : Text α) (r : ℕ) (a : α) (hrpos : 0 < r) (hk : r ≤ P.length)
    (hchar : (P.take r).getLast? = some a) : P.take r = P.take (r - 1) ++ [a] := by
  have hne : P.take r ≠ [] := by
    have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hk
    intro he
    have h0 : (P.take r).length = 0 := by simp [he]
    omega
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
      suffix_trans hsuf₂ hsuf'
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
          have hlen : (P.take (r - 1)).length ≤ (P.take q).length := by
            have h1 : (P.take (r - 1)).length = r - 1 := by
              rw [List.length_take]; exact Nat.min_eq_left (by omega)
            have h2 : (P.take q).length = q := by
              rw [List.length_take]; exact Nat.min_eq_left (suffixLen_le P x)
            rw [h1, h2]; omega
          have hpreq : isSuffix (P.take (r - 1)) (P.take q) :=
            isSuffix_of_suffix_of_suffix hq hpre hlen
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
  exact le_antisymm hle₂ hle₁

/-- `σ(y T) = σ(P_{σ(y)} T)`: the suffix function of an extended string only
depends on the longest prefix-suffix of the base. -/
theorem suffixLen_append_eq (P : Text α) (y T : Text α) :
    suffixLen P (y ++ T) = suffixLen P (P.take (suffixLen P y) ++ T) := by
  induction T generalizing y with
  | nil =>
      rw [List.append_nil, List.append_nil]
      exact (suffixLen_of_take P (suffixLen P y) (suffixLen_le P y)).symm
  | cons a T ih =>
      rw [show y ++ (a :: T) = (y ++ [a]) ++ T by simp]
      rw [ih (y ++ [a]), suffixLen_snoc_eq P y a]
      rw [show P.take (suffixLen P y) ++ (a :: T) = (P.take (suffixLen P y) ++ [a]) ++ T by simp]
      exact (ih (P.take (suffixLen P y) ++ [a])).symm

/-- The transition function `δ(q, a) = σ(P_q a)` (CLRS §32.3). -/
def delta (P : Text α) (q : ℕ) (a : α) : ℕ :=
  suffixLen P (P.take q ++ [a])

/-- `δ` extended to a string: `δ*(q, T) = foldl δ q T`. -/
def deltaStar (P : Text α) (q : ℕ) : Text α → ℕ :=
  List.foldl (delta P) q

@[simp] theorem deltaStar_nil (P : Text α) (q : ℕ) : deltaStar P q [] = q := rfl

@[simp] theorem deltaStar_cons (P : Text α) (q : ℕ) (a : α) (T : Text α) :
    deltaStar P q (a :: T) = deltaStar P (delta P q a) T := rfl

/-- `δ*(q, T) = σ(P_q T)`. -/
theorem deltaStar_eq_suffixLen (P : Text α) (q : ℕ) (T : Text α) (hq : q ≤ P.length) :
    deltaStar P q T = suffixLen P (P.take q ++ T) := by
  induction T generalizing q with
  | nil => rw [deltaStar_nil, List.append_nil]; exact (suffixLen_of_take P q hq).symm
  | cons a T ih =>
      rw [deltaStar_cons]
      have hq' : delta P q a ≤ P.length := by
        unfold delta; exact suffixLen_le P (P.take q ++ [a])
      rw [ih (delta P q a) hq']
      unfold delta
      rw [show P.take q ++ (a :: T) = (P.take q ++ [a]) ++ T by simp]
      exact (suffixLen_append_eq P (P.take q ++ [a]) T).symm

/-- The automaton (from state 0) reaches state `|P|` exactly when `P` is a
suffix of the input. -/
theorem deltaStar_accepts_iff_suffix (P T : Text α) :
    deltaStar P 0 T = P.length ↔ isSuffix P T := by
  have h := deltaStar_eq_suffixLen P 0 T (by omega)
  rw [h]
  change suffixLen P T = P.length ↔ isSuffix P T
  constructor
  · intro hlen
    have hsuf := suffixLen_satisfies P T
    rw [hlen, List.take_length] at hsuf
    simpa using hsuf
  · intro hsuf
    have hmax := suffixLen_maximal P T P.length (by rfl) (by simpa using hsuf)
    have hle := suffixLen_le P T
    omega

/-- `δ*(0, x) = σ(x)` never exceeds the length of its input. -/
lemma deltaStar_le_length (P x : Text α) : deltaStar P 0 x ≤ x.length := by
  rw [deltaStar_eq_suffixLen P 0 x (by omega)]
  simpa using (suffixLen_le_length P x)

/-- The empty pattern is never a proper suffix: `δ*` from `0` stays at `0`. -/
lemma deltaStar_empty (x : Text α) : deltaStar ([] : Text α) 0 x = 0 := by
  rw [deltaStar_eq_suffixLen ([] : Text α) 0 x (by omega)]
  simp [suffixLen, suffixLenAux]

/-- Appending one character to the scanned text advances `δ*` by one transition. -/
lemma deltaStar_append_one (P : Text α) (scanned : Text α) (c : α) :
    deltaStar P 0 (scanned ++ [c]) = delta P (deltaStar P 0 scanned) c := by
  change List.foldl (delta P) 0 (scanned ++ [c]) = delta P (List.foldl (delta P) 0 scanned) c
  rw [List.foldl_append]
  rfl

/-- `range (n + 2)` is `0` followed by `range (n + 1)` shifted by one. -/
lemma range_succ_cons (n : ℕ) :
    List.range (n + 2) = 0 :: (List.range (n + 1)).map (fun k => 1 + k) := by
  conv_lhs => rw [show n + 2 = 1 + (n + 1) by omega]
  rw [List.range_add]
  simp only [List.range_one, List.singleton_append]

@[simp] lemma take_cons_zero (c : α) (T : Text α) : (c :: T).take 0 = [] := rfl

lemma take_cons_succ_one (c : α) (T : Text α) (k : ℕ) : (c :: T).take (1 + k) = c :: T.take k := by
  rw [List.take_cons (by omega : 0 < 1 + k)]
  rw [show (1 + k) - 1 = k by omega]

/--
The finite-automaton scan (CLRS `FINITE-AUTOMATON-MATCHER`).  `scanned` is the
text already scanned, `q = δ*(0, scanned)` the current state, and `m = |P|`.
It returns, in increasing order, every shift `scanned.length - m` at which the
state has reached `m`, i.e. every shift where `P` matches the text.
-/
def dfaScan (P : Text α) (m : ℕ) (scanned : Text α) (q : ℕ) : Text α → List ℕ
  | [] => if q == m then [scanned.length - m] else []
  | c :: rest =>
      let q' := delta P q c
      let tail := dfaScan P m (scanned ++ [c]) q' rest
      if q == m then (scanned.length - m) :: tail else tail

@[simp] lemma dfaScan_nil (P : Text α) (m : ℕ) (scanned : Text α) (q : ℕ) :
    dfaScan P m scanned q [] = (if q == m then [scanned.length - m] else []) := rfl

lemma dfaScan_cons (P : Text α) (m : ℕ) (scanned : Text α) (q : ℕ) (c : α) (T : Text α) :
    dfaScan P m scanned q (c :: T)
      = (if q == m then [scanned.length - m] else [])
          ++ dfaScan P m (scanned ++ [c]) (delta P q c) T := by
  by_cases h : q == m <;> simp [dfaScan, h]

/-- The tail of the scan specification: the composed shift/state functions
rewrite to the RHS functions. -/
lemma dfaScan_spec_tail (P : Text α) (m : ℕ) (scanned : Text α) (c : α) (T : Text α) :
    List.map ((fun j => scanned.length + j - m) ∘ (fun k => 1 + k))
        (List.filter ((fun j => deltaStar P 0 (scanned ++ (c :: T).take j) == m) ∘ (fun k => 1 + k)) (List.range (T.length + 1)))
      = List.map (fun j => (scanned ++ [c]).length + j - m)
          (List.filter (fun j => deltaStar P 0 ((scanned ++ [c]) ++ T.take j) == m) (List.range (T.length + 1))) := by
  have hp : ((fun j => deltaStar P 0 (scanned ++ (c :: T).take j) == m) ∘ (fun k => 1 + k))
      = (fun j => deltaStar P 0 ((scanned ++ [c]) ++ T.take j) == m) := by
    funext j
    simp [take_cons_succ_one, List.append_assoc]
  have hf : ((fun j => scanned.length + j - m) ∘ (fun k => 1 + k))
      = (fun j => (scanned ++ [c]).length + j - m) := by
    funext j
    simp [List.length_append]
    omega
  rw [hp, hf]

/-- The RHS of the scan specification, decomposed across one consumed character. -/
lemma dfaScan_spec_cons (P : Text α) (m : ℕ) (scanned : Text α) (c : α) (T : Text α) :
    ((List.range ((c :: T).length + 1)).filter (fun j => deltaStar P 0 (scanned ++ (c :: T).take j) == m)).map
        (fun j => scanned.length + j - m)
      = (if deltaStar P 0 scanned == m then [scanned.length - m] else [])
          ++ ((List.range (T.length + 1)).filter (fun j => deltaStar P 0 ((scanned ++ [c]) ++ T.take j) == m)).map
              (fun j => (scanned ++ [c]).length + j - m) := by
  change ((List.range (T.length + 2)).filter (fun j => deltaStar P 0 (scanned ++ (c :: T).take j) == m)).map
        (fun j => scanned.length + j - m)
      = (if deltaStar P 0 scanned == m then [scanned.length - m] else [])
          ++ ((List.range (T.length + 1)).filter (fun j => deltaStar P 0 ((scanned ++ [c]) ++ T.take j) == m)).map
              (fun j => (scanned ++ [c]).length + j - m)
  rw [range_succ_cons T.length]
  simp only [List.filter_cons, List.map_cons, List.filter_nil, List.map_nil, List.map_append]
  simp only [List.filter_map]
  by_cases h : deltaStar P 0 scanned = m <;> simp [h, List.map_map, List.append_nil] <;> rw [dfaScan_spec_tail P m scanned c T] <;> simp

/--
The automaton scan from a scanned whose state is `δ*(0, scanned)` returns exactly
the shifts `scanned.length + j - m` for end positions `scanned.length + j` whose
scanned text `scanned ++ T.take j` reaches state `m`.
-/
lemma dfaScan_spec (P : Text α) (m : ℕ) (scanned T : Text α) :
    dfaScan P m scanned (deltaStar P 0 scanned) T
      = ((List.range (T.length + 1)).filter (fun j => deltaStar P 0 (scanned ++ T.take j) == m)).map
          (fun j => scanned.length + j - m) := by
  induction T generalizing scanned with
  | nil =>
      simp [dfaScan, List.append_nil, List.take_zero, List.range_one, List.filter_cons, List.map_cons]
      by_cases h : deltaStar P 0 scanned = m <;> simp [h]
  | cons c T ih =>
      rw [dfaScan_cons, ← deltaStar_append_one P scanned c]
      rw [ih (scanned ++ [c])]
      exact (dfaScan_spec_cons P m scanned c T).symm

/--
The finite-automaton matcher: scan `T` left-to-right maintaining the automaton
state, recording every shift where the state reaches `|P|`.  This is the
all-occurrences DFA matcher of CLRS §32.3.
-/
def dfaMatcher (P T : Text α) : List ℕ :=
  dfaScan P P.length [] 0 T

/-- The automaton matcher, expressed as an end-position filter-map. -/
theorem dfaMatcher_spec (P T : Text α) :
    dfaMatcher P T
      = ((List.range (T.length + 1)).filter (fun j => deltaStar P 0 (T.take j) == P.length)).map
          (fun j => j - P.length) := by
  unfold dfaMatcher
  simpa using (dfaScan_spec P P.length [] T)

/-- A real match at shift `s` is exactly a suffix of the `(s + |P|)`-scanned. -/
lemma matchesAt_iff_isSuffix_take (P T : Text α) (s : ℕ) (hs : s + P.length ≤ T.length) :
    matchesAt T P s = true ↔ isSuffix P (T.take (s + P.length)) := by
  unfold matchesAt
  rw [if_pos hs, beq_iff_eq]
  constructor
  · intro h
    refine ⟨T.take s, ?_⟩
    rw [List.take_add (i := s) (j := P.length) (l := T), h]
  · intro h
    rcases h with ⟨u, hu⟩
    have hulen : u.length = s := by
      have hlen := congrArg List.length hu
      rw [List.length_append, List.length_take] at hlen
      have hmin : min (s + P.length) T.length = s + P.length := Nat.min_eq_left hs
      rw [hmin] at hlen
      omega
    calc
      (T.drop s).take P.length = (T.take (s + P.length)).drop s := by
        rw [List.drop_take]; simp
      _ = (u ++ P).drop s := by rw [← hu]
      _ = (u ++ P).drop u.length := by rw [hulen]
      _ = P := List.drop_left

/-- `δ*(0, T.take (s + |P|))` accepting agrees with `matchesAt T P s`. -/
lemma deltaStar_take_eq_matchesAt (P T : Text α) (s : ℕ) (hs : s + P.length ≤ T.length) :
    (deltaStar P 0 (T.take (s + P.length)) == P.length) = matchesAt T P s := by
  have hacc : (deltaStar P 0 (T.take (s + P.length)) = P.length) ↔ (matchesAt T P s = true) := by
    constructor
    · intro hd
      have hsuf := (deltaStar_accepts_iff_suffix P (T.take (s + P.length))).mp hd
      exact (matchesAt_iff_isSuffix_take P T s hs).mpr hsuf
    · intro hm
      have hsuf := (matchesAt_iff_isSuffix_take P T s hs).mp hm
      exact (deltaStar_accepts_iff_suffix P (T.take (s + P.length))).mpr hsuf
  cases h : matchesAt T P s with
  | true =>
      have hd : deltaStar P 0 (T.take (s + P.length)) = P.length := hacc.mpr h
      simp [hd, beq_iff_eq]
  | false =>
      have hd : deltaStar P 0 (T.take (s + P.length)) ≠ P.length := by
        intro hd'
        have htrue : matchesAt T P s = true := hacc.mp hd'
        rw [h] at htrue
        cases htrue
      cases hb : deltaStar P 0 (T.take (s + P.length)) == P.length with
      | true =>
          have heq : deltaStar P 0 (T.take (s + P.length)) = P.length := beq_iff_eq.mp hb
          exact (hd heq).elim
      | false =>
          rfl

/-- The end-position filter-map of the automaton matcher equals the shift-domain
`naiveMatcher` result. -/
lemma filter_map_delta_eq_naive (P T : Text α) :
    ((List.range (T.length + 1)).filter (fun j => deltaStar P 0 (T.take j) == P.length)).map
        (fun j => j - P.length) = naiveMatcher T P := by
  by_cases hzero : P.length = 0
  · have hnil : P = [] := List.eq_nil_of_length_eq_zero hzero
    subst P
    simp [naiveMatcher_empty, deltaStar_empty]
  · have hm0 : 0 < P.length := Nat.pos_of_ne_zero hzero
    by_cases hle : P.length ≤ T.length
    · have hrange : List.range (T.length + 1)
          = List.range P.length ++ List.map (fun x => P.length + x) (List.range (T.length - P.length + 1)) := by
        have h := List.range_add (n := P.length) (m := T.length - P.length + 1)
        rw [show P.length + (T.length - P.length + 1) = T.length + 1 by omega] at h
        exact h
      rw [hrange, List.filter_append, List.map_append]
      have hfilt1 : (List.range P.length).filter (fun j => deltaStar P 0 (T.take j) == P.length) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro j hj
        rw [List.mem_filter] at hj
        rcases hj with ⟨hjr, hjp⟩
        have hjm : j < P.length := List.mem_range.mp hjr
        have hd : deltaStar P 0 (T.take j) ≤ j := by
          exact le_trans (deltaStar_le_length P (T.take j)) (by rw [List.length_take]; exact Nat.min_le_left _ _)
        have hbad : deltaStar P 0 (T.take j) = P.length := beq_iff_eq.mp hjp
        have hle' : P.length ≤ j := by simpa [hbad] using hd
        omega
      rw [hfilt1, List.map_nil, List.nil_append]
      rw [List.filter_map, List.map_map]
      have hsub : (fun x => (P.length + x) - P.length) = (fun x => x) := by
        funext x; rw [Nat.add_sub_cancel_left]
      change List.map (fun x => (P.length + x) - P.length)
          ((List.range (T.length - P.length + 1)).filter (fun x => deltaStar P 0 (T.take (P.length + x)) == P.length))
        = naiveMatcher T P
      simp [hsub]
      rw [naiveMatcher, if_neg hzero]
      apply List.filter_congr
      intro s hs
      have hsle : s + P.length ≤ T.length := by
        have := List.mem_range.mp hs
        omega
      rw [show P.length + s = s + P.length by omega]
      exact deltaStar_take_eq_matchesAt P T s hsle
    · have hlong : T.length < P.length := Nat.lt_of_not_ge hle
      have hfilt : (List.range (T.length + 1)).filter (fun j => deltaStar P 0 (T.take j) == P.length) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro j hj
        rw [List.mem_filter] at hj
        rcases hj with ⟨hjr, hjp⟩
        have hjn : j < T.length + 1 := List.mem_range.mp hjr
        have hd : deltaStar P 0 (T.take j) ≤ j := by
          exact le_trans (deltaStar_le_length P (T.take j)) (by rw [List.length_take]; exact Nat.min_le_left _ _)
        have hbad : deltaStar P 0 (T.take j) = P.length := beq_iff_eq.mp hjp
        have hle' : P.length ≤ j := by simpa [hbad] using hd
        omega
      rw [hfilt, List.map_nil]
      simpa [noMatch] using (naiveMatcher_pattern_too_long T P hlong).symm

/--
**Correctness of the finite-automaton matcher.**  `dfaMatcher P T` returns
exactly the shifts that `naiveMatcher T P` returns, for every pattern and text.
-/
theorem dfaMatcher_correct (P T : Text α) : dfaMatcher P T = naiveMatcher T P := by
  rw [dfaMatcher_spec, filter_map_delta_eq_naive]

/-- Every shift returned by the automaton matcher is a valid match. -/
theorem dfaMatcher_sound (P T : Text α) (s : ℕ) (h : s ∈ dfaMatcher P T) : matchesAt T P s := by
  rw [dfaMatcher_correct] at h
  exact naiveMatcher_sound T P s h

/-- Every valid match is returned by the automaton matcher. -/
theorem dfaMatcher_complete (P T : Text α) (s : ℕ) (h : matchesAt T P s) : s ∈ dfaMatcher P T := by
  rw [dfaMatcher_correct]
  exact naiveMatcher_complete T P s h

/-- The deterministic matching-time work of the finite-automaton matcher: one
transition per text character, so the matching phase runs in time `Θ(|T|)` after
the transition table has been precomputed. -/
def dfaMatcherCost (P T : Text α) : ℕ := T.length

/-- The automaton matcher scans each character once. -/
theorem dfaMatcherCost_eq (P T : Text α) : dfaMatcherCost P T = T.length := rfl

section TransitionTable

/--
The transition table for pattern `P` over a finite alphabet `alphabet` (CLRS
§32.3 `COMPUTE-TRANSITION-FUNCTION`): one row per state `q ∈ [0, |P|]`, each row
listing the precomputed next-state `δ(q, a)` for every `a ∈ alphabet`, in
row-major order.
-/
def transitionTable (alphabet : List α) (P : Text α) : List (List ℕ) :=
  (List.range (P.length + 1)).map (fun q => alphabet.map (fun a => delta P q a))

/-- Look up the next state for state `q` and symbol `a` in a transition table
indexed by `alphabet`, returning `0` for an out-of-range state or symbol. -/
def transitionLookup (alphabet : List α) (table : List (List ℕ)) (q : ℕ) (a : α) : ℕ :=
  (table.getD q []).getD (alphabet.idxOf a) 0

/-- The transition table has one row per state. -/
theorem transitionTable_length (alphabet : List α) (P : Text α) :
    (transitionTable alphabet P).length = P.length + 1 := by
  unfold transitionTable
  simp

/--
The table lookup agrees with the semantic transition `δ`: for every state
`q ≤ |P|` and every symbol `a` in the alphabet, the entry stored in
`transitionTable alphabet P` at `(q, a)` is exactly `δ(q, a)`.
-/
theorem transitionLookup_eq_delta (alphabet : List α) (P : Text α) (q : ℕ) (hq : q ≤ P.length) (a : α)
    (ha : a ∈ alphabet) :
    transitionLookup alphabet (transitionTable alphabet P) q a = delta P q a := by
  unfold transitionLookup transitionTable
  have hrow : ((List.range (P.length + 1)).map (fun q => alphabet.map (fun a => delta P q a))).getD q []
      = alphabet.map (fun a => delta P q a) := by
    rw [List.getD_eq_getElem]
    · rw [List.getElem_map, List.getElem_range]
    · rw [List.length_map, List.length_range]
      omega
  rw [hrow]
  have hlt : alphabet.idxOf a < alphabet.length := (List.idxOf_lt_length_iff).mpr ha
  have hlen : alphabet.idxOf a < (alphabet.map (fun a => delta P q a)).length := by
    simpa using hlt
  rw [List.getD_eq_getElem (l := alphabet.map (fun a => delta P q a)) (d := 0) (n := alphabet.idxOf a) hlen]
  rw [List.getElem_map]
  rw [List.getElem_idxOf hlt]

/--
The table-driven scan: the same left-to-right scan as `dfaScan`, but each
transition is read from the precomputed table rather than recomputed as `δ`.
-/
def dfaScanTable (alphabet : List α) (P : Text α) (m : ℕ) (scanned : Text α) (q : ℕ) : Text α → List ℕ
  | [] => if q == m then [scanned.length - m] else []
  | c :: rest =>
      let q' := transitionLookup alphabet (transitionTable alphabet P) q c
      let tail := dfaScanTable alphabet P m (scanned ++ [c]) q' rest
      if q == m then (scanned.length - m) :: tail else tail

lemma dfaScanTable_cons (alphabet : List α) (P : Text α) (m : ℕ) (scanned : Text α) (q : ℕ) (c : α) (T : Text α) :
    dfaScanTable alphabet P m scanned q (c :: T)
      = (if q == m then [scanned.length - m] else [])
          ++ dfaScanTable alphabet P m (scanned ++ [c]) (transitionLookup alphabet (transitionTable alphabet P) q c) T := by
  by_cases h : q == m <;> simp [dfaScanTable, h]

/-- The table-driven matcher (CLRS `FINITE-AUTOMATON-MATCHER` with precomputed
`δ`): scan `T` using the transition table for `alphabet`, in O(1) per character. -/
def dfaMatcherTable (alphabet : List α) (P T : Text α) : List ℕ :=
  dfaScanTable alphabet P P.length [] 0 T

/-- The table-driven scan agrees with the semantic scan when every state is in
range and every scanned character is in the alphabet. -/
lemma dfaScanTable_eq_dfaScan (alphabet : List α) (P : Text α) (scanned T : Text α) (q : ℕ)
    (hq : q ≤ P.length) (hT : ∀ c ∈ T, c ∈ alphabet) :
    dfaScanTable alphabet P P.length scanned q T = dfaScan P P.length scanned q T := by
  induction T generalizing scanned q with
  | nil => rfl
  | cons c T ih =>
      rw [dfaScanTable_cons, dfaScan_cons]
      have hlookup : transitionLookup alphabet (transitionTable alphabet P) q c = delta P q c :=
        transitionLookup_eq_delta alphabet P q hq c (hT c (by simp))
      have hq' : delta P q c ≤ P.length := by unfold delta; exact suffixLen_le P (P.take q ++ [c])
      have hT' : ∀ c ∈ T, c ∈ alphabet := by intro c hc; exact hT c (by simp [hc])
      rw [hlookup, ih (scanned ++ [c]) (delta P q c) hq' hT']

/--
The table-driven matcher refines the semantic automaton matcher over a finite
alphabet: when every character of `T` lies in `alphabet`, the two return exactly
the same shifts.
-/
theorem dfaMatcherTable_correct (alphabet : List α) (P T : Text α) (hT : ∀ c ∈ T, c ∈ alphabet) :
    dfaMatcherTable alphabet P T = dfaMatcher P T := by
  unfold dfaMatcherTable dfaMatcher
  exact dfaScanTable_eq_dfaScan alphabet P [] T 0 (by omega) hT

/-- The table-driven matcher returns exactly the shifts of `naiveMatcher` when the
text stays within the alphabet. -/
theorem dfaMatcherTable_eq_naive (alphabet : List α) (P T : Text α) (hT : ∀ c ∈ T, c ∈ alphabet) :
    dfaMatcherTable alphabet P T = naiveMatcher T P := by
  rw [dfaMatcherTable_correct alphabet P T hT, dfaMatcher_correct]

/-- The deterministic preprocessing work: the total number of table cells, one
unit per precomputed transition. -/
def transitionTableBuildCost (alphabet : List α) (P : Text α) : ℕ :=
  ((transitionTable alphabet P).map List.length).sum

/--
The preprocessing cost equals `(|P| + 1) · |alphabet|`: the transition table has
one cell per state-symbol pair, matching the textbook `O(m·|Σ|)` construction.
-/
theorem transitionTableBuildCost_eq (alphabet : List α) (P : Text α) :
    transitionTableBuildCost alphabet P = (P.length + 1) * alphabet.length := by
  unfold transitionTableBuildCost transitionTable
  rw [List.map_map]
  change ((List.range (P.length + 1)).map (fun q => List.length (alphabet.map (fun a => delta P q a)))).sum
      = (P.length + 1) * alphabet.length
  simp [List.length_map, List.length_range, List.sum_replicate]

/-- The total deterministic work: preprocessing plus the Θ(|T|) scan. -/
theorem dfaTotalCost_eq (alphabet : List α) (P T : Text α) :
    transitionTableBuildCost alphabet P + dfaMatcherCost P T = (P.length + 1) * alphabet.length + T.length := by
  rw [transitionTableBuildCost_eq, dfaMatcherCost_eq]

end TransitionTable

end Chapter32
end CLRS
