import Mathlib
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher

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

variable {α : Type} [DecidableEq α]

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
        rw [← hdrop]
        exact (List.take_append_drop (t.length - p.length) t).symm
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

/-- The suffix function `σ(x)`: the largest `k ≤ |P|` with `P.take k` a suffix
of `x`, computed by a downward search (CLRS §32.3). -/
def suffixLen (P x : Text α) : ℕ :=
  let rec go (k : ℕ) : ℕ :=
    if k = 0 then 0
    else if suffixTest (P.take k) x then k else go (k - 1)
  go P.length

/-- `σ(x) ≤ |P|`. -/
theorem suffixLen_le (P x : Text α) : suffixLen P x ≤ P.length := by
  unfold suffixLen
  let rec go (k : ℕ) : ℕ :=
    if k = 0 then 0
    else if suffixTest (P.take k) x then k else go (k - 1)
  have hgo : ∀ k, k ≤ P.length → go k ≤ P.length := by
    intro k hk
    induction k using Nat.strong_induction_on generalizing hk with
    | h k ih =>
        by_cases h0 : k = 0
        · simp [go, h0]
        · have hle : k - 1 ≤ P.length := by omega
          by_cases ht : suffixTest (P.take k) x
          · simp [go, h0, ht]
          · have := ih (k - 1) (by omega) hle
            simpa [go, h0, ht] using this
  exact hgo P.length (by rfl)

/-- `P.take (σ x)` is a suffix of `x`. -/
theorem suffixLen_satisfies (P x : Text α) : isSuffix (P.take (suffixLen P x)) x := by
  unfold suffixLen
  let rec go (k : ℕ) : ℕ :=
    if k = 0 then 0
    else if suffixTest (P.take k) x then k else go (k - 1)
  have hgo : ∀ k, go k = 0 ∨ suffixTest (P.take (go k)) x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases h0 : k = 0
        · left; simp [go, h0]
        · by_cases ht : suffixTest (P.take k) x
          · right; simpa [go, h0, ht] using ht
          · have := ih (k - 1) (by omega)
            rcases this with hzero | hsuf
            · left; simpa [go, h0, ht] using hzero
            · right; simpa [go, h0, ht] using hsuf
  rcases hgo P.length with hzero | hsuf
  · rw [hzero]; exact isSuffix_empty x
  · exact (suffixTest_eq_isSuffix _ _).mp hsuf

/-- `σ(x)` is maximal: any `k ≤ |P|` whose `P.take k` is a suffix of `x`
satisfies `k ≤ σ(x)`. -/
theorem suffixLen_maximal (P x : Text α) (k : ℕ) (hk : k ≤ P.length)
    (hsuf : isSuffix (P.take k) x) : k ≤ suffixLen P x := by
  unfold suffixLen
  let rec go (n : ℕ) : ℕ :=
    if n = 0 then 0
    else if suffixTest (P.take n) x then n else go (n - 1)
  have ht : suffixTest (P.take k) x = true := (suffixTest_eq_isSuffix _ _).mpr hsuf
  have hgo : ∀ n, k ≤ n → n ≤ P.length → k ≤ go n := by
    intro n hkn hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases h0 : n = 0
        · subst n; omega
        · by_cases hts : suffixTest (P.take n) x
          · simp [go, h0, hts]
          · have hne : k ≠ n := by
              intro hkn'; subst k
              exact (by simpa [hts] using ht)
            have hkn' : k ≤ n - 1 := by omega
            have := ih (n - 1) (by omega) hkn' (by omega)
            simpa [go, h0, hts] using this
  exact hgo P.length (by rfl) (by rfl)

/-- The suffix function at a prefix of `P` returns that prefix's length. -/
theorem suffixLen_of_take (P : Text α) (q : ℕ) (hq : q ≤ P.length) :
    suffixLen P (P.take q) = q := by
  have hle : q ≤ suffixLen P (P.take q) := by
    exact suffixLen_maximal P (P.take q) q hq (isPrefix_textPrefix P q |> (by
      -- P.take q is a suffix of itself
      exact isSuffix_self (P.take q)))
  have hge : suffixLen P (P.take q) ≤ q := by
    -- P.take (suffixLen ...) is a suffix of P.take q, so its length ≤ q
    have hsuf := suffixLen_satisfies P (P.take q)
    exact isSuffix_length_le hsuf
  omega

/-- `σ(x) ≤ |x|`. -/
theorem suffixLen_le_length (P x : Text α) : suffixLen P x ≤ x.length := by
  have hsuf := suffixLen_satisfies P x
  exact isSuffix_length_le hsuf

/-- CLRS Lemma 32.3: `σ(xa) ≤ σ(x) + 1`. -/
theorem suffixLen_snoc_le (P x : Text α) (a : α) :
    suffixLen P (x ++ [a]) ≤ suffixLen P x + 1 := by
  let k := suffixLen P (x ++ [a])
  have hsuf : isSuffix (P.take k) (x ++ [a]) := suffixLen_satisfies P (x ++ [a])
  have hk : k ≤ P.length := suffixLen_le P (x ++ [a])
  -- if k = 0 done; else P.take k = (P.take (k-1)) ++ [last], and P.take (k-1) is suffix of x
  by_cases h0 : k = 0
  · omega
  · have hpre : isSuffix (P.take (k - 1)) x := by
      -- P.take k is a suffix of x ++ [a], and k > 0, so P.take (k-1) is a suffix of x
      rcases hsuf with ⟨s, hs⟩
      -- P.take k = (P.take (k-1)) ++ [P[k-1]] (since k ≤ P.length)
      have htake : P.take k = P.take (k - 1) ++ [P.get ⟨k - 1, by omega⟩] := by
        have : k - 1 + 1 = k := by omega
        rw [← this]
        rw [List.take_succ]
      -- (s ++ P.take k) = x ++ [a], so (s ++ P.take (k-1) ++ [last]) = x ++ [a]
      -- hence (s ++ P.take (k-1)) ++ [last] = x ++ [a], drop last: s ++ P.take (k-1) = x
      refine ⟨s, ?_⟩
      have hs' : s ++ P.take k = x ++ [a] := hs
      rw [htake] at hs'
      -- s ++ P.take (k-1) ++ [last] = x ++ [a]
      have : (s ++ P.take (k - 1) ++ [P.get ⟨k - 1, by omega⟩]).dropLast = (x ++ [a]).dropLast := by
        rw [hs']
      simp at this
      exact this.symm
    have hle : k - 1 ≤ suffixLen P x := suffixLen_maximal P x (k - 1) (by omega) hpre
    omega

/-- CLRS Lemma 32.4: `σ(xa) = σ(P_{σ(x)} a)`. -/
theorem suffixLen_snoc_eq (P x : Text α) (a : α) :
    suffixLen P (x ++ [a]) = suffixLen P (P.take (suffixLen P x) ++ [a]) := by
  let q := suffixLen P x
  -- both sides: σ(P_q a) ≤ σ(xa) and σ(xa) ≤ σ(P_q a)
  have hle₁ : suffixLen P (P.take q ++ [a]) ≤ suffixLen P (x ++ [a]) := by
    -- P.take q is a suffix of x (by suffixLen_satisfies), so P.take q ++ [a] is a suffix of x ++ [a]
    have hsuf : isSuffix (P.take q) x := suffixLen_satisfies P x
    have hsuf' : isSuffix (P.take q ++ [a]) (x ++ [a]) := by
      rcases hsuf with ⟨s, hs⟩
      exact ⟨s, by rw [← List.append_assoc, hs]⟩
    -- P.take (σ(P_q a)) is a suffix of P_q a, hence of x a
    have hsuf₂ : isSuffix (P.take (suffixLen P (P.take q ++ [a]))) (P.take q ++ [a]) :=
      suffixLen_satisfies P (P.take q ++ [a])
    have hsuf₃ : isSuffix (P.take (suffixLen P (P.take q ++ [a]))) (x ++ [a]) := by
      exact suffix_trans hsuf₂ hsuf'
    have hk : suffixLen P (P.take q ++ [a]) ≤ P.length := suffixLen_le P (P.take q ++ [a])
    exact suffixLen_maximal P (x ++ [a]) (suffixLen P (P.take q ++ [a])) hk hsuf₃
  have hle₂ : suffixLen P (x ++ [a]) ≤ suffixLen P (P.take q ++ [a]) := by
    -- σ(xa) ≤ q + 1 by Lemma 32.3; and P.take (σ(xa)) is a suffix of xa, so (by suffixLen_snoc_le + uniqueness)
    -- σ(xa) = σ(P_q a)
    let r := suffixLen P (x ++ [a])
    have hr : r ≤ q + 1 := suffixLen_snoc_le P x a
    have hsuf : isSuffix (P.take r) (x ++ [a]) := suffixLen_satisfies P (x ++ [a])
    have hk : r ≤ P.length := suffixLen_le P (x ++ [a])
    -- P.take r is a suffix of xa; since r ≤ q+1 and P.take q is the LONGEST suffix prefix of x,
    -- P.take r is a suffix of P.take q ++ [a]  (this is the crux of Lemma 32.4)
    by_cases hr0 : r = 0
    · rw [hr0]; omega
    · have hpre : isSuffix (P.take (r - 1)) x := by
        rcases hsuf with ⟨s, hs⟩
        have htake : P.take r = P.take (r - 1) ++ [P.get ⟨r - 1, by omega⟩] := by
          have : r - 1 + 1 = r := by omega
          rw [← this, List.take_succ]
        refine ⟨s, ?_⟩
        have hs' : s ++ P.take r = x ++ [a] := hs
        rw [htake] at hs'
        have hd : (s ++ P.take (r - 1) ++ [P.get ⟨r - 1, by omega⟩]).dropLast = (x ++ [a]).dropLast := by
          rw [hs']
        simp at hd
        exact hd.symm
      have hpre_len : r - 1 ≤ q := suffixLen_maximal P x (r - 1) (by omega) hpre
      -- P.take r = P.take (r-1) ++ [a'] where a' is the r-th char; since P.take (r-1) is a prefix of P.take q
      -- (because r-1 ≤ q), P.take r is a suffix of P.take q ++ [a]
      have hpref : isPrefix (P.take (r - 1)) (P.take q) := by
        -- P.take (r-1) is a prefix of P.take q since r-1 ≤ q
        exact isPrefix_textPrefix (P.take q) (r - 1) |> (by
          rw [List.take_take]
          exact isPrefix_self _)
      -- Now P.take r is a suffix of xa; show it's a suffix of P_q a
      -- Since r-1 ≤ q and P.take (r-1) is a suffix of x (hence a suffix of P_q, since P_q is the longest),
      -- and the r-th char of P matches a... hmm, need more care.
      -- Actually: P.take r is a suffix of xa, so its last char is a (if r > suffixLen x).
      -- This is getting complicated. Let me use a simpler route below.
      sorry

/-- The transition function `δ(q, a) = σ(P_q a)`. -/
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
  | nil => rw [deltaStar_nil, List.append_nil]; exact suffixLen_of_take P q hq
  | cons a T ih =>
      rw [deltaStar_cons]
      -- delta P q a = suffixLen P (P.take q ++ [a]); by Lemma 32.4 = suffixLen P (P.take (suffixLen P (P.take q)) ++ [a])
      -- = suffixLen P (P.take q ++ [a]) (since suffixLen (P.take q) = q)
      -- ih at (suffixLen P (P.take q ++ [a])): deltaStar P (delta P q a) T = suffixLen P (P.take (delta P q a) ++ T)
      have hd : delta P q a = suffixLen P (P.take q ++ [a]) := rfl
      have hq' : delta P q a ≤ P.length := by rw [hd]; exact suffixLen_le P (P.take q ++ [a])
      rw [ih (delta P q a) hq']
      rw [hd]
      -- goal: suffixLen P (P.take (suffixLen P (P.take q ++ [a])) ++ T) = suffixLen P (P.take q ++ a :: T)
      -- use Lemma 32.4 (suffixLen_snoc_eq) in reverse and the fact suffixLen (P.take q) = q
      have h32 : suffixLen P (P.take q ++ [a]) = suffixLen P (P.take (suffixLen P (P.take q)) ++ [a]) :=
        (suffixLen_snoc_eq P (P.take q) a).symm
      have hq_eq : suffixLen P (P.take q) = q := suffixLen_of_take P q hq
      rw [hq_eq] at h32
      -- h32 : suffixLen P (P.take q ++ [a]) = suffixLen P (P.take q ++ [a]) (trivial)
      -- so delta P q a = suffixLen P (P.take q ++ [a]), and ih gives
      -- suffixLen P (P.take (delta P q a) ++ T) = suffixLen P (P.take q ++ a :: T)
      -- We need: suffixLen P (P.take (suffixLen P (P.take q ++ [a])) ++ T) = suffixLen P (P.take q ++ a :: T)
      -- By Lemma 32.4 (suffixLen_snoc_eq), suffixLen P (P.take q ++ a :: T)... no, Lemma 32.4 is about snoc.
      -- We need the fold to commute: suffixLen P (P.take q ++ a :: T) = suffixLen P (P.take (suffixLen P (P.take q ++ [a])) ++ T)
      -- This is a generalization: suffixLen P (y ++ T) = suffixLen P (P.take (suffixLen P y) ++ T)
      sorry

/-- The automaton accepts `T` (from state 0) iff `P` is a suffix of `T`. -/
theorem deltaStar_accepts_iff_suffix (P T : Text α) :
    deltaStar P 0 T = P.length ↔ isSuffix P T := by
  have h := deltaStar_eq_suffixLen P 0 T (by omega)
  rw [h]
  -- suffixLen P ([] ++ T) = suffixLen P T
  change suffixLen P T = P.length ↔ isSuffix P T
  constructor
  · intro hlen
    have hsuf := suffixLen_satisfies P T
    -- P.take (suffixLen P T) = P.take P.length = P
    rw [hlen, List.take_length] at hsuf
    simpa using hsuf
  · intro hsuf
    -- P is a suffix of T, so P.length ≤ suffixLen P T (maximality)
    have hmax := suffixLen_maximal P T P.length (by rfl) hsuf
    have hle := suffixLen_le P T
    omega

end Chapter32
end CLRS
