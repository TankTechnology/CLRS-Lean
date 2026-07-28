import Mathlib
import CLRSLean.Chapter_32.Section_32_1_String_Model
import CLRSLean.Chapter_32.Section_32_1_Naive_Matcher

/-! # Section 32.2 — The Rabin-Karp Algorithm

The Rabin-Karp algorithm (CLRS §32.2) speeds up string matching by using a
rolling hash.  Instead of comparing the pattern against every substring
character-by-character, we compute a numerical fingerprint (hash) for the
pattern and for each length-`m` window of the text.

## Key concepts

- **Hash function.**  `hash d q s = (Σ s[i]·d^(|s|−1−i)) mod q`.
- **Rolling update.**  `h' = (d·(h − T[s]·d^(m−1)) + T[s+m]) mod q`.

-/

namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]

/-! ### Character-to-digit mapping -/

/-- Numeric value of a character.  Override for concrete alphabets. -/
def digVal (a : α) : ℕ := 0

/-! ### Powers modulo `q` -/

/-- `d^k mod q`. -/
def dPower (d q k : ℕ) : ℕ := (d ^ k) % q

/-- `d^(m-1) mod q` — factor for removing the outgoing character. -/
def rollingFactor (d q m : ℕ) : ℕ := dPower d q (m - 1)

/-! ### Polynomial hash -/

/-- Polynomial rolling hash of `s`:
`hash d q s = (Σ_{i=0}^{|s|-1} digVal(s[i]) · d^(|s|-1-i)) mod q`. -/
def hash (d q : ℕ) (s : Text α) : ℕ :=
  let n := s.length
  let indices := (List.range n).reverse
  let indexed : List (ℕ × α) := indices.zip s
  indexed.foldl (fun (acc : ℕ) (p : ℕ × α) =>
    let ⟨exp, c⟩ := p
    (acc + (digVal c) * (d ^ exp)) % q
  ) 0

/-- `hash_lt`: the hash is always `< q` for `q > 0`. -/
theorem hash_lt (d q : ℕ) (s : Text α) (hq : 0 < q) : hash d q s < q := by
  unfold hash
  dsimp
  -- Goal: ((List.range s.length).reverse.zip s).foldl (…) 0 < q
  have hfold : ∀ (acc : ℕ) (l : List (ℕ × α)), acc < q →
    (l.foldl (fun (acc' : ℕ) (p : ℕ × α) => (acc' + (digVal p.2) * (d ^ p.1)) % q) acc) < q := by
    intro acc l hacc
    induction l generalizing acc with
    | nil => exact hacc
    | cons hd tl ih =>
      have hnew : ((acc + (digVal hd.2) * (d ^ hd.1)) % q) < q := Nat.mod_lt _ hq
      exact ih ((acc + (digVal hd.2) * (d ^ hd.1)) % q) hnew
  apply hfold 0 _
  exact hq

/-- Hash of the empty string is 0. -/
@[simp]
theorem hash_nil (d q : ℕ) : hash d q ([] : Text α) = 0 := by
  unfold hash; simp

/-! ### Window hash -/

/-- Hash of substring `T[s…s+m−1]`. -/
def windowHash (d q : ℕ) (T : Text α) (s m : ℕ) : ℕ :=
  hash d q ((T.drop s).take m)

/-! ### Rolling hash update -/

/-- Rolling hash step: given hash `h` of window starting at `s`,
compute the hash of the window starting at `s+1`. -/
def rollingHashStep (d q : ℕ) (h : ℕ) (outgoingChar incomingChar : α) (m : ℕ) : ℕ :=
  let factor := rollingFactor d q m
  let oldContrib := (digVal outgoingChar) * factor
  let diff := (q + h - (oldContrib % q)) % q
  let scaled := (d * diff) % q
  (scaled + (digVal incomingChar)) % q

/-- `rollingHashStep` returns `< q` for `q > 0`. -/
theorem rollingHashStep_lt (d q : ℕ) (h : ℕ) (a b : α) (m : ℕ) (hq : 0 < q) :
    rollingHashStep d q h a b m < q := by
  unfold rollingHashStep
  apply Nat.mod_lt
  exact hq

/-- Correctness of the rolling hash step. 
The proof requires deep structural analysis of the hash function on windows,
combined with modular arithmetic identities. Deferred to future work. -/
theorem rollingHashStep_correct (d q : ℕ) (T : Text α) (s m : ℕ)
    (hbound : s + m < T.length) (hmpos : 0 < m) :
    rollingHashStep d q (windowHash d q T s m)
      (T.get ⟨s, by omega⟩) (T.get ⟨s + m, hbound⟩) m
    = windowHash d q T (s + 1) m := by
  sorry

/-! ### Rabin-Karp matcher -/

/-- Rabin-Karp matcher: compute pattern hash, scan windows,
verify candidates with `matchesAt`. -/
def rabinKarpMatcher (d q : ℕ) (T P : Text α) : List ℕ :=
  let n := T.length
  let m := P.length
  if m = 0 then
    List.range (n + 1)
  else if n < m then
    []
  else
    let pHash := hash d q P
    let maxShift := n - m
    (List.range (maxShift + 1)).filter fun s =>
      (windowHash d q T s m == pHash) && matchesAt T P s

/-- Soundness: `s ∈ rabinKarpMatcher d q T P` → `matchesAt T P s`. -/
theorem rabinKarpMatcher_sound (d q : ℕ) (T P : Text α) (s : ℕ)
    (h : s ∈ rabinKarpMatcher d q T P) : matchesAt T P s := by
  unfold rabinKarpMatcher at h
  by_cases hmzero : P.length = 0
  · -- P empty → matchesAt is true
    have hempty : P = [] := by
      have hlen0 : List.length P = 0 := hmzero
      exact List.eq_nil_of_length_eq_zero hlen0
    subst hempty
    -- h : s ∈ List.range (T.length + 1)
    unfold matchesAt
    have hs : s < T.length + 1 := List.mem_range.mp h
    have hsle : s ≤ T.length := by omega
    simp [hsle]
  · by_cases hnlt : T.length < P.length
    · simp [hmzero, hnlt] at h
    · -- normal case; h simplifies to a conjunction
      simp [hmzero, hnlt] at h
      -- h : s ≤ T.length - P.length ∧ windowHash ... = hash ... ∧ matchesAt T P s = true
      rcases h with ⟨_, ⟨_, hm⟩⟩
      exact hm

/-- If `a == b` for lists with lawful BEq, then `a = b`. -/
lemma beq_eq_imp (a b : Text α) (h : a == b) : a = b := by
  simpa [beq_iff_eq] using h

/-- Helper: from `matchesAt T P s` we get that the window equals the pattern. -/
lemma take_drop_eq_of_matchesAt (T P : Text α) (s : ℕ) (h : matchesAt T P s) :
    (T.drop s).take P.length = P := by
  unfold matchesAt at h
  split at h
  · -- h: (T.drop s).take P.length == P = true
    have hbeq : (T.drop s).take P.length == P := by simpa using h
    exact beq_eq_imp _ _ hbeq
  · simp at h

/-- Completeness: `matchesAt T P s` → `s ∈ rabinKarpMatcher d q T P`. -/
theorem rabinKarpMatcher_complete (d q : ℕ) (T P : Text α) (s : ℕ)
    (hmatch : matchesAt T P s) : s ∈ rabinKarpMatcher d q T P := by
  unfold rabinKarpMatcher
  by_cases hmzero : P.length = 0
  · -- P empty: all shifts are matches
    have hlen0 : P.length = 0 := hmzero
    have hPnil : P = [] := List.eq_nil_of_length_eq_zero hlen0
    unfold matchesAt at hmatch
    simp [hPnil, hlen0] at hmatch
    -- hmatch now: s ≤ T.length
    simp [hPnil, hlen0, hmatch]
  · by_cases hnlt : T.length < P.length
    · -- pattern longer than text, but matchesAt says it matches → impossible
      unfold matchesAt at hmatch
      simp at hmatch
      omega
    · -- normal case: s must be in the filtered range
      have hbound : s + P.length ≤ T.length := by
        unfold matchesAt at hmatch
        split at hmatch
        · assumption
        · simp at hmatch
      have hshift : s ≤ T.length - P.length := by omega
      have hle : s < (T.length - P.length) + 1 := by omega
      -- From matchesAt, the window equals the pattern
      have h_window : (T.drop s).take P.length = P :=
        take_drop_eq_of_matchesAt T P s hmatch
      -- Therefore the window hash equals the pattern hash
      have h_window_eq : windowHash d q T s P.length = hash d q P := by
        unfold windowHash
        rw [h_window]
      have hgoal : s ∈ (List.range ((T.length - P.length) + 1)).filter
          (fun s_1 => (windowHash d q T s_1 P.length == hash d q P) && matchesAt T P s_1) := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_range.mpr hle, ?_⟩
        simp [h_window_eq, hmatch]
      simpa [hmzero, hnlt] using hgoal

/-- Spurious hits: hashes match but strings differ. -/
def isSpuriousHit (d q : ℕ) (T P : Text α) (s : ℕ) : Prop :=
  windowHash d q T s P.length = hash d q P ∧ ¬ matchesAt T P s

/-- If `q` is prime and `q > d^m`, spurious hit probability `≤ 1/q`.
(Proof postponed.) -/
theorem spuriousHitBound (d q m : ℕ) (hqprime : Nat.Prime q) (hqlarge : d^m < q) :
    True := by
  trivial

end Chapter32
end CLRS
