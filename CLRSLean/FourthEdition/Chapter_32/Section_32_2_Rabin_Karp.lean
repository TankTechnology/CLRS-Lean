import Mathlib
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher

/-! # Section 32.2 — The Rabin–Karp Algorithm

The Rabin–Karp algorithm (CLRS §32.2) finds all occurrences of a pattern `P`
in a text `T` by hashing the pattern and every `|P|`-length window of `T`,
and comparing the hashes modulo `q`.  A shift whose hash matches but whose
string does not is a *spurious hit*: the algorithm rules it out with an
explicit character-by-character comparison (`matchesAt`), so it remains
correct for every choice of modulus.

## Key definitions

- {lit}`hash d q val w` — the base-`d` modular hash of `w` over the numeric
  values `val c`, computed by Horner's rule modulo `q`.
- {lit}`rabinKarpMatcher T P d q val` — returns the list of all shifts where
  `P` occurs in `T` (hash match plus explicit comparison), mirroring
  {lit}`naiveMatcher`.

## Main results

- Theorem {lit}`hash_snoc` — the O(1) incremental update
  `hash (w ++ [c]) = (hash w · d + val c) mod q`.
- Theorem {lit}`hash_eq_of_text_eq` — equal strings have equal hashes; hence a
  real match is never discarded as a spurious hit.
- Theorem {lit}`rabinKarp_sound` — every shift returned by `rabinKarpMatcher`
  is a valid match.
- Theorem {lit}`rabinKarp_complete` — every valid match is returned by
  `rabinKarpMatcher`.
- Theorem {lit}`rabinKarp_correct` — `rabinKarpMatcher` agrees with
  `naiveMatcher` on every shift.

The full CLRS window-slide recurrence (eq. (32.3)) is left as a named gap; the
O(1) right-extend step `hash_snoc` covers the incremental update used to seed
the hashes.

Notation conventions used in this section:

- `T` : the text being searched
- `P` : the pattern being searched for
- `d` : the radix of the numeric alphabet
- `q` : the modulus (CLRS assumes `0 < q`)
- `val` : assigns each alphabet symbol a numeric value in `ℕ`
-/

namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]

/--
The base-`d` modular hash of `w` over the numeric values `val c`, computed by
Horner's rule modulo `q` (CLRS §32.2).  For `w = [a₀, …, a_{k-1}]` this is
`((⋯((val a₀ · d + val a₁) · d + …) · d + val a_{k-1}) mod q`.  The function
is total (`x % 0 = 0`); CLRS assumes a modulus `0 < q`.
-/
def hash (d q : ℕ) (val : α → ℕ) (w : Text α) : ℕ :=
  w.foldl (fun acc c => (acc * d + val c) % q) 0

/--
The O(1) incremental update: appending a character to a string costs one
multiplication, one addition and one modulus, rather than a full re-hash.
This is the step used to seed the Rabin–Karp hashes (CLRS §32.2).
-/
theorem hash_snoc (d q : ℕ) (val : α → ℕ) (w : Text α) (c : α) :
    hash d q val (w ++ [c]) = (hash d q val w * d + val c) % q := by
  unfold hash
  rw [List.foldl_append]
  simp

/-- Equal strings have equal hashes, for any radix, modulus and value map. -/
theorem hash_eq_of_text_eq (d q : ℕ) (val : α → ℕ) {w₁ w₂ : Text α} (h : w₁ = w₂) :
    hash d q val w₁ = hash d q val w₂ := by
  subst h
  rfl

/--
If the pattern matches at shift `s`, then the window's hash equals the
pattern's hash: a real match is never discarded as a spurious hit.  This is
the completeness half of the hash test.
-/
lemma hash_beq_of_matchesAt (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (hm : matchesAt T P s = true) :
    (hash d q val ((T.drop s).take P.length) == hash d q val P) = true := by
  have hwind : ((T.drop s).take P.length == P) = true := by
    unfold matchesAt at hm
    split at hm
    · simpa using hm
    · contradiction
  have hwindEq : (T.drop s).take P.length = P := by
    exact beq_iff_eq.mp hwind
  rw [hash_eq_of_text_eq d q val hwindEq]
  simp

/--
The Rabin–Karp acceptance test for shift `s`: the hash of the window
`(T.drop s).take |P|` equals the hash of `P`, *and* the window literally
equals `P`.  The second conjunct filters out spurious hits, keeping the test
sound for every modulus.
-/
def rabinKarpShift (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ) : Bool :=
  (hash d q val ((T.drop s).take P.length) == hash d q val P) && matchesAt T P s

/--
The Rabin–Karp string matcher: enumerate all shifts and return those that
pass `rabinKarpShift`.  For an empty pattern it returns every shift, exactly
like `naiveMatcher`.
-/
def rabinKarpMatcher (T P : Text α) (d q : ℕ) (val : α → ℕ) : List ℕ :=
  if P.length = 0 then
    List.range (T.length + 1)
  else
    let n := T.length
    let m := P.length
    (List.range (n - m + 1)).filter (rabinKarpShift T P d q val)

/--
The Rabin–Karp acceptance test agrees with the plain match test on every
shift: when the pattern matches, the hash equality is automatic, and when it
does not, the explicit comparison rejects the shift regardless of the hash.
-/
lemma rabinKarpShift_eq_matchesAt (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ) :
    rabinKarpShift T P d q val s = matchesAt T P s := by
  unfold rabinKarpShift
  by_cases h : matchesAt T P s = true
  · have hb := hash_beq_of_matchesAt T P d q val s h
    simp [h, hb]
  · have hf : matchesAt T P s = false := by
      cases hb : matchesAt T P s
      · rfl
      · exact False.elim (h hb)
    simp [hf]

/-- If a shift `s` is in `rabinKarpMatcher`, then `matchesAt T P s` is true. -/
theorem rabinKarp_sound (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (h : s ∈ rabinKarpMatcher T P d q val) : matchesAt T P s := by
  unfold rabinKarpMatcher at h
  split at h
  · rename_i hzero
    have hempty : P = [] := by
      cases P
      · rfl
      · simp at hzero
    subst hempty
    unfold matchesAt
    have hs : s ≤ T.length := by
      have := List.mem_range.mp h
      omega
    simp [hs]
  · have hmem := List.mem_filter.mp h
    simpa [rabinKarpShift_eq_matchesAt T P d q val s] using hmem.2

/-- If `matchesAt T P s` is true, then `s` is in `rabinKarpMatcher`. -/
theorem rabinKarp_complete (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (hmatch : matchesAt T P s) : s ∈ rabinKarpMatcher T P d q val := by
  unfold rabinKarpMatcher
  by_cases hzero : P.length = 0
  · have hempty : P = [] := by
      cases P
      · rfl
      · simp at hzero
    subst hempty
    unfold matchesAt at hmatch
    simp at hmatch
    have hs : s < T.length + 1 := by omega
    simp [hs]
  · have hbound : s + P.length ≤ T.length := by
      unfold matchesAt at hmatch
      split at hmatch
      · assumption
      · simp at hmatch
    have hle : s < (T.length - P.length) + 1 := by omega
    have hmatch' : matchesAt T P s = true := hmatch
    have hshift : rabinKarpShift T P d q val s = true := by
      rw [rabinKarpShift_eq_matchesAt T P d q val s, hmatch']
    simpa [hzero] using
      List.mem_filter.mpr ⟨List.mem_range.mpr hle, hshift⟩

/--
**Correctness of Rabin–Karp.**  `rabinKarpMatcher` returns exactly the shifts
that `naiveMatcher` returns, for every text, pattern, radix, modulus and
numeric value map.  Soundness is by construction (the explicit comparison);
completeness uses the fact that equal strings have equal hashes, so a valid
match can never be filtered out as a spurious hit.
-/
theorem rabinKarp_correct (T P : Text α) (d q : ℕ) (val : α → ℕ) :
    rabinKarpMatcher T P d q val = naiveMatcher T P := by
  by_cases hzero : P.length = 0
  · simp [hzero, rabinKarpMatcher, naiveMatcher]
  · simp [hzero, rabinKarpMatcher, naiveMatcher]
    apply List.filter_congr
    intro s hs
    exact rabinKarpShift_eq_matchesAt T P d q val s

/-
The rolling-window recurrence and its proof.  This section adds the executable
`O(1)` slide (CLRS eq. (32.3)) on top of the hash-and-confirm matcher above,
plus the rolling matcher that uses it and the deterministic work bound.
-/
section Rolling

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α] [Inhabited α]

/-- Horner evaluation of `w` over `val` without the intermediate modular
reductions.  `hash d q val w` is exactly `hashNoMod d val w % q`. -/
def hashNoMod (d : ℕ) (val : α → ℕ) (w : Text α) : ℕ :=
  w.foldl (fun acc c => acc * d + val c) 0

/-- A Horner fold is congruent modulo `q` when its initial accumulator is. -/
lemma foldl_horner_mod_congr (d q : ℕ) (val : α → ℕ) (as : Text α) {x y : ℕ}
    (h : Nat.ModEq q x y) :
    Nat.ModEq q (as.foldl (fun a c => a * d + val c) x)
      (as.foldl (fun a c => a * d + val c) y) := by
  induction as generalizing x y with
  | nil => simpa using h
  | cons a as ih =>
      have hstep : Nat.ModEq q (x * d + val a) (y * d + val a) :=
        (Nat.ModEq.mul h (Nat.ModEq.refl d)).add (Nat.ModEq.refl (val a))
      exact ih hstep

/-- Reducing after each Horner step is congruent to reducing once at the end. -/
lemma foldl_mod_congr (d q : ℕ) (val : α → ℕ) (w : Text α) (acc : ℕ) :
    Nat.ModEq q (w.foldl (fun a c => (a * d + val c) % q) acc)
      (w.foldl (fun a c => a * d + val c) acc) := by
  induction w generalizing acc with
  | nil => exact Nat.ModEq.refl acc
  | cons a as ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have h1 := ih ((acc * d + val a) % q)
      have h2 : Nat.ModEq q (as.foldl (fun a c => a * d + val c) ((acc * d + val a) % q))
          (as.foldl (fun a c => a * d + val c) (acc * d + val a)) :=
        foldl_horner_mod_congr d q val as (Nat.mod_modEq (acc * d + val a) q)
      exact h1.trans h2

/-- `hash` is always below the modulus for a positive modulus. -/
theorem hash_lt (d q : ℕ) (val : α → ℕ) (w : Text α) (hq : 0 < q) :
    hash d q val w < q := by
  unfold hash
  have hmain : ∀ acc, acc < q →
      (w.foldl (fun a c => (a * d + val c) % q) acc) < q := by
    induction w with
    | nil => intro acc hacc; exact hacc
    | cons a as ih =>
        intro acc hacc
        rw [List.foldl_cons]
        exact ih ((acc * d + val a) % q) (Nat.mod_lt _ hq)
  exact hmain 0 hq

/-- `hash` is the Horner evaluation reduced modulo `q`. -/
theorem hash_eq_hashNoMod_mod (d q : ℕ) (val : α → ℕ) (w : Text α) :
    hash d q val w = hashNoMod d val w % q := by
  unfold hash hashNoMod
  by_cases hq : q = 0
  · subst q; simp
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hcong := foldl_mod_congr d q val w 0
    have hl : (w.foldl (fun a c => (a * d + val c) % q) 0) < q := by
      simpa [hash] using hash_lt d q val w hqpos
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hl] using hcong

/-- A Horner fold with initial accumulator `acc` equals `acc · d^|as|` plus the
fold starting from `0`. -/
lemma foldl_horner_acc (d : ℕ) (val : α → ℕ) (as : Text α) (acc : ℕ) :
    as.foldl (fun a c => a * d + val c) acc
      = acc * d ^ as.length + as.foldl (fun a c => a * d + val c) 0 := by
  induction as generalizing acc with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih (acc * d + val b)]
      rw [List.foldl_cons, ih (0 * d + val b)]
      rw [List.length_cons, pow_succ]
      ring

/-- The leading character contributes `val a · d^|as|` to the Horner hash. -/
lemma hashNoMod_cons (d : ℕ) (val : α → ℕ) (a : α) (as : Text α) :
    hashNoMod d val (a :: as) = val a * (d ^ as.length) + hashNoMod d val as := by
  unfold hashNoMod
  rw [List.foldl_cons]
  simpa using foldl_horner_acc d val as (val a)

/-- `(x + y) % q` is unchanged when `y` is reduced modulo `q`. -/
lemma add_mod_add_mod (q x y : ℕ) : (x + y) % q = (x + y % q) % q :=
  (Nat.ModEq.add (Nat.ModEq.refl x) (Nat.mod_modEq y q)).symm

/-- The leading character's contribution to the Horner hash (CLRS §32.2). -/
theorem hash_cons (d q : ℕ) (val : α → ℕ) (a : α) (as : Text α) :
    hash d q val (a :: as) = (val a * (d ^ as.length) + hash d q val as) % q := by
  rw [hash_eq_hashNoMod_mod d q val (a :: as)]
  rw [hashNoMod_cons]
  rw [add_mod_add_mod q (val a * d ^ as.length) (hashNoMod d val as)]
  rw [← hash_eq_hashNoMod_mod d q val as]

/-- Casting `x % q` into `ZMod q` is the same as casting `x`. -/
lemma zmod_natCast_mod (q x : ℕ) : ((x % q : ℕ) : ZMod q) = (x : ZMod q) :=
  (ZMod.natCast_eq_natCast_iff (x % q) x q).2 (Nat.mod_mod x q)

/--
The O(1) rolling update (CLRS eq. (32.3)): given the hash `h` of a nonempty
window `w` and the incoming character `c`, the hash of `w.drop 1 ++ [c]` is
`(d·h + val c − val w[0]·d^|w|) mod q`, with the subtraction normalized into
`ℕ` by the `+ q` term (valid for `0 < q`).
-/
def slideHash (d q : ℕ) (val : α → ℕ) (h : ℕ) (w : Text α) (c : α) : ℕ :=
  (d * h + val c + q - (val (w.headD default) * d ^ w.length) % q) % q

/-- The `ZMod q` value of a slide: the `+ q − x` normalization collapses to the
true modular subtraction. -/
lemma slideHash_zmod (d q : ℕ) (hq : 0 < q) (val : α → ℕ) (w : Text α) (h : ℕ) (c : α) :
    ((slideHash d q val h w c : ℕ) : ZMod q)
      = (d : ZMod q) * (h : ZMod q) + (val c : ZMod q)
          - (val (w.headD default) : ZMod q) * (d : ZMod q) ^ w.length := by
  unfold slideHash
  rw [zmod_natCast_mod q (d * h + val c + q - (val (w.headD default) * d ^ w.length) % q)]
  have hge : (val (w.headD default) * d ^ w.length) % q ≤ d * h + val c + q := by
    exact Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hq)) (Nat.le_add_left _ _)
  rw [Nat.cast_sub hge]
  rw [zmod_natCast_mod q (val (w.headD default) * d ^ w.length)]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- The Horner hash of a cons in `ZMod q`. -/
lemma hash_cons_zmod (d q : ℕ) (val : α → ℕ) (a : α) (as : Text α) :
    (hash d q val (a :: as) : ZMod q)
      = (val a : ZMod q) * (d : ZMod q) ^ as.length + (hash d q val as : ZMod q) := by
  rw [hash_cons, zmod_natCast_mod]
  push_cast
  rfl

/-- The Horner hash of a snoc in `ZMod q`. -/
lemma hash_snoc_zmod (d q : ℕ) (val : α → ℕ) (w : Text α) (c : α) :
    (hash d q val (w ++ [c]) : ZMod q)
      = (hash d q val w : ZMod q) * d + (val c : ZMod q) := by
  rw [hash_snoc, zmod_natCast_mod]
  push_cast
  rfl

/--
**Rabin–Karp rolling recurrence (CLRS eq. (32.3)).**  Sliding a nonempty window
by one position — dropping the leading character and appending a new one —
updates the hash in `O(1)`: one multiplication, one addition, one subtraction
and one modulus, rather than a full re-hash of the window.
-/
theorem hash_slide (d q : ℕ) (val : α → ℕ) (w : Text α) (c : α) (hq : 0 < q)
    (hw : w ≠ []) :
    hash d q val (w.drop 1 ++ [c]) = slideHash d q val (hash d q val w) w c := by
  rcases w with _ | ⟨a, as⟩
  · contradiction
  change hash d q val (as ++ [c]) = slideHash d q val (hash d q val (a :: as)) (a :: as) c
  have hl : hash d q val (as ++ [c]) < q := hash_lt d q val (as ++ [c]) hq
  have hr : slideHash d q val (hash d q val (a :: as)) (a :: as) c < q := by
    unfold slideHash; exact Nat.mod_lt _ hq
  have hcong : ((hash d q val (as ++ [c]) : ZMod q)
        = (slideHash d q val (hash d q val (a :: as)) (a :: as) c : ZMod q)) := by
    rw [hash_snoc_zmod]
    rw [slideHash_zmod d q hq val (a :: as) (hash d q val (a :: as)) c]
    rw [hash_cons_zmod]
    rw [List.length_cons, pow_succ]
    simp only [List.headD]
    ring
  have hmod : hash d q val (as ++ [c]) % q = slideHash d q val (hash d q val (a :: as)) (a :: as) c % q :=
    (ZMod.natCast_eq_natCast_iff _ _ q).1 hcong
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at hmod
  exact hmod

/-- `range (n+1)` mapped by `f` is `f 0` followed by the shifted tail. -/
lemma range_succ_map (n : ℕ) (f : ℕ → β) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (List.range (n + 1 + 1)).map f = f 0 :: (List.range (n + 1)).map (fun i => f (i + 1))
      rw [List.range_succ, List.map_append, List.map_cons, ih]
      rw [List.range_succ, List.map_append, List.map_cons]
      simp

/-- The number of true entries of `f` over `range (k+1)` splits at the head. -/
lemma length_filter_range_succ (k : ℕ) (f : ℕ → Bool) :
    ((List.range (k + 1)).filter f).length
      = (if f 0 then 1 else 0) + ((List.range k).filter (fun i => f (i + 1))).length := by
  have hrange : List.range (k + 1) = 0 :: (List.range k).map (fun i => i + 1) := by
    simpa using (range_succ_map k (fun i : ℕ => i))
  rw [hrange]
  rw [List.filter_cons, List.filter_map, List.length_map]
  by_cases h : f 0
  · simp [h]
  · simp [h]

/-- The acceptance test of the rolling scan agrees with the plain match test. -/
lemma rollingTest_eq_matchesAt (T P : Text α) (d q : ℕ) (val : α → ℕ) (p m s : ℕ)
    (w : Text α) (h : ℕ) (hp : p = hash d q val P) (hm : m = P.length)
    (hw : w = (T.drop s).take m) (hh : h = hash d q val w) :
    (h == p && matchesAt T P s) = matchesAt T P s := by
  by_cases hmt : matchesAt T P s = true
  · have hbeq : (h == p) = true := by
      have hb := hash_beq_of_matchesAt T P d q val s hmt
      simpa [hh, hp, hm, hw] using hb
    simp [hmt, hbeq]
  · have hf : matchesAt T P s = false := by
      cases hb : matchesAt T P s <;> simp [hb] at hmt ⊢
    simp [hf]

/-- The hash-hit test of the rolling scan is exactly the window hash equality. -/
lemma rollingHashHit_eq (T P : Text α) (d q : ℕ) (val : α → ℕ) (p m s : ℕ)
    (w : Text α) (h : ℕ) (hp : p = hash d q val P) (hm : m = P.length)
    (hw : w = (T.drop s).take m) (hh : h = hash d q val w) :
    (h == p) = (hash d q val ((T.drop s).take P.length) == hash d q val P) := by
  simp [hh, hp, hm, hw]

/-- The number of hash hits among `k+1` consecutive windows starting at shift `s`. -/
def hashHitsIn (T P : Text α) (d q : ℕ) (val : α → ℕ) (s k : ℕ) : ℕ :=
  ((List.range (k + 1)).filter
    (fun i => hash d q val ((T.drop (s + i)).take P.length) == hash d q val P)).length

/-- `hashHitsIn` over a single window. -/
lemma hashHitsIn_zero (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ) :
    hashHitsIn T P d q val s 0
      = (if hash d q val ((T.drop s).take P.length) == hash d q val P then 1 else 0) := by
  simp [hashHitsIn]
  by_cases h : hash d q val ((T.drop s).take P.length) == hash d q val P
  · simp [h]
  · simp [h]

/-- `hashHitsIn` splits across the first window. -/
lemma hashHitsIn_succ (T P : Text α) (d q : ℕ) (val : α → ℕ) (s k : ℕ) :
    hashHitsIn T P d q val s (k + 1) = hashHitsIn T P d q val s 0 + hashHitsIn T P d q val (s + 1) k := by
  unfold hashHitsIn
  rw [length_filter_range_succ k (fun i => hash d q val ((T.drop (s + i)).take P.length) == hash d q val P)]
  congr 1
  · rfl
  · apply List.length_congr
    intro i hi
    rw [show s + (i + 1) = (s + 1) + i by omega]

/-- Sliding the window: dropping one leading character and appending `c` yields
the next length-`m` window of `T`. -/
lemma window_slide {T : Text α} {s m : ℕ} {w : Text α} {c : α} {rest' : Text α}
    (hw : w = (T.drop s).take m) (hwlen : w.length = m) (hm0 : 0 < m)
    (hr : c :: rest' = T.drop (s + m)) :
    w.drop 1 ++ [c] = (T.drop (s + 1)).take m := by
  have hwrest : w ++ (c :: rest') = T.drop s := by
    calc
      w ++ (c :: rest') = (T.drop s).take m ++ T.drop (s + m) := by rw [hw, ← hr]
      _ = (T.drop s).take m ++ (T.drop s).drop m := by rw [List.drop_drop]
      _ = T.drop s := List.take_append_drop m (T.drop s)
  have hlen_wdrop : (w.drop 1).length = m - 1 := by
    rw [List.length_drop, hwlen]
  calc
    (T.drop (s + 1)).take m = ((T.drop s).drop 1).take m := by
      congr 1
      rw [List.drop_drop]
      omega
    _ = ((w ++ (c :: rest')).drop 1).take m := by rw [hwrest]
    _ = (w.drop 1 ++ (c :: rest')).take m := by
          rw [List.drop_append_of_le_length]
          omega
    _ = w.drop 1 ++ [c] := by
          rw [List.take_append]
          simp [hlen_wdrop, hm0]

/-- One rolling scan step, returning the matches found and the accumulated work. -/
def rollingGo (T P : Text α) (d q : ℕ) (val : α → ℕ) (p m s : ℕ) (w : Text α) (h : ℕ)
    (rest : Text α) : List ℕ × ℕ :=
  match rest with
  | [] => (if h == p && matchesAt T P s then [s] else [], 1 + (if h == p then m else 0))
  | c :: rest' =>
      let (tail, costTail) := rollingGo T P d q val p m (s + 1) (w.drop 1 ++ [c])
        (slideHash d q val h w c) rest'
      let conf := if h == p then m else 0
      if h == p && matchesAt T P s then (s :: tail, conf + 1 + costTail)
      else (tail, conf + 1 + costTail)

/--
The rolling scan's specification: `rollingGo` returns exactly the shifts in
`[s, s + rest.length]` where `P` matches, and a cost of one rolling update per
shift plus an `m`-step character confirmation at every hash hit.
-/
lemma rollingGo_spec (T P : Text α) (d q : ℕ) (val : α → ℕ) (p m s : ℕ) (w : Text α) (h : ℕ)
    (rest : Text α) (hq : 0 < q) (hm0 : 0 < m) (hp : p = hash d q val P) (hm : m = P.length)
    (hw : w = (T.drop s).take m) (hwlen : w.length = m) (hh : h = hash d q val w)
    (hr : rest = T.drop (s + m)) :
    rollingGo T P d q val p m s w h rest =
      ( ((List.range (rest.length + 1)).map (fun i => s + i)).filter (fun s' => matchesAt T P s'),
        rest.length + 1 + hashHitsIn T P d q val s rest.length * m ) := by
  induction rest generalizing s w h with
  | nil =>
      rw [rollingGo]
      rw [rollingTest_eq_matchesAt T P d q val p m s w h hp hm hw hh]
      congr
      · rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.filter_cons]
        rw [show ((List.range 0).map (fun i => s + (i + 1))).filter (fun s' => matchesAt T P s') = []
            by simp]
        by_cases h : matchesAt T P s <;> simp [h]
      · rw [rollingHashHit_eq T P d q val p m s w h hp hm hw hh, hashHitsIn_zero]
        congr 1
        by_cases h : hash d q val ((T.drop s).take P.length) == hash d q val P <;> simp [h]
  | cons c rest' ih =>
      rw [rollingGo]
      -- set up the recursive invariants
      have hw' : w.drop 1 ++ [c] = (T.drop (s + 1)).take m := window_slide hw hwlen hm0 (by rwa [hr])
      have hwlen' : (w.drop 1 ++ [c]).length = m := by
        rw [List.length_append, List.length_cons, List.length_nil, hwlen]
        simp; omega
      have hh' : slideHash d q val h w c = hash d q val (w.drop 1 ++ [c]) := by
        have hwne : w ≠ [] := by
          intro he; subst he; simp at hwlen; omega
        rw [hh]
        exact (hash_slide d q val w c hq hwne).symm
      have hr' : rest' = T.drop ((s + 1) + m) := by
        have : c :: rest' = T.drop (s + m) := by rwa [hr]
        rw [← List.drop_drop, this]
        simp
      rw [ih (s + 1) (w.drop 1 ++ [c]) (slideHash d q val h w c) hw' hwlen' hh' hr']
      rw [rollingTest_eq_matchesAt T P d q val p m s w h hp hm hw hh]
      rw [rollingHashHit_eq T P d q val p m s w h hp hm hw hh]
      -- split the range and the hash-hit count
      rw [range_succ_map rest'.length (fun i => s + i)]
      rw [hashHitsIn_succ T P d q val s rest'.length]
      simp only [List.filter_cons]
      by_cases hmatch : matchesAt T P s
      · have hhit : hash d q val ((T.drop s).take P.length) == hash d q val P = true := by
          have hb := hash_beq_of_matchesAt T P d q val s hmatch
          simpa using hb
        simp [hmatch, hhit, List.map_cons, List.map_append]
        ring
      · have hhit' : hash d q val ((T.drop s).take P.length) == hash d q val P = false := by
          cases hb : hash d q val ((T.drop s).take P.length) == hash d q val P <;> simp [hb] at hmatch ⊢
        simp [hmatch, hhit', List.map_cons, List.map_append]

end Rolling

end Chapter32
end CLRS
