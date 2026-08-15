import Mathlib
import CLRSLean.FourthEdition.Chapter_11.Section_11_2_Chained_Hash_Tables

/-!
# CLRS Section 11.3 - Hash functions

Section 11.2 defines the predicate {lit}`IsUniversal` (CLRS equation (11.4)) and
proves, *from that hypothesis alone*, the universal-hashing costs
{lit}`universal_expected_collisions` and {lit}`universal_expected_search_cost`.
What was missing is an actual family that **satisfies** {lit}`IsUniversal`: until
now universality was an unwitnessed assumption.  This section closes that loop by
constructing a concrete universal family and, additionally, records the two
deterministic heuristics of CLRS §11.3.1-11.3.2.

Main results:

- Definition {lit}`divisionHash` and lemma {lit}`divisionHash_lt`: the division
  method {lit}`h(k) = k mod m` with its range bound (CLRS §11.3.1).
- Definition {lit}`multiplicationHash` and lemma {lit}`multiplicationHash_lt`:
  the multiplication method {lit}`h(k) = floor (m * frac (k * A))` with its range
  bound (CLRS §11.3.2).
- Definition {lit}`affineHash`: the prime-field affine family
  {lit}`h_{a,b}(k) = a * k + b` over the field {lit}`ZMod p` (`p` prime).  This is
  the number-theoretic dot-product construction of CLRS §11.3.3 in the exact case
  {lit}`m = p`.
- Theorem {lit}`affineHash_isUniversal`: the affine family satisfies
  {lit}`IsUniversal` (CLRS Theorem 11.5).  Two distinct keys collide exactly when
  the multiplier {lit}`a` is zero, an event of probability {lit}`1/p = 1/m`, so
  the collision probability is at most {lit}`1/m`.  This provides the first
  concrete witness discharging the {lit}`IsUniversal` hypothesis.
- Theorems {lit}`affineHash_expected_collisions` and
  {lit}`affineHash_expected_search_cost`: the §11.2 universal-hashing bounds
  instantiated on the concrete family, i.e. expected collisions {lit}`≤ n/m` and
  expected search cost {lit}`≤ 1 + n/m` with no {lit}`IsUniversal` hypothesis left
  open.

Status: `proved`.  A concrete universal family exists and instantiates the
downstream §11.2 bounds; the deterministic heuristics are recorded with range
lemmas.

Notation conventions used in this section:

- `p` : a prime modulus, so `ZMod p` is a finite field of `p` elements
- `m` : the table size (`m = p` for the affine family)
- `a`, `b` : the slope and intercept of an affine hash `h_{a,b}(k) = a * k + b`
- `A` : the multiplicative constant in `(0, 1)` of the multiplication method

Current gaps: the general mod-`m` reduction of CLRS Theorem 11.5 (arbitrary
`m ≤ p` via an outer `mod m`) is a refinement of the exact `m = p` construction
proved here; both give a genuine universal family discharging {lit}`IsUniversal`.
-/

namespace CLRS
namespace Chapter11

open CLRS.Probability

/-! ## Deterministic hashing heuristics (CLRS §11.3.1-11.3.2) -/

/--
The **division method** (CLRS §11.3.1): map a natural-number key to the remainder
{lit}`k mod m`.  This is a deterministic hash into `{0, …, m-1}`.
-/
def divisionHash (m k : ℕ) : ℕ := k % m

/-- The division method lands in the bucket range {lit}`{0, …, m-1}`. -/
theorem divisionHash_lt (m k : ℕ) (hm : 0 < m) : divisionHash m k < m :=
  Nat.mod_lt _ hm

/--
The **multiplication method** (CLRS §11.3.2): with a real constant `A`, take the
fractional part of {lit}`k * A`, scale by `m`, and take the floor.  This is a
deterministic hash into `{0, …, m-1}`.
-/
noncomputable def multiplicationHash (m : ℕ) (A : ℝ) (k : ℕ) : ℕ :=
  ⌊(m : ℝ) * Int.fract ((k : ℝ) * A)⌋.toNat

/-- The multiplication method lands in the bucket range {lit}`{0, …, m-1}`. -/
theorem multiplicationHash_lt (m : ℕ) (A : ℝ) (k : ℕ) (hm : 0 < m) :
    multiplicationHash m A k < m := by
  unfold multiplicationHash
  have hfract_lt : Int.fract ((k : ℝ) * A) < 1 := Int.fract_lt_one _
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlt : (m : ℝ) * Int.fract ((k : ℝ) * A) < (m : ℝ) := by
    calc (m : ℝ) * Int.fract ((k : ℝ) * A)
        < (m : ℝ) * 1 := by exact mul_lt_mul_of_pos_left hfract_lt hmpos
      _ = (m : ℝ) := by ring
  have h1 : ⌊(m : ℝ) * Int.fract ((k : ℝ) * A)⌋ < (m : ℤ) := by
    rw [Int.floor_lt]; push_cast; exact hlt
  omega

/-! ## A concrete universal family (CLRS Theorem 11.5)

We construct the prime-field affine family {lit}`h_{a,b}(k) = a * k + b` over the
finite field {lit}`ZMod p`.  With `m = p` this is exactly the number-theoretic
construction of CLRS §11.3.3.  The family is indexed by all pairs
{lit}`(a, b) ∈ ZMod p × ZMod p`, drawn uniformly.

Universality is genuinely number-theoretic: for distinct keys `x ≠ y`, the two
hash values agree iff {lit}`a * (x - y) = 0`.  In a field this forces `a = 0`
(since `x - y ≠ 0` is a unit), an event of probability exactly {lit}`1/p`. -/

/-- The canonical representative of a residue in `ZMod p` as an element of
`Fin p`, using the value map `ZMod.val`.  This lets the affine family land in the
`Fin m` codomain required by {lit}`IsUniversal`. -/
def toFin {p : ℕ} [NeZero p] (a : ZMod p) : Fin p := ⟨a.val, ZMod.val_lt a⟩

/-- The representative map `ZMod p → Fin p` is injective, because `ZMod.val` is. -/
theorem toFin_injective {p : ℕ} [NeZero p] : Function.Injective (toFin (p := p)) := by
  intro a b hab
  have hval : a.val = b.val := congrArg Fin.val hab
  exact ZMod.val_injective p hval

/--
The **prime-field affine hash family** (CLRS §11.3.3, Theorem 11.5, exact
`m = p` case): {lit}`h_{a,b}(k) = a * k + b`, computed in the field `ZMod p` and
represented in `Fin p`.  The index `(a, b)` ranges over `ZMod p × ZMod p`.
-/
def affineHash (p : ℕ) [NeZero p] (t : ZMod p × ZMod p) (k : ZMod p) : Fin p :=
  toFin (t.1 * k + t.2)

/--
**Theorem (CLRS Theorem 11.5).**  The prime-field affine family is universal: for
any two distinct keys, a uniformly random member collides on them with
probability at most {lit}`1/m` (here `m = p`).

This is the first concrete witness of the {lit}`IsUniversal` predicate from
Section 11.2, so the collision and search-cost bounds there are no longer
conditional on an unproven hypothesis.
-/
theorem affineHash_isUniversal (p : ℕ) [NeZero p] (hp : p.Prime) :
    IsUniversal (affineHash p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x y hxy
  -- The collision event `h x = h y` is exactly the event `a = 0`.
  have hiff : ∀ t : ZMod p × ZMod p,
      (affineHash p t x = affineHash p t y) ↔ (t.1 = 0) := by
    intro t
    constructor
    · intro h
      have h2 : t.1 * x + t.2 = t.1 * y + t.2 := toFin_injective h
      have h3 : t.1 * x = t.1 * y := add_right_cancel h2
      have h4 : t.1 * (x - y) = 0 := by rw [mul_sub, h3, sub_self]
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h5
      · exact absurd (sub_eq_zero.mp h5) hxy
    · intro h
      show affineHash p t x = affineHash p t y
      unfold affineHash
      rw [h]; simp
  -- Rewrite the collision indicator as the indicator of `a = 0`.
  have hfun :
      (fun t : ZMod p × ZMod p => indicator (affineHash p t x = affineHash p t y))
        = (fun t : ZMod p × ZMod p => indicator (t.1 = 0)) := by
    funext t
    by_cases h : t.1 = 0
    · simp [indicator, (hiff t).mpr h, h]
    · have hne : ¬ (affineHash p t x = affineHash p t y) := fun hc => h ((hiff t).mp hc)
      simp [indicator, hne, h]
  rw [hfun]
  -- The probability that the first coordinate is `0` is `1/card = 1/p`.
  have hcardZ : Fintype.card (ZMod p) ≠ 0 := Fintype.card_ne_zero
  have hmarg := fintypeExpect_fst (Ω₁ := ZMod p) (Ω₂ := ZMod p) hcardZ
    (fun a => indicator (a = 0))
  have hrw : (fun t : ZMod p × ZMod p => indicator (t.1 = 0))
      = (fun t : ZMod p × ZMod p => (fun a : ZMod p => indicator (a = 0)) t.1) := rfl
  rw [hrw, hmarg, fintypeExpect_indicator_singleton, ZMod.card]

/--
**Corollary (concrete universal collision bound).**  Instantiating
{lit}`universal_expected_collisions` on the affine family: for a query key `x`
and `n` stored keys all distinct from `x`, the expected number of collisions
under a uniformly random affine hash is at most the load factor {lit}`n/m`
(`m = p`), with no {lit}`IsUniversal` hypothesis left open.
-/
theorem affineHash_expected_collisions (p : ℕ) [NeZero p] (hp : p.Prime) {n : ℕ}
    (x : ZMod p) (k : Fin n → ZMod p) (hk : ∀ i, k i ≠ x) :
    fintypeExpect (fun t : ZMod p × ZMod p =>
        ∑ i : Fin n, indicator (affineHash p t x = affineHash p t (k i)))
      ≤ (n : ℝ) / (p : ℝ) :=
  universal_expected_collisions (affineHash p) (affineHash_isUniversal p hp) x k hk

/--
**Corollary (concrete universal search-cost bound).**  Instantiating
{lit}`universal_expected_search_cost` on the affine family: the expected
search cost (one probe plus expected collisions) is at most {lit}`1 + n/m`
(`m = p`), with no {lit}`IsUniversal` hypothesis left open (CLRS Theorem 11.3).
-/
theorem affineHash_expected_search_cost (p : ℕ) [NeZero p] (hp : p.Prime) {n : ℕ}
    (x : ZMod p) (k : Fin n → ZMod p) (hk : ∀ i, k i ≠ x) :
    fintypeExpect (fun t : ZMod p × ZMod p =>
        1 + ∑ i : Fin n, indicator (affineHash p t x = affineHash p t (k i)))
      ≤ 1 + (n : ℝ) / (p : ℝ) := by
  haveI : Nonempty (ZMod p × ZMod p) := ⟨(0, 0)⟩
  exact universal_expected_search_cost (affineHash p) (affineHash_isUniversal p hp) x k hk

/-! ## The general mod-`m` affine family (CLRS Theorem 11.5, full form)

The exact `m = p` construction above reduces each hash value into `Fin p`.  CLRS
Theorem 11.5 instead uses a *larger* prime modulus `p` and an outer reduction
modulo the table size `m ≤ p`: `h_{a,b}(k) = ((a·k + b) mod p) mod m`.  This
subsection formalises that general family and proves it universal.

The proof is the standard counting argument of CLRS.  For distinct keys `x ≠ y`
and a nonzero multiplier `a`, the field values `r = a·x + b` and `s = a·y + b`
differ (else `a·(x - y) = 0` in the field `ZMod p`); the assignment
`(a,b) ↦ (r,s)` is injective.  A collision modulo `m` therefore corresponds to a
pair of distinct residues `r ≠ s` with `r ≡ s (mod m)`.  The number of such
residue pairs in `{0,…,p-1}²` is at most `p·(p-1)/m`, which gives the collision
probability bound `1/m`. -/

/-- The number of `s < p` strictly greater than `r` and congruent to `r` modulo
`m` is at most `(p - 1 - r) / m`. -/
lemma count_congruent_gt_le (p m r : ℕ) (hm : 0 < m) (hr : r < p) :
    (((Finset.range p).filter (fun s : ℕ => r < s ∧ s % m = r % m)).card : ℕ)
      ≤ (p - 1 - r) / m := by
  classical
  let f : ℕ → ℕ := fun s => (s - r) / m
  let S : Finset ℕ := (Finset.range p).filter (fun s : ℕ => r < s ∧ s % m = r % m)
  let T : Finset ℕ := Finset.Icc 1 ((p - 1 - r) / m)
  have hMt : Set.MapsTo f (S : Set ℕ) (T : Set ℕ) := by
    intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hsp, hscond⟩
    rcases hscond with ⟨hrs, hmod⟩
    have hslt : s < p := Finset.mem_range.mp hsp
    have hme : s ≡ r [MOD m] := by
      change s % m = r % m
      exact hmod
    have hle : r ≤ s := le_of_lt hrs
    have hdvd : m ∣ s - r := (Nat.modEq_iff_dvd' hle).mp hme.symm
    have hge : m ≤ s - r := by
      obtain ⟨q, hq⟩ := hdvd
      have hne : s - r ≠ 0 := by omega
      have hqpos : 1 ≤ q := by
        by_contra hqn
        have hq0 : q = 0 := by omega
        subst q
        simp at hq
        exact hne hq
      nlinarith
    have hpos : 1 ≤ (s - r) / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hge)
    have hsub : s - r ≤ p - 1 - r := by
      have hsp1 : s ≤ p - 1 := by omega
      exact Nat.sub_le_sub_right hsp1 r
    have hle2 : (s - r) / m ≤ (p - 1 - r) / m := Nat.div_le_div_right hsub
    simpa [f, T] using (Finset.mem_Icc.mpr ⟨hpos, hle2⟩)
  have hInj : (S : Set ℕ).InjOn f := by
    intro s hs t ht hf
    have hmes : s ≡ r [MOD m] := by
      have hmod : s % m = r % m := (Finset.mem_filter.mp hs).2.2
      change s % m = r % m
      exact hmod
    have hmet : t ≡ r [MOD m] := by
      have hmod : t % m = r % m := (Finset.mem_filter.mp ht).2.2
      change t % m = r % m
      exact hmod
    have hsle : r ≤ s := le_of_lt (Finset.mem_filter.mp hs).2.1
    have htle : r ≤ t := le_of_lt (Finset.mem_filter.mp ht).2.1
    have hdvdS : m ∣ s - r := (Nat.modEq_iff_dvd' hsle).mp hmes.symm
    have hdvdT : m ∣ t - r := (Nat.modEq_iff_dvd' htle).mp hmet.symm
    have hcal : s - r = t - r := by
      calc s - r = (s - r) / m * m := by rw [Nat.div_mul_cancel hdvdS]
        _ = (t - r) / m * m := by
              change f s * m = f t * m
              rw [hf]
        _ = t - r := by rw [Nat.div_mul_cancel hdvdT]
    omega
  have hle := Finset.card_le_card_of_injOn f hMt hInj
  have hT : T.card = (p - 1 - r) / m := by
    simp [T]
  rwa [hT] at hle

/-- The number of `s < p` strictly less than `r` and congruent to `r` modulo
`m` is at most `r / m`. -/
lemma count_congruent_lt_le (p m r : ℕ) (hm : 0 < m) (hr : r < p) :
    (((Finset.range p).filter (fun s : ℕ => s < r ∧ s % m = r % m)).card : ℕ)
      ≤ r / m := by
  classical
  let f : ℕ → ℕ := fun s => (r - s) / m
  let S : Finset ℕ := (Finset.range p).filter (fun s : ℕ => s < r ∧ s % m = r % m)
  let T : Finset ℕ := Finset.Icc 1 (r / m)
  have hMt : Set.MapsTo f (S : Set ℕ) (T : Set ℕ) := by
    intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hsp, hscond⟩
    rcases hscond with ⟨hsr, hmod⟩
    have hme : s ≡ r [MOD m] := by
      change s % m = r % m
      exact hmod
    have hle : s ≤ r := le_of_lt hsr
    have hdvd : m ∣ r - s := (Nat.modEq_iff_dvd' hle).mp hme
    have hge : m ≤ r - s := by
      obtain ⟨q, hq⟩ := hdvd
      have hne : r - s ≠ 0 := by omega
      have hqpos : 1 ≤ q := by
        by_contra hqn
        have hq0 : q = 0 := by omega
        subst q
        simp at hq
        exact hne hq
      nlinarith
    have hpos : 1 ≤ (r - s) / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hge)
    have hle2 : (r - s) / m ≤ r / m := Nat.div_le_div_right (Nat.sub_le r s)
    simpa [f, T] using (Finset.mem_Icc.mpr ⟨hpos, hle2⟩)
  have hInj : (S : Set ℕ).InjOn f := by
    intro s hs t ht hf
    have hmes : s ≡ r [MOD m] := by
      have hmod : s % m = r % m := (Finset.mem_filter.mp hs).2.2
      change s % m = r % m
      exact hmod
    have hmet : t ≡ r [MOD m] := by
      have hmod : t % m = r % m := (Finset.mem_filter.mp ht).2.2
      change t % m = r % m
      exact hmod
    have hsle : s ≤ r := le_of_lt (Finset.mem_filter.mp hs).2.1
    have htle : t ≤ r := le_of_lt (Finset.mem_filter.mp ht).2.1
    have hdvdS : m ∣ r - s := (Nat.modEq_iff_dvd' hsle).mp hmes
    have hdvdT : m ∣ r - t := (Nat.modEq_iff_dvd' htle).mp hmet
    have hcal : r - s = r - t := by
      calc r - s = (r - s) / m * m := by rw [Nat.div_mul_cancel hdvdS]
        _ = (r - t) / m * m := by
              change f s * m = f t * m
              rw [hf]
        _ = r - t := by rw [Nat.div_mul_cancel hdvdT]
    omega
  have hle := Finset.card_le_card_of_injOn f hMt hInj
  have hT : T.card = r / m := by
    simp [T]
  rwa [hT] at hle

/-- The number of pairs `(r, s)` with `r < p`, `s < p`, `r ≠ s`, and
`r % m = s % m` is at most `p·(p-1)/m`. -/
lemma congruentPair_count_le (p m : ℕ) (hm : 0 < m) :
    (((Finset.range p).product (Finset.range p)).filter
        (fun rs : ℕ × ℕ => rs.1 ≠ rs.2 ∧ rs.1 % m = rs.2 % m)).card
      ≤ (p : ℝ) * (p - 1 : ℝ) / (m : ℝ) := by
  classical
  let S : ℕ → Finset ℕ := fun r =>
    (Finset.range p).filter (fun s : ℕ => s ≠ r ∧ s % m = r % m)
  have hper : ∀ r ∈ Finset.range p, ((S r).card : ℝ) ≤ (p - 1 : ℝ) / (m : ℝ) := by
    intro r hr
    have hrp : r < p := Finset.mem_range.mp hr
    let Sneg : Finset ℕ := (Finset.range p).filter (fun s : ℕ => s < r ∧ s % m = r % m)
    let Spos : Finset ℕ := (Finset.range p).filter (fun s : ℕ => r < s ∧ s % m = r % m)
    have hsplit : S r = Sneg ∪ Spos := by
      ext s
      constructor
      · intro hs
        rcases Finset.mem_filter.mp hs with ⟨hsp, hne, hmod⟩
        have hslt : s < r ∨ r < s := by omega
        rw [Finset.mem_union]
        rcases hslt with hslt | hslt
        · exact Or.inl (Finset.mem_filter.mpr ⟨hsp, ⟨hslt, hmod⟩⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨hsp, ⟨hslt, hmod⟩⟩)
      · intro hs
        rw [Finset.mem_union] at hs
        rcases hs with hs | hs
        · rcases Finset.mem_filter.mp hs with ⟨hsp, hsr, hmod⟩
          exact Finset.mem_filter.mpr ⟨hsp, ⟨ne_of_lt hsr, hmod⟩⟩
        · rcases Finset.mem_filter.mp hs with ⟨hsp, hsr, hmod⟩
          exact Finset.mem_filter.mpr ⟨hsp, ⟨ne_of_gt hsr, hmod⟩⟩
    have hd : Disjoint Sneg Spos := by
      rw [Finset.disjoint_left]
      intro s hsneg hspos
      simp [Sneg, Spos] at hsneg hspos
      omega
    have hcard : (S r).card = Sneg.card + Spos.card := by
      rw [hsplit, Finset.card_union_of_disjoint hd]
    have hb1 : (Spos.card : ℝ) ≤ (p - 1 - r : ℝ) / (m : ℝ) := by
      calc
        (Spos.card : ℝ) ≤ (((p - 1 - r) / m : ℕ) : ℝ) := by
          exact_mod_cast (count_congruent_gt_le p m r hm hrp)
        _ ≤ (p - 1 - r : ℝ) / (m : ℝ) := by
          have hnum : ((p - 1 - r : ℕ) : ℝ) = (p - 1 - r : ℝ) := by
            rw [Nat.cast_sub (by omega : r ≤ p - 1)]
            rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
          rw [← hnum]
          exact Nat.cast_div_le
    have hb2 : (Sneg.card : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
      calc
        (Sneg.card : ℝ) ≤ ((r / m : ℕ) : ℝ) := by
          exact_mod_cast (count_congruent_lt_le p m r hm hrp)
        _ ≤ (r : ℝ) / (m : ℝ) := Nat.cast_div_le
    have hdiv : (r : ℝ) / (m : ℝ) + (p - 1 - r : ℝ) / (m : ℝ) = (p - 1 : ℝ) / (m : ℝ) := by
      rw [← add_div]
      ring
    rw [hcard, Nat.cast_add]
    calc (Sneg.card : ℝ) + (Spos.card : ℝ)
        ≤ (r : ℝ) / (m : ℝ) + (p - 1 - r : ℝ) / (m : ℝ) := add_le_add hb2 hb1
      _ = (p - 1 : ℝ) / (m : ℝ) := hdiv
  have hPsubset : (((Finset.range p).product (Finset.range p)).filter
        (fun rs : ℕ × ℕ => rs.1 ≠ rs.2 ∧ rs.1 % m = rs.2 % m))
      ⊆ (Finset.range p).biUnion (fun r : ℕ => ({r} : Finset ℕ).product (S r)) := by
    intro rs hrs
    rcases Finset.mem_filter.mp hrs with ⟨hrsprod, hne, hmod⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hrsprod
    rcases hrsprod with ⟨hrp, hsp⟩
    rw [Finset.mem_biUnion]
    refine ⟨rs.1, hrp, ?_⟩
    rw [Finset.product_eq_sprod, Finset.mem_product]
    refine ⟨Finset.mem_singleton.mpr rfl, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hsp, hne.symm, hmod.symm⟩
  have hcb := Finset.card_biUnion_le (s := Finset.range p)
    (t := fun r : ℕ => ({r} : Finset ℕ).product (S r))
  calc
    ((((Finset.range p).product (Finset.range p)).filter
        (fun rs : ℕ × ℕ => rs.1 ≠ rs.2 ∧ rs.1 % m = rs.2 % m)).card : ℝ)
        ≤ (((Finset.range p).biUnion (fun r : ℕ => ({r} : Finset ℕ).product (S r))).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card hPsubset)
    _ ≤ (∑ r ∈ (Finset.range p : Finset ℕ), ((({r} : Finset ℕ).product (S r)).card : ℝ)) := by
            exact_mod_cast hcb
    _ = (∑ r ∈ (Finset.range p : Finset ℕ), ((S r).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro r hr
            simp [Finset.card_product]
    _ ≤ (∑ r ∈ (Finset.range p : Finset ℕ), (p - 1 : ℝ) / (m : ℝ)) := by
            apply Finset.sum_le_sum
            intro r hr
            exact hper r hr
    _ = (p : ℝ) * (p - 1 : ℝ) / (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring

/-- The **general mod-`m` affine family** of CLRS Theorem 11.5:
`h_{a,b}(k) = ((a·k + b) mod p) mod m`, computed in the field `ZMod p` and then
reduced modulo the table size `m`.  The index `(a,b)` ranges over `ZMod p ×
ZMod p` with `a ≠ 0`; the codomain is `Fin m`. -/
def affineHashMod (p m : ℕ) [NeZero p] [NeZero m]
    (t : {a : ZMod p // a ≠ 0} × ZMod p) (k : ZMod p) : Fin m :=
  ⟨ZMod.val (t.1.1 * k + t.2) % m, Nat.mod_lt _ (NeZero.pos m)⟩

/--
**Theorem (CLRS Theorem 11.5, full mod-`m` form).**  The general affine family
{lit}`h_{a,b}(k) = ((a·k + b) mod p) mod m` (`a ≠ 0`) is universal: any two
distinct keys collide under a uniformly random member with probability at most
{lit}`1/m`.  This refines the exact `m = p` construction
{lit}`affineHash_isUniversal` to arbitrary table sizes `m ≤ p`.
-/
theorem affineHashMod_isUniversal (p m : ℕ) [NeZero p] [NeZero m] (hp : p.Prime) :
    IsUniversal (affineHashMod p m) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x y hxy
  let B : Finset ({a : ZMod p // a ≠ 0} × ZMod p) :=
    (Finset.univ : Finset ({a : ZMod p // a ≠ 0} × ZMod p)).filter
      (fun t => affineHashMod p m t x = affineHashMod p m t y)
  have hExpect :
      fintypeExpect (fun t : {a : ZMod p // a ≠ 0} × ZMod p =>
        indicator (affineHashMod p m t x = affineHashMod p m t y))
        = (B.card : ℝ) / (Fintype.card ({a : ZMod p // a ≠ 0} × ZMod p) : ℝ) := by
    unfold fintypeExpect indicator
    have hsum : (∑ t : {a : ZMod p // a ≠ 0} × ZMod p,
        (if affineHashMod p m t x = affineHashMod p m t y then (1 : ℝ) else 0))
        = (B.card : ℝ) := by
      simp [B]
    rw [hsum]
  rw [hExpect]
  let φ : ({a : ZMod p // a ≠ 0} × ZMod p) → ℕ × ℕ := fun t =>
    (ZMod.val (t.1.1 * x + t.2), ZMod.val (t.1.1 * y + t.2))
  have hφinj : (B : Set ({a : ZMod p // a ≠ 0} × ZMod p)).InjOn φ := by
    intro t1 ht1 t2 ht2 hφ
    rcases t1 with ⟨a1, b1⟩
    rcases t2 with ⟨a2, b2⟩
    have hfst : ZMod.val (a1.1 * x + b1) = ZMod.val (a2.1 * x + b2) :=
      congrArg Prod.fst hφ
    have hsnd : ZMod.val (a1.1 * y + b1) = ZMod.val (a2.1 * y + b2) :=
      congrArg Prod.snd hφ
    have h1 : a1.1 * x + b1 = a2.1 * x + b2 := ZMod.val_injective p hfst
    have h2 : a1.1 * y + b1 = a2.1 * y + b2 := ZMod.val_injective p hsnd
    have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hdiff : a1.1 - a2.1 = 0 := by
      have hsub : a1.1 * (x - y) = a2.1 * (x - y) := by
        calc a1.1 * (x - y) = (a1.1 * x + b1) - (a1.1 * y + b1) := by ring
          _ = (a2.1 * x + b2) - (a2.1 * y + b2) := by rw [h1, h2]
          _ = a2.1 * (x - y) := by ring
      have hmul : (a1.1 - a2.1) * (x - y) = 0 := by
        calc (a1.1 - a2.1) * (x - y) = a1.1 * (x - y) - a2.1 * (x - y) := by ring
          _ = 0 := by rw [hsub, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_right hxy0
    have ha : a1.1 = a2.1 := sub_eq_zero.mp hdiff
    have hb : b1 = b2 := by
      have hx : a1.1 * x + b1 = a1.1 * x + b2 := by
        rwa [← ha] at h1
      exact add_left_cancel hx
    exact Prod.ext (Subtype.ext ha) hb
  let C : Finset (ℕ × ℕ) :=
    (Finset.range p).product (Finset.range p) |>.filter
      (fun rs : ℕ × ℕ => rs.1 ≠ rs.2 ∧ rs.1 % m = rs.2 % m)
  have hIm : B.image φ ⊆ C := by
    intro rs hrs
    rcases (Finset.mem_image.mp hrs) with ⟨t, htB, hφt⟩
    rcases t with ⟨a, b⟩
    rw [← hφt]
    change (ZMod.val (a.1 * x + b), ZMod.val (a.1 * y + b)) ∈ C
    have hcoll : affineHashMod p m ⟨a, b⟩ x = affineHashMod p m ⟨a, b⟩ y :=
      (Finset.mem_filter.mp htB).2
    simp [C]
    constructor
    · constructor
      · exact ZMod.val_lt (a.1 * x + b)
      · exact ZMod.val_lt (a.1 * y + b)
    · constructor
      · intro hval
        have h : a.1 * x + b = a.1 * y + b := ZMod.val_injective p hval
        have h' : a.1 * (x - y) = 0 := by
          calc a.1 * (x - y) = (a.1 * x + b) - (a.1 * y + b) := by ring
            _ = 0 := by rw [h, sub_self]
        have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
        exact a.2 ((mul_eq_zero.mp h').resolve_right hxy0)
      · have hfin : (⟨ZMod.val (a.1 * x + b) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m)
            = ⟨ZMod.val (a.1 * y + b) % m, Nat.mod_lt _ (NeZero.pos m)⟩ := by
          simpa [affineHashMod] using hcoll
        exact congrArg Fin.val hfin
  have hcardIm : (B.image φ).card = B.card := Finset.card_image_of_injOn hφinj
  have hleC : B.card ≤ C.card := by
    rw [← hcardIm]
    exact Finset.card_le_card hIm
  have hBcard : (B.card : ℝ) ≤ (p : ℝ) * (p - 1 : ℝ) / (m : ℝ) := by
    have hCbound : (C.card : ℝ) ≤ (p : ℝ) * (p - 1 : ℝ) / (m : ℝ) :=
      congruentPair_count_le p m (NeZero.pos m)
    exact le_trans (by exact_mod_cast hleC) hCbound
  have hIcard : (Fintype.card ({a : ZMod p // a ≠ 0} × ZMod p) : ℝ) = (p : ℝ) * (p - 1 : ℝ) := by
    rw [Fintype.card_prod]
    have hne0 : Fintype.card {a : ZMod p // a = 0} = 1 := by
      rw [Fintype.card_subtype_eq]
    have h1 : Fintype.card {a : ZMod p // a ≠ 0} = p - 1 := by
      have hc := Fintype.card_subtype_compl (p := fun a : ZMod p => a = 0)
      rw [hne0, ZMod.card] at hc
      simpa [ne_eq, eq_comm] using hc
    rw [h1, ZMod.card]
    rw [Nat.cast_mul]
    rw [Nat.cast_sub hp.one_le]
    ring
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hIpos : 0 < (p : ℝ) * (p - 1 : ℝ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    nlinarith
  have hdiv : (B.card : ℝ) / ((p : ℝ) * (p - 1 : ℝ)) ≤ 1 / (m : ℝ) := by
    rw [div_le_iff₀ hIpos]
    calc (B.card : ℝ) ≤ (p : ℝ) * (p - 1 : ℝ) / (m : ℝ) := hBcard
      _ = (1 : ℝ) / (m : ℝ) * ((p : ℝ) * (p - 1 : ℝ)) := by
        field_simp [hmne]
  rw [hIcard]
  exact hdiv

end Chapter11
end CLRS
