import Mathlib
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables

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

end Chapter11
end CLRS
