import Mathlib

/-!
# CLRS Section 20.1 - van Emde Boas universe decomposition

This section isolates the arithmetic used by van Emde Boas trees: split a key
into a high cluster index and a low position, then reconstruct the original key.
The first-pass model uses an explicit cluster side length {lit}`m`.

Main results:

- Theorem {lit}`VEB.index_high_low`: reconstructing from {lit}`high` and
  {lit}`low` returns the original key.
- Theorems {lit}`VEB.high_index` and {lit}`VEB.low_index`: a bounded low
  component can be recovered after recombining a cluster index and offset.
- Theorem {lit}`VEB.index_lt`: bounded cluster and offset components recombine
  to a key inside the square universe.
- Theorem {lit}`VEB.high_lt`: if a key is below {lit}`m * m`, its high part is
  below {lit}`m`.
- Theorem {lit}`VEB.low_lt`: for positive {lit}`m`, the low part is below
  {lit}`m`.
-/

namespace CLRS
namespace Chapter20
namespace VEB

/-- High cluster index for side length {lit}`m`. -/
def high (m x : Nat) : Nat :=
  x / m

/-- Low offset inside a cluster for side length {lit}`m`. -/
def low (m x : Nat) : Nat :=
  x % m

/-- Recombine a high cluster and low offset for side length {lit}`m`. -/
def index (m hi lo : Nat) : Nat :=
  m * hi + lo

/-- Splitting a key into high/low parts and recombining returns the key. -/
theorem index_high_low {m x : Nat} :
    index m (high m x) (low m x) = x := by
  exact Nat.div_add_mod x m

/-- Recover the high cluster index after recombining a bounded low offset. -/
theorem high_index {m hi lo : Nat} (hlo : lo < m) :
    high m (index m hi lo) = hi := by
  have hm : 0 < m := Nat.zero_lt_of_lt hlo
  unfold high index
  rw [Nat.mul_comm m hi]
  rw [Nat.add_comm]
  rw [Nat.add_mul_div_right _ _ hm]
  rw [Nat.div_eq_of_lt hlo]
  simp

/-- Recover the low offset after recombining a bounded low offset. -/
theorem low_index {m hi lo : Nat} (hlo : lo < m) :
    low m (index m hi lo) = lo := by
  unfold low index
  rw [Nat.mul_comm m hi]
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hlo

/-- Bounded high and low components recombine to a key inside the square universe. -/
theorem index_lt {m hi lo : Nat} (hhi : hi < m) (hlo : lo < m) :
    index m hi lo < m * m := by
  unfold index
  have hsum : m * hi + lo < m * hi + m :=
    Nat.add_lt_add_left hlo (m * hi)
  have hsucc : hi + 1 <= m := Nat.succ_le_of_lt hhi
  have hmul : m * (hi + 1) <= m * m := Nat.mul_le_mul_left m hsucc
  calc
    m * hi + lo < m * hi + m := hsum
    _ = m * (hi + 1) := by ring
    _ <= m * m := hmul

/-- If {lit}`x < m * m`, then its high part is below {lit}`m`. -/
theorem high_lt {m x : Nat} (hx : x < m * m) :
    high m x < m := by
  exact Nat.div_lt_of_lt_mul hx

/-- The low part is always below a positive side length. -/
theorem low_lt {m x : Nat} (hm : 0 < m) :
    low m x < m := by
  exact Nat.mod_lt x hm

end VEB
end Chapter20
end CLRS
