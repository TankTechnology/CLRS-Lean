import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# 5.3. Fisher–Yates choice vectors

The choice at position `i` is an offset in `Fin (n - i)`, hence selects one of
the positions `i, ..., n - 1`.  The product sample space has cardinality `n!`.
-/

namespace CLRS
namespace Chapter05

/-- Independent finite choices used by forward Fisher–Yates. -/
def ChoiceVector (n : Nat) : Type := (i : Fin n) -> Fin (n - i.val)

instance (n : Nat) : Fintype (ChoiceVector n) :=
  inferInstanceAs (Fintype ((i : Fin n) -> Fin (n - i.val)))

instance (n : Nat) : DecidableEq (ChoiceVector n) :=
  inferInstanceAs (DecidableEq ((i : Fin n) -> Fin (n - i.val)))

/-- The cardinality of `ChoiceVector n` is `n!`. -/
theorem card_choiceVector (n : Nat) :
    Fintype.card (ChoiceVector n) = (Nat.factorial n : Nat) := by
  induction' n with n ih
  · simp [ChoiceVector]
  · calc
    Fintype.card (ChoiceVector (n + 1)) =
        Fintype.card (forall i : Fin (n + 1), Fin ((n + 1) - i.val)) := rfl
    _ = ∏ i : Fin (n + 1), Fintype.card (Fin ((n + 1) - i.val)) := by
      simp [Fintype.card_pi]
    _ = Fintype.card (Fin ((n + 1) - ((0 : Fin (n + 1)).val))) *
        (∏ i : Fin n, Fintype.card (Fin ((n + 1) - (Fin.succ i).val))) := by
      simp [Fin.prod_univ_succ]
    _ = (n + 1 : Nat) * (∏ i : Fin n, Fintype.card (Fin (n - i.val))) := by
      simp [Fintype.card_fin]
    _ = (n + 1) * Fintype.card (forall i : Fin n, Fin (n - i.val)) := by
      simp [Fintype.card_pi]
    _ = (n + 1) * Fintype.card (ChoiceVector n) := rfl
    _ = (n + 1) * (Nat.factorial n : Nat) := by rw [ih]
    _ = (Nat.factorial (n + 1) : Nat) := by
      simp [Nat.factorial_succ, mul_comm]

/-- Choices that always select the current position. -/
def zeroChoiceVector (n : Nat) : ChoiceVector n :=
  fun i => ⟨0, by omega⟩

/-- Choices that always select the last remaining position. -/
def lastChoiceVector (n : Nat) : ChoiceVector n :=
  fun i => ⟨n - i.val - 1, by omega⟩

end Chapter05
end CLRS
