import CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor

/-!
Euclid follows the public first-argument recursion. Its returned counter charges
one remainder/division step at each nonterminal call. The value refines the
public function and the count equals the legacy division recurrence with
swapped arguments; no bit-cost model is claimed.
-/

namespace CLRS.Chapter31

def euclidWithCount : Nat → Nat → Nat × Nat
  | 0, b => (b, 0)
  | a + 1, b =>
    let next := euclidWithCount (b % (a + 1)) (a + 1)
    (next.1, next.2 + 1)
termination_by a _ => a
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

theorem euclidWithCount_spec (a b : Nat) :
    euclidWithCount a b = (euclid a b, euclidDivisions b a) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    cases a with
    | zero => simp [euclidWithCount, euclid, euclidDivisions]
    | succ a =>
      rw [euclidWithCount, ih _ (Nat.mod_lt _ (Nat.succ_pos _)), euclid, euclidDivisions]
      simp [Nat.add_comm]

@[simp] theorem euclidWithCount_value (a b : Nat) : (euclidWithCount a b).1 = euclid a b := by
  rw [euclidWithCount_spec]

@[simp] theorem euclidWithCount_count (a b : Nat) :
    (euclidWithCount a b).2 = euclidDivisions b a := by rw [euclidWithCount_spec]

end CLRS.Chapter31
