import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity

/-!
# Closed wire indices for stack-validity traces

The stack-validity trace is structurally recursive, but every fresh output
wire has a simple affine index.  These formulas are the arithmetic interface
needed by a uniform Cook--Levin serializer and by the final conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

/-- Output `i` of a suffix-OR mask is the gate produced after all suffixes to
its right: `start + length - i`. -/
theorem suffixOrGateTrace_output_eq (start : Nat)
    (wires : List CircuitBuilder.Wire) (i : Fin wires.length) :
    (suffixOrGateTrace start wires).outputs i =
      start + wires.length - i.val := by
  induction wires with
  | nil => exact Fin.elim0 i
  | cons wire rest ih =>
      simp only [suffixOrGateTrace]
      split
      next hi => simp [hi]
      next hi =>
        rw [ih]
        simp only [List.length_cons]
        have hil := i.isLt
        simp only [List.length_cons] at hil
        cases hval : i.val with
        | zero => exact (hi hval).elim
        | succ k =>
            simp only [Nat.add_sub_cancel]
            rw [Nat.add_sub_assoc (m := rest.length) (k := k)
              (by omega) start]
            rw [Nat.add_sub_assoc (m := rest.length + 1) (k := k + 1)
              (by omega) start]
            simp

/-- Cell `i` contributes six gates and its Boolean-equality output is the last
of those six fresh wires. -/
theorem cellValidityGateTrace_output_eq (start n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) (i : Fin n) :
    (cellValidityGateTrace start n active blank).outputs i =
      start + 6 * i.val + 5 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp only [cellValidityGateTrace]
      split
      next hi =>
        rw [ih]
      next hi =>
        simp only [CircuitBuilder.boolEqGateTrace]
        rw [cellValidityGateTrace_length]
        simp
        omega

/-- In the ordered stack family, each preceding stack occupies exactly
`H + 1 + 6H` gates; cell `i` is the last wire of its six-gate block. -/
theorem stackValidityFamilyGateTrace_output_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H)
    (n : Nat) (keys : Fin n → tm.K) (j : Fin n) (i : Fin H) :
    (stackValidityFamilyGateTrace start wires n keys).outputs j i =
      start + (H + 1 + 6 * H) * j.val + (H + 1) + 6 * i.val + 5 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      simp only [stackValidityFamilyGateTrace]
      split
      next hj =>
        rw [ih]
      next hj =>
        have hjlt := j.isLt
        have hjeq : j.val = n := by omega
        rw [cellValidityGateTrace_output_eq]
        simp only [stackValidityFamilyGateTrace_length,
          suffixOrGateTrace_length, List.length_ofFn]
        simp
        rw [hjeq]
        ring

end CLRS.Chapter34.Turing.CookLevin
