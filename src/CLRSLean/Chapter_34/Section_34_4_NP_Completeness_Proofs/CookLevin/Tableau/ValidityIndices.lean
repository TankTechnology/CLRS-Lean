import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity

/-!
# Closed wire indices for stack-validity traces

The stack-validity trace is structurally recursive, but every fresh output
wire has a simple affine index.  These formulas are the arithmetic interface
needed by a uniform Cook--Levin serializer and by the final conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

/-- The output of group `i` in a serial exactly-one family is the last gate
of that group: the family start, plus every preceding group cost, plus the
last offset of the current `3m+4` block. -/
theorem exactlyOneFamilyGateTrace_output_eq (start n : Nat)
    (groups : Fin n → List CircuitBuilder.Wire) (i : Fin n) :
    (exactlyOneFamilyGateTrace start n groups).outputs i =
      start +
        (∑ previous : Fin i.val,
          (3 * (groups ⟨previous.val,
            Nat.lt_trans previous.isLt i.isLt⟩).length + 4)) +
        3 * (groups i).length + 3 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp only [exactlyOneFamilyGateTrace]
      split
      next hi =>
        simpa using ih (fun j => groups j.castSucc) ⟨i.val, hi⟩
      next hi =>
        have hilast : i = Fin.last n := by
          apply Fin.ext
          simp
          omega
        subst i
        rw [exactlyOneGateTrace_wire]
        simp only [exactlyOneFamilyGateTrace_length]
        congr 1

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

/-! ## Exact ordered cell blocks -/

/-- The literal six-gate block contributed by cell `i`: one negation of its
blank bit followed by active/nonblank Boolean equality. -/
def cellValidityGateBlock (start n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) (i : Fin n) :
    List CircuitGate :=
  [.not (blank i)] ++
    (CircuitBuilder.boolEqGateTrace (start + 6 * i.val + 1)
      (active i) (start + 6 * i.val)).gates

/-- The semantic `6n` cell-validity trace is exactly the ordered flattening of
its per-cell blocks. -/
theorem cellValidityGateTrace_gates_eq_blocks (start n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) :
    (cellValidityGateTrace start n active blank).gates =
      (List.ofFn fun i : Fin n =>
        cellValidityGateBlock start n active blank i).flatten := by
  induction n with
  | zero => simp [cellValidityGateTrace]
  | succ n ih =>
      simp only [cellValidityGateTrace]
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_concat,
        cellValidityGateTrace_length, ih]
      simp [cellValidityGateBlock]

/-- The literal mask-plus-cells block contributed by ordered stack `j`. -/
noncomputable def stackValidityGateBlock
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (start : Nat) (wires : CfgWires tm H) (keys : Fin n → tm.K)
    (j : Fin n) : List CircuitGate :=
  let blockStart := start + (H + 1 + 6 * H) * j.val
  let k := keys j
  let mask := suffixOrGateTrace blockStart
    (List.ofFn fun i : Fin H => wires.stackHeight k i.succ)
  let active : Fin H → CircuitBuilder.Wire := fun i =>
    mask.outputs (Fin.cast (by simp) i)
  let blank : Fin H → CircuitBuilder.Wire := fun i =>
    wires.stackCell k i (Fin.last (reachableAlphabet tm k).card)
  let cells := cellValidityGateTrace (blockStart + (H + 1)) H active blank
  mask.gates ++ cells.gates

/-- The semantic ordered-stack family is exactly the flattening of its
mask-plus-cells blocks. -/
theorem stackValidityFamilyGateTrace_gates_eq_blocks
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H)
    (n : Nat) (keys : Fin n → tm.K) :
    (stackValidityFamilyGateTrace start wires n keys).gates =
      (List.ofFn fun j : Fin n =>
        stackValidityGateBlock start wires keys j).flatten := by
  induction n with
  | zero => simp [stackValidityFamilyGateTrace]
  | succ n ih =>
      simp only [stackValidityFamilyGateTrace]
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_concat,
        stackValidityFamilyGateTrace_length, ih]
      simp [stackValidityGateBlock, suffixOrGateTrace_length]
      congr 2 <;> ring

end CLRS.Chapter34.Turing.CookLevin
