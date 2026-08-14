import Mathlib.Tactic

/-!
# General Acyclic Boolean Circuits

This file gives an honest syntax for finite Boolean circuits whose gates may
refer to arbitrary earlier gates.  Gate order is the acyclicity witness:
`Circuit.WellFormed` requires every gate reference to be strictly smaller than
the gate's position, and it requires the designated output to exist.

The evaluator follows that same order, storing every computed gate value in an
array.  The prefix lemmas below expose the accumulator invariant used by later
encodings and Cook--Levin proofs.

Main results:

- `Circuit.wellFormedGatesAux_eq_true_iff`: the executable indexed traversal
  checks exactly the public quantified well-formedness condition.
- `Circuit.evalValues_size`: evaluation produces one value per gate.
- `Circuit.evalPrefix_push`: extending a gate prefix extends its value array by
  exactly the new gate's value over the preceding accumulator.
- `Circuit.evalPrefix_gate_value`: the value computed at any gate position uses
  exactly the values of the preceding gate prefix.
- `Circuit.evalValues_getElem_eq_evalPrefix`: the same gate value occurs in the
  complete evaluation array.
- `Circuit.evalValues_getElem_eq_gateEquation`: a well-formed gate satisfies a
  default-free equation over proof-carrying full-array predecessor lookups.
- `Circuit.eval_eq_getElem`: a well-formed circuit reads its existing output
  gate rather than the evaluator's out-of-bounds default.
-/

namespace CLRS

namespace Chapter34

/-! ## Syntax and well-formedness -/

/-- A Boolean-circuit gate.  Non-input gates refer to gate positions. -/
inductive CircuitGate : Type
  | input (inputIndex : Nat)
  | const (value : Bool)
  | not (source : Nat)
  | and (left right : Nat)
  | or (left right : Nat)
deriving DecidableEq, Repr

/-- A finite Boolean circuit with an explicit input arity and output gate. -/
structure Circuit where
  inputCount : Nat
  gates : List CircuitGate
  output : Nat
deriving DecidableEq, Repr

namespace CircuitGate

/-- A gate is valid at a position when its input is in range or all of its
gate dependencies occur strictly earlier in the circuit. -/
def ValidAt (inputCount i : Nat) : CircuitGate → Prop
  | .input inputIndex => inputIndex < inputCount
  | .const _ => True
  | .not source => source < i
  | .and left right | .or left right => left < i ∧ right < i

instance (inputCount i : Nat) (gate : CircuitGate) :
    Decidable (gate.ValidAt inputCount i) := by
  cases gate <;> simp only [ValidAt] <;> infer_instance

end CircuitGate

namespace Circuit

/-- A circuit is well formed when its output exists and each gate uses only a
declared input or strictly earlier gates. -/
def WellFormed (c : Circuit) : Prop :=
  c.output < c.gates.length ∧
    ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt c.inputCount i

/-- Check a gate list in one pass, carrying the index of its first gate. -/
def wellFormedGatesAux (inputCount nextIndex : Nat) : List CircuitGate → Bool
  | [] => true
  | gate :: gates =>
      decide (gate.ValidAt inputCount nextIndex) &&
        wellFormedGatesAux inputCount (nextIndex + 1) gates

/-- The indexed gate-list check is equivalent to validity at every position. -/
lemma wellFormedGatesAux_eq_true_iff (inputCount nextIndex : Nat)
    (gates : List CircuitGate) :
    wellFormedGatesAux inputCount nextIndex gates = true ↔
      ∀ i (hi : i < gates.length),
        (gates.get ⟨i, hi⟩).ValidAt inputCount (nextIndex + i) := by
  induction gates generalizing nextIndex with
  | nil => simp [wellFormedGatesAux]
  | cons gate gates ih =>
      rw [wellFormedGatesAux, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hgate, hgates⟩ i hi
        cases i with
        | zero => simpa using hgate
        | succ i =>
            have hi' : i < gates.length := by simpa using hi
            have hvalid := hgates i hi'
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid
      · intro hvalid
        constructor
        · simpa using hvalid 0 (by simp)
        · intro i hi
          have hnext := hvalid (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

instance (c : Circuit) : Decidable c.WellFormed := by
  let checked : Prop :=
    c.output < c.gates.length ∧
      wellFormedGatesAux c.inputCount 0 c.gates = true
  apply decidable_of_iff checked
  constructor
  · rintro ⟨houtput, hchecked⟩
    refine ⟨houtput, ?_⟩
    simpa using
      (wellFormedGatesAux_eq_true_iff c.inputCount 0 c.gates).mp hchecked
  · rintro ⟨houtput, hgates⟩
    refine ⟨houtput, (wellFormedGatesAux_eq_true_iff c.inputCount 0 c.gates).mpr ?_⟩
    simpa using hgates

end Circuit

/-! ## Gate-order evaluation -/

namespace CircuitGate

/-- Evaluate one gate from an input assignment and the values of the already
evaluated gate prefix. Out-of-range dependencies use the Boolean value false;
in a well-formed circuit those defaults are unreachable. -/
def evalWith (inputs : Nat → Bool) (values : Array Bool) : CircuitGate → Bool
  | .input i => inputs i
  | .const b => b
  | .not a => !(values.getD a false)
  | .and a b => values.getD a false && values.getD b false
  | .or a b => values.getD a false || values.getD b false

/-- The semantic equation for a gate stored in a complete value array.
Dependency cases carry proofs that their predecessor positions are earlier and
therefore in bounds; no default array lookup appears in this specification. -/
def GateEquation (inputs : Nat → Bool) (values : Array Bool)
    (gateIndex : Nat) (hgateIndex : gateIndex < values.size) : CircuitGate → Prop
  | .input inputIndex => values[gateIndex]'hgateIndex = inputs inputIndex
  | .const value => values[gateIndex]'hgateIndex = value
  | .not source =>
      ∃ hsource : source < gateIndex,
        values[gateIndex]'hgateIndex =
          !values[source]'(Nat.lt_trans hsource hgateIndex)
  | .and left right =>
      ∃ hleft : left < gateIndex, ∃ hright : right < gateIndex,
        values[gateIndex]'hgateIndex =
          (values[left]'(Nat.lt_trans hleft hgateIndex) &&
            values[right]'(Nat.lt_trans hright hgateIndex))
  | .or left right =>
      ∃ hleft : left < gateIndex, ∃ hright : right < gateIndex,
        values[gateIndex]'hgateIndex =
          (values[left]'(Nat.lt_trans hleft hgateIndex) ||
            values[right]'(Nat.lt_trans hright hgateIndex))

end CircuitGate

namespace Circuit

/-- Evaluate the circuit in gate order, retaining the value of every gate. -/
def evalValues (c : Circuit) (inputs : Nat → Bool) : Array Bool :=
  c.gates.foldl (fun values gate => values.push (gate.evalWith inputs values)) #[]

/-- Evaluate the designated output gate, defaulting to the Boolean value false
only when the output index is invalid. -/
def eval (c : Circuit) (inputs : Nat → Bool) : Bool :=
  (c.evalValues inputs).getD c.output false

private lemma evalFold_size (inputs : Nat → Bool) (gates : List CircuitGate)
    (initial : Array Bool) :
    (gates.foldl
      (fun values gate => values.push (gate.evalWith inputs values)) initial).size =
      initial.size + gates.length := by
  induction gates generalizing initial with
  | nil => simp
  | cons gate gates ih =>
      simp only [List.foldl_cons]
      rw [ih, Array.size_push]
      simp only [List.length_cons]
      omega

private lemma evalFold_getD_eq_initial (inputs : Nat → Bool)
    (gates : List CircuitGate) (initial : Array Bool) (i : Nat)
    (hi : i < initial.size) :
    (gates.foldl
      (fun values gate => values.push (gate.evalWith inputs values)) initial).getD
        i false = initial.getD i false := by
  induction gates generalizing initial with
  | nil => rfl
  | cons gate gates ih =>
      simp only [List.foldl_cons]
      rw [ih (initial := initial.push (gate.evalWith inputs initial))
        (hi := by rw [Array.size_push]; omega)]
      have hipush : i < (initial.push (gate.evalWith inputs initial)).size := by
        rw [Array.size_push]
        omega
      unfold Array.getD
      rw [dif_pos hipush, dif_pos hi]
      exact Array.getElem_push_lt hi

/-- Gate-order evaluation produces exactly one stored value per gate. -/
lemma evalValues_size (c : Circuit) (inputs : Nat → Bool) :
    (c.evalValues inputs).size = c.gates.length := by
  simpa [evalValues] using evalFold_size inputs c.gates #[]

/-- Evaluating an extended prefix first evaluates the old prefix and then
pushes the new gate's value computed from that preceding accumulator. -/
lemma evalPrefix_push (inputs : Nat → Bool) (pre : List CircuitGate)
    (gate : CircuitGate) :
    (pre ++ [gate]).foldl
      (fun values next => values.push (next.evalWith inputs values)) #[] =
      let values := pre.foldl
        (fun values next => values.push (next.evalWith inputs values)) #[]
      values.push (gate.evalWith inputs values) := by
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- At every gate position, evaluating through that gate computes its value
from exactly the accumulator obtained by evaluating the preceding gate prefix. -/
lemma evalPrefix_gate_value (c : Circuit) (inputs : Nat → Bool)
    (i : Nat) (hi : i < c.gates.length) :
    let values := (c.gates.take i).foldl
      (fun acc gate => acc.push (gate.evalWith inputs acc)) #[]
    ((c.gates.take (i + 1)).foldl
      (fun acc gate => acc.push (gate.evalWith inputs acc)) #[]).getD i false =
      (c.gates.get ⟨i, hi⟩).evalWith inputs values := by
  have htake : (c.gates.take i).length = i :=
    List.length_take_of_le (Nat.le_of_lt hi)
  have hsize :
      ((c.gates.take i).foldl
        (fun acc gate => acc.push (gate.evalWith inputs acc)) #[]).size = i := by
    simpa [htake] using evalFold_size inputs (c.gates.take i) #[]
  rw [← List.take_concat_get hi, List.concat_eq_append]
  rw [evalPrefix_push]
  simp only [Array.getD]
  split
  · simp [Array.getElem_push, hsize]
  · rename_i hout
    simp [Array.size_push, hsize] at hout

private lemma evalPrefix_getD_eq_evalValues (c : Circuit) (inputs : Nat → Bool)
    (prefixLength : Nat) (hprefix : prefixLength ≤ c.gates.length)
    (i : Nat) (hi : i < prefixLength) :
    ((c.gates.take prefixLength).foldl
      (fun values gate => values.push (gate.evalWith inputs values)) #[]).getD
        i false = (c.evalValues inputs).getD i false := by
  let prefixValues := (c.gates.take prefixLength).foldl
    (fun values gate => values.push (gate.evalWith inputs values)) #[]
  have hprefixLength : (c.gates.take prefixLength).length = prefixLength :=
    List.length_take_of_le hprefix
  have hprefixSize : prefixValues.size = prefixLength := by
    simpa [prefixValues, hprefixLength] using
      evalFold_size inputs (c.gates.take prefixLength) #[]
  have hpreserve := evalFold_getD_eq_initial inputs
    (c.gates.drop prefixLength) prefixValues i (by simpa [hprefixSize] using hi)
  have hsplit : c.evalValues inputs =
      (c.gates.drop prefixLength).foldl
        (fun values gate => values.push (gate.evalWith inputs values)) prefixValues := by
    change c.gates.foldl
      (fun values gate => values.push (gate.evalWith inputs values)) #[] = _
    conv_lhs =>
      rw [← List.take_append_drop prefixLength c.gates, List.foldl_append]
  rw [hsplit]
  exact hpreserve.symm

/-- Every entry of the complete evaluation array is the value obtained by
evaluating its gate against exactly the preceding folded gate prefix. -/
lemma evalValues_getElem_eq_evalPrefix (c : Circuit) (inputs : Nat → Bool)
    (i : Nat) (hi : i < c.gates.length) :
    (c.evalValues inputs)[i]'(by simpa [evalValues_size] using hi) =
      (c.gates.get ⟨i, hi⟩).evalWith inputs
        ((c.gates.take i).foldl
          (fun values gate => values.push (gate.evalWith inputs values)) #[]) := by
  have hfull : i < (c.evalValues inputs).size := by
    simpa [evalValues_size] using hi
  have hprefix : i + 1 ≤ c.gates.length := by omega
  have hpreserve := evalPrefix_getD_eq_evalValues c inputs (i + 1) hprefix i (by omega)
  calc
    (c.evalValues inputs)[i]'hfull = (c.evalValues inputs).getD i false := by
      simp [Array.getD, hfull]
    _ = ((c.gates.take (i + 1)).foldl
        (fun values gate => values.push (gate.evalWith inputs values)) #[]).getD i false :=
      hpreserve.symm
    _ = (c.gates.get ⟨i, hi⟩).evalWith inputs
        ((c.gates.take i).foldl
          (fun values gate => values.push (gate.evalWith inputs values)) #[]) :=
      evalPrefix_gate_value c inputs i hi

/-- In a well-formed circuit, every complete-array entry satisfies its gate's
semantic equation using proof-carrying lookups of actual predecessor entries.
Consequently, none of the evaluator's dependency defaults is used. -/
lemma evalValues_getElem_eq_gateEquation (c : Circuit) (inputs : Nat → Bool)
    (h : c.WellFormed) (i : Nat) (hi : i < c.gates.length) :
    (c.gates.get ⟨i, hi⟩).GateEquation inputs (c.evalValues inputs) i
      (by simpa [evalValues_size] using hi) := by
  let prefixValues := (c.gates.take i).foldl
    (fun values gate => values.push (gate.evalWith inputs values)) #[]
  have hentry := evalValues_getElem_eq_evalPrefix c inputs i hi
  have hprefix : i ≤ c.gates.length := Nat.le_of_lt hi
  have predecessor_eq (source : Nat) (hsource : source < i) :
      prefixValues.getD source false =
        (c.evalValues inputs)[source]'(by
          simpa [evalValues_size] using Nat.lt_trans hsource hi) := by
    have hpreserve := evalPrefix_getD_eq_evalValues c inputs i hprefix source hsource
    calc
      prefixValues.getD source false = (c.evalValues inputs).getD source false := by
        simpa [prefixValues] using hpreserve
      _ = (c.evalValues inputs)[source]'(by
          simpa [evalValues_size] using Nat.lt_trans hsource hi) := by
        simp [Array.getD, evalValues_size, Nat.lt_trans hsource hi]
  have hvalid := h.2 i hi
  generalize hgate : c.gates.get ⟨i, hi⟩ = gate at hentry hvalid ⊢
  cases gate with
  | input inputIndex =>
      simpa only [CircuitGate.GateEquation, CircuitGate.evalWith, prefixValues] using hentry
  | const value =>
      simpa only [CircuitGate.GateEquation, CircuitGate.evalWith, prefixValues] using hentry
  | not source =>
      refine ⟨hvalid, ?_⟩
      have hentry' :
          (c.evalValues inputs)[i]'(by simpa [evalValues_size] using hi) =
            !(prefixValues.getD source false) := by
        simpa only [CircuitGate.evalWith, prefixValues] using hentry
      rw [predecessor_eq source hvalid] at hentry'
      exact hentry'
  | and left right =>
      refine ⟨hvalid.1, hvalid.2, ?_⟩
      have hentry' :
          (c.evalValues inputs)[i]'(by simpa [evalValues_size] using hi) =
            (prefixValues.getD left false && prefixValues.getD right false) := by
        simpa only [CircuitGate.evalWith, prefixValues] using hentry
      rw [predecessor_eq left hvalid.1, predecessor_eq right hvalid.2] at hentry'
      exact hentry'
  | or left right =>
      refine ⟨hvalid.1, hvalid.2, ?_⟩
      have hentry' :
          (c.evalValues inputs)[i]'(by simpa [evalValues_size] using hi) =
            (prefixValues.getD left false || prefixValues.getD right false) := by
        simpa only [CircuitGate.evalWith, prefixValues] using hentry
      rw [predecessor_eq left hvalid.1, predecessor_eq right hvalid.2] at hentry'
      exact hentry'

/-- A well-formed circuit's output evaluation is an in-bounds array lookup. -/
lemma eval_eq_getElem (c : Circuit) (inputs : Nat → Bool)
    (h : c.WellFormed) :
    c.eval inputs =
      (c.evalValues inputs)[c.output]'(by
        simpa [Circuit.evalValues_size] using h.1) := by
  simp [eval, Array.getD, h.1, evalValues_size]

end Circuit

/-- A well-formed general circuit is satisfiable when some assignment of its
declared input bits makes the designated output gate true. -/
def GeneralCircuitSatisfiable (c : Circuit) : Prop :=
  c.WellFormed ∧
    ∃ assignment : Fin c.inputCount → Bool,
      c.eval (fun i => if hi : i < c.inputCount then assignment ⟨i, hi⟩ else false) = true

end Chapter34

end CLRS
