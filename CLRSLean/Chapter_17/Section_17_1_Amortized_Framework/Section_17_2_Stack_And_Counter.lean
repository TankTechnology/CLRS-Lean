import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 17.2 - Stack and counter examples

This section records two compact textbook amortized-analysis examples.  The
stack model uses the real operation cost for {lit}`MULTIPOP`: at most one unit
per popped element.  The counter model includes the executable little-endian
increment, the exact one-step flip count, and the standard one-bit-count
potential proof.

Main results:

- Theorem {lit}`multiPop_totalCost_le`: one {lit}`MULTIPOP` operation pops at
  most the requested number of stack cells.
- Theorem {lit}`binaryCounter_increment_potential_le_two`: one executable
  binary-counter increment has amortized cost at most 2 under the number-of-one
  bits potential.
- Theorem {lit}`binaryCounter_trace_potential_le`: the executable multi-step
  increment trace has total flips plus final potential bounded by the initial
  potential plus {lit}`2n`.
- Theorem {lit}`binaryCounter_trace_totalFlips_le`: starting from the empty
  counter, the executable trace flips at most {lit}`2n` bits.
- Theorem {lit}`binaryCounter_totalFlips_le`: the first-pass counter cost model
  has total flip count at most {lit}`2n`.

Status: `proved` for the stack and binary-counter amortized examples.
-/

namespace CLRS
namespace Chapter17

/-! ## Stack multipop -/

/-- Pop at most {lit}`k` elements from a stack represented by a list. -/
def multiPop {α : Type u} (s : List α) (k : Nat) : List α :=
  s.drop k

/-- Cost of a single {lit}`MULTIPOP`: the number of cells actually removed. -/
def multiPopCost {α : Type u} (s : List α) (k : Nat) : Nat :=
  min k s.length

/-- A single {lit}`MULTIPOP` pops at most the requested number of cells. -/
theorem multiPop_totalCost_le {α : Type u} (s : List α) (k : Nat) :
    multiPopCost s k <= k := by
  exact Nat.min_le_left k s.length

/-! ## Binary counter -/

/--
Executable little-endian binary-counter increment.  This definition is included
for the public model; the first-pass cost theorem below uses a specification
cost sequence with the standard constant amortized bound.
-/
def binaryCounterIncrement : List Bool -> List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: binaryCounterIncrement bits

/-- Number of one bits in the little-endian counter state. -/
def trueBitCount : List Bool -> Nat
  | [] => 0
  | false :: bits => trueBitCount bits
  | true :: bits => trueBitCount bits + 1

/-- Exact number of bit flips performed by one executable increment. -/
def bitFlipsOfIncrement : List Bool -> Nat
  | [] => 1
  | false :: _bits => 1
  | true :: bits => bitFlipsOfIncrement bits + 1

/--
The executable increment has amortized cost at most two when the potential is
the number of one bits.
-/
theorem binaryCounter_increment_potential_le_two (bits : List Bool) :
    bitFlipsOfIncrement bits + trueBitCount (binaryCounterIncrement bits) <=
      trueBitCount bits + 2 := by
  induction bits with
  | nil =>
      simp [bitFlipsOfIncrement, trueBitCount, binaryCounterIncrement]
  | cons bit bits ih =>
      cases bit
      · simp [bitFlipsOfIncrement, trueBitCount, binaryCounterIncrement]
        omega
      · simp [bitFlipsOfIncrement, trueBitCount, binaryCounterIncrement]
        omega

/-- Counter state after {lit}`n` executable increments from an initial state. -/
def binaryCounterAfter : Nat -> List Bool -> List Bool
  | 0, bits => bits
  | n + 1, bits => binaryCounterAfter n (binaryCounterIncrement bits)

/-- Total executable bit flips along {lit}`n` counter increments. -/
def binaryCounterTraceFlips : Nat -> List Bool -> Nat
  | 0, _bits => 0
  | n + 1, bits =>
      bitFlipsOfIncrement bits + binaryCounterTraceFlips n (binaryCounterIncrement bits)

/--
The executable counter trace inherits the one-step potential bound: total flips
plus final one-bit potential is at most initial potential plus {lit}`2n`.
-/
theorem binaryCounter_trace_potential_le (n : Nat) (bits : List Bool) :
    binaryCounterTraceFlips n bits + trueBitCount (binaryCounterAfter n bits) <=
      trueBitCount bits + 2 * n := by
  induction n generalizing bits with
  | zero =>
      simp [binaryCounterTraceFlips, binaryCounterAfter]
  | succ n ih =>
      simp [binaryCounterTraceFlips, binaryCounterAfter]
      have htail := ih (binaryCounterIncrement bits)
      have hstep := binaryCounter_increment_potential_le_two bits
      omega

/-- Starting from the empty counter, {lit}`n` executable increments flip at most {lit}`2n` bits. -/
theorem binaryCounter_trace_totalFlips_le (n : Nat) :
    binaryCounterTraceFlips n [] <= 2 * n := by
  have htrace := binaryCounter_trace_potential_le n []
  have hle :
      binaryCounterTraceFlips n [] <=
        binaryCounterTraceFlips n [] + trueBitCount (binaryCounterAfter n []) := by
    exact Nat.le_add_right _ _
  exact Nat.le_trans hle (by simpa [trueBitCount] using htrace)

/-- First-pass amortized flip count for one counter increment. -/
def bitFlipsForIncrement (_i : Nat) : Nat :=
  2

/-- Under the first-pass cost model, {lit}`n` increments flip at most {lit}`2n` bits. -/
theorem binaryCounter_totalFlips_le (n : Nat) :
    prefixCost bitFlipsForIncrement n <= 2 * n := by
  induction n with
  | zero =>
      simp [prefixCost]
  | succ n ih =>
      simp [prefixCost, bitFlipsForIncrement]
      omega

end Chapter17
end CLRS
