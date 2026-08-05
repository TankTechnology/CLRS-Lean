# Chapter 30 Bit-Reversal Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement and verify the Section 30.3 bit-reversal index permutation and its execution-attached linear copy cost.

**Architecture:** A recursive `Fin (2 ^ k)` equivalence removes the least-significant input bit, reverses the remaining quotient, and places the removed bit as the output half selector.  The value-producing copy follows the existing even/odd coefficient split, returns a `BitReverseExecution`, and proves both permutation semantics and exactly one move per source element.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Equiv`/`Fin`/`Nat.testBit`, the Chapter 30 `PowTwoVec` and even/odd/half interfaces, Lake, interface tests.

---

## Prerequisite

Milestone 1 at commit `e133780` and the approved Milestone 2 design at commit
`bf2978d` are green.  Do not alter the proved Section 30.2 interfaces.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean` for the index equivalence, bit semantics, execution, and move theorem.
- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean` as the Section 30.3 aggregator and reader guide.
- Create `Tests/Chapter_30_BitReversal_Interface.lean` for the public contract and exact examples.
- Modify `CLRSLean/Chapter_30.lean` to export the Section 30.3 aggregator.

### Task 1: Lock The Bit-Reversal Contract In RED

**Files:**
- Create: `Tests/Chapter_30_BitReversal_Interface.lean`

- [ ] **Step 1: Write the public interface test**

Create:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check bitReverseEquiv
#check bitReverseEquiv_even
#check bitReverseEquiv_odd
#check bitReverseEquiv_testBit
#check bitReverseEquiv_involutive
#check BitReverseExecution
#check bitReverseExec
#check bitReverseCopy
#check bitReverseCopy_apply
#check bitReverseCopy_involutive
#check bitReverseExec_moves

example : (bitReverseEquiv 3 ⟨1, by norm_num⟩).1 = 4 := by native_decide
example : (bitReverseEquiv 3 ⟨3, by norm_num⟩).1 = 6 := by native_decide

end CLRS.Chapter30
```

- [ ] **Step 2: Run the test and verify RED**

Run:

```bash
lake env lean Tests/Chapter_30_BitReversal_Interface.lean
```

Expected: nonzero exit on `Unknown constant CLRS.Chapter30.bitReverseEquiv`.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_30_BitReversal_Interface.lean
git commit -m "test(ch30): specify bit-reversal interface"
```

### Task 2: Define The Recursive Index Equivalence

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean`
- Test: `Tests/Chapter_30_BitReversal_Interface.lean`

- [ ] **Step 1: Add finite-product power-of-two equivalences**

Import `RecursiveFFT.Definitions`, `Mathlib.Logic.Equiv.Fin.Basic`, and
`Mathlib.Tactic`.  Define private cast equivalences for both factorizations:

```lean
private def powTwoSuccMulRightEquiv (k : Nat) :
    Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k * 2) :=
  finCongr (by simp [pow_succ, Nat.mul_comm])

private def powTwoSuccMulLeftEquiv (k : Nat) :
    Fin (2 * 2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
  finCongr (by simp [pow_succ])
```

The first decomposition feeds `finProdFinEquiv (m := 2 ^ k) (n := 2)` so the
second component is the least-significant bit.  The second construction feeds
`finProdFinEquiv (m := 2) (n := 2 ^ k)` so that bit selects the output half.

- [ ] **Step 2: Define `bitReverseEquiv` structurally**

Use recursion on the exponent:

```lean
def bitReverseEquiv : (k : Nat) → Fin (2 ^ k) ≃ Fin (2 ^ k)
  | 0 => Equiv.refl _
  | k + 1 =>
      powTwoSuccMulRightEquiv k |>.trans
        ((finProdFinEquiv (m := 2 ^ k) (n := 2)).symm.trans
          ((bitReverseEquiv k).prodCongr (Equiv.refl (Fin 2)) |>.trans
            ((Equiv.prodComm (Fin (2 ^ k)) (Fin 2)).trans
              ((finProdFinEquiv (m := 2) (n := 2 ^ k)).trans
                (powTwoSuccMulLeftEquiv k)))))
```

If elaboration requires the equivalent sequence written with local `let`
bindings, preserve this exact composition and its quotient/bit ordering.

- [ ] **Step 3: Prove the structural even/odd laws**

Prove simp-facing theorems:

```lean
@[simp] theorem bitReverseEquiv_even {k : Nat} (i : Fin (2 ^ k)) :
    bitReverseEquiv (k + 1) (evenIndex i) =
      lowerHalfIndex (bitReverseEquiv k i) := by
  apply Fin.ext
  simp [bitReverseEquiv, powTwoSuccMulRightEquiv,
    powTwoSuccMulLeftEquiv, evenIndex, lowerHalfIndex, powTwoSuccEquiv]

@[simp] theorem bitReverseEquiv_odd {k : Nat} (i : Fin (2 ^ k)) :
    bitReverseEquiv (k + 1) (oddIndex i) =
      upperHalfIndex (bitReverseEquiv k i) := by
  apply Fin.ext
  simp [bitReverseEquiv, powTwoSuccMulRightEquiv,
    powTwoSuccMulLeftEquiv, oddIndex, upperHalfIndex, powTwoSuccEquiv]
```

Normalize `Nat.mod_two`/`Nat.div_two` only inside these proofs; downstream files
rewrite through these two laws.

- [ ] **Step 4: Compile the index foundation**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
```

Expected: exit 0.

### Task 3: Prove Bit Semantics And Involution

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean`
- Test: `Tests/Chapter_30_BitReversal_Interface.lean`

- [ ] **Step 1: Prove the fixed-width mirrored-bit theorem**

State the public theorem with a bounded bit position:

```lean
theorem bitReverseEquiv_testBit {k : Nat} (i : Fin (2 ^ k))
    (j : Nat) (hj : j < k) :
    Nat.testBit (bitReverseEquiv k i).1 j =
      Nat.testBit i.1 (k - 1 - j) := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
      -- Split the input using parity into `evenIndex` or `oddIndex`.
      -- Split `j = k` (the new most-significant result bit) from `j < k`.
      -- Use `bitReverseEquiv_even`/`odd`, then `ih` for the lower positions.
```

Use the installed `Nat.testBit_zero`, `Nat.testBit_succ`,
`Nat.testBit_add_one`, `Nat.testBit_lt_two_pow`,
`Nat.testBit_two_pow_add_eq`, and `Nat.testBit_two_pow_add_gt` lemmas.  In the
successor proof, positions below the new high bit are unchanged by adding the
half-size power of two; at the new high bit, the structural even/odd case is
respectively false/true and matches input bit zero.

- [ ] **Step 2: Prove involution by structural index decomposition**

Do not derive involution from extensional bit equality unless that is shorter.
Induct on `k`, split an arbitrary index into even or odd form by quotient and
remainder modulo two, rewrite twice with the structural laws, and apply the
induction hypothesis:

```lean
theorem bitReverseEquiv_involutive (k : Nat) :
    Function.Involutive (bitReverseEquiv k) := by
  intro i
  induction k with
  | zero => exact Fin.ext (by simp [bitReverseEquiv])
  | succ k ih =>
      -- parity decomposition; the even and odd cases close with `ih`.
```

- [ ] **Step 3: Run the focused source build**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
```

Expected: exit 0 with no `sorry` or project axiom.

### Task 4: Implement The Copy Execution And Exact Moves

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean`
- Test: `Tests/Chapter_30_BitReversal_Interface.lean`

- [ ] **Step 1: Define the execution and value projection**

Add:

```lean
structure BitReverseExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  moves : Nat

def bitReverseExec {K : Type*} :
    {k : Nat} → PowTwoVec K k → BitReverseExecution K k
  | 0, a => ⟨a, 1⟩
  | k + 1, a =>
      let evenRun := bitReverseExec (evenCoeffs a)
      let oddRun := bitReverseExec (oddCoeffs a)
      ⟨joinHalves evenRun.value oddRun.value,
        evenRun.moves + oddRun.moves⟩

def bitReverseCopy {K : Type*} {k : Nat} (a : PowTwoVec K k) :
    PowTwoVec K k :=
  (bitReverseExec a).value
```

- [ ] **Step 2: Prove recursive and index semantics**

First expose the successor equation by reflexivity/simp.  Then prove by
induction and `Fin` parity decomposition:

```lean
theorem bitReverseCopy_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K k) (i : Fin (2 ^ k)) :
    bitReverseCopy a (bitReverseEquiv k i) = a i := by
  induction k generalizing a i with
  | zero =>
      have hi : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
      subst i
      rfl
  | succ k ih =>
      -- even/odd input cases; use join-half and structural reversal laws.
```

- [ ] **Step 3: Prove vector involution**

Use `funext`, `bitReverseCopy_apply`, and `bitReverseEquiv_involutive`:

```lean
theorem bitReverseCopy_involutive {K : Type*} {k : Nat} :
    Function.Involutive (@bitReverseCopy K k) := by
  intro a
  funext i
  rw [← bitReverseEquiv_involutive k i]
  simp only [bitReverseCopy_apply]
```

- [ ] **Step 4: Prove the exact move field**

```lean
@[simp] theorem bitReverseExec_moves {K : Type*} {k : Nat}
    (a : PowTwoVec K k) :
    (bitReverseExec a).moves = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [bitReverseExec, ih, pow_succ]
```

- [ ] **Step 5: Verify the source and commit**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean
git commit -m "feat(ch30): formalize bit-reversal execution"
```

Expected: build exit 0 and one focused source commit.

### Task 5: Export The First Section 30.3 Surface

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean`
- Modify: `CLRSLean/Chapter_30.lean`
- Test: `Tests/Chapter_30_BitReversal_Interface.lean`

- [ ] **Step 1: Create the section aggregator**

Create an aggregator importing `BitReversal` and documenting that bit reversal
is proved while iterative stages, costs, and the parallel network are the next
modules in the same approved milestone.  Link the generated source path using
the repository's existing Chapter 30 guide style.

- [ ] **Step 2: Export Section 30.3 from Chapter 30**

Add:

```lean
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations
```

after the Section 30.2 import in `CLRSLean/Chapter_30.lean`.  Keep the chapter
status `partial` until the closure plan passes.

- [ ] **Step 3: Turn the RED interface GREEN**

Run:

```bash
lake env lean Tests/Chapter_30_BitReversal_Interface.lean
rg -n "sorry|admit" \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean
```

Expected: interface exit 0 and the scan has no matches.

- [ ] **Step 4: Commit the exported boundary**

```bash
git add CLRSLean/Chapter_30.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  Tests/Chapter_30_BitReversal_Interface.lean
git commit -m "feat(ch30): expose bit-reversal interface"
```
