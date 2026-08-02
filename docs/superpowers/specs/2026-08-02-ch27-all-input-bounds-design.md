# Chapter 27 All-Input Cost Bounds Design

## Goal

Close issue #121 at its complete boundary: extend the existing exact
power-of-two cost theorems for P-MERGE, P-MERGE-SORT, and parallel Strassen to
arbitrary natural input sizes.  The result must prove monotonicity of all six
work/span functions, expose the adjacent-power sandwich used by CLRS, and
derive all-input `Theta` theorems in textbook-facing comparison scales.

This work changes only the recurrence-analysis layer.  Executable P-MERGE and
P-MERGE-SORT implementations remain the separate #122 refinement target.

## Existing foundation

`Section_27_2_4_Algorithms.lean` already defines executable natural-valued
recurrences and exact closed forms on inputs `2 ^ k`:

- `pMergeWork` and `pMergeSpan`;
- `pMergeSortWork` and `pMergeSortSpan`; and
- `strassenWork` and `strassenSpan`.

Chapter 4 already provides the reusable all-input bridge in
`Section_04_6_Master_Theorem_All_Input.lean`: `powerInterval_of_pos`,
`MonotoneAbs`, `allInput_bigTheta_of_powerStep`, and comparison theorems for
critical-power, polynomial, polynomial-logarithmic, polylogarithmic, and
real-log scales.  Chapter 27 will import and instantiate that layer rather than
duplicate it or move chapter-specific recurrences into `ProofPatterns`.

## Monotonicity layer

For every cost function, first prove a one-step inequality by strong induction:

```lean
private theorem pMergeWork_le_succ (n : Nat) :
    pMergeWork n <= pMergeWork (n + 1)
```

The proof unfolds both sides above the base cases.  The parity split for
`(n + 1) / 2` determines whether the floor half increases and the ceiling half
stays fixed, or vice versa.  `Nat.log_mono_right` handles the binary-search
term.  The same structure applies to P-MERGE-SORT work.  Span proofs only
follow the ceiling half; `pMergeSortSpan_le_succ` additionally uses the already
proved monotonicity of `pMergeSpan`.  Strassen work/span use the simpler floor
half split.

The public layer contains exactly these six natural monotonicity theorems:

```lean
theorem pMergeWork_monotone : Monotone pMergeWork
theorem pMergeSpan_monotone : Monotone pMergeSpan
theorem pMergeSortWork_monotone : Monotone pMergeSortWork
theorem pMergeSortSpan_monotone : Monotone pMergeSortSpan
theorem strassenWork_monotone : Monotone strassenWork
theorem strassenSpan_monotone : Monotone strassenSpan
```

A private generic cast lemma turns `Monotone T` for `T : Nat -> Nat` into
Chapter 4's `MonotoneAbs (fun n => (T n : Real))`.  This avoids six public
real-cast wrapper definitions.

## Adjacent-power sandwich interface

Each cost function exposes a public theorem named `*_power_sandwich`.  Its
statement has the same shape as Chapter 4's maximum-subarray theorem:

```lean
theorem pMergeWork_power_sandwich (n : Nat) (hn : 0 < n) :
    pMergeWork (2 ^ Nat.log 2 n) <= pMergeWork n /\
    pMergeWork n <= pMergeWork (2 ^ (Nat.log 2 n + 1))
```

The other five theorems substitute their corresponding cost function.  All six
are direct applications of `powerInterval_of_pos 2 n` and the public
monotonicity theorem.  Keeping this layer public makes the floor/ceiling
transfer independently reusable without forcing downstream code through real
asymptotic notation.

## All-input asymptotic interface

The exact power-of-two equations are converted privately into exact-power
`Chapter03.isBigTheta` witnesses.  Chapter 4's adjacent-power transfer then
produces these six public theorems:

```lean
theorem pMergeWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeWork n : Real))
      (Chapter04.polynomialScale 1)

theorem pMergeSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeSpan n : Real))
      (Chapter04.criticalPowerLogPolylogScale 1 2 1)

theorem pMergeSortWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeSortWork n : Real))
      (Chapter04.polynomialLogScale 2 1)

theorem pMergeSortSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeSortSpan n : Real))
      (Chapter04.criticalPowerLogPolylogScale 1 2 2)

theorem strassenWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (strassenWork n : Real))
      (Chapter04.realLogScale 7 2)

theorem strassenSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (strassenSpan n : Real))
      (Chapter04.polynomialLogScale 2 0)
```

These comparison functions mean, respectively, `Theta(n)`, `Theta(log^2 n)`,
`Theta(n log n)`, `Theta(log^3 n)`, `Theta(n^(log_2 7))`, and `Theta(log n)`.
The `+ 1` in the discrete logarithmic scales keeps the functions positive at
small inputs and does not alter their asymptotic class.

## Proof order and file ownership

All new Lean declarations stay in
`CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`, next to the recurrence
they describe.  The order is:

1. P-MERGE work and span monotonicity, sandwich, and all-input bounds;
2. P-MERGE-SORT work and span, reusing P-MERGE span monotonicity;
3. parallel Strassen work and span;
4. public-interface and documentation synchronization.

No new section module or shared proof-pattern module is needed.

## Test-first proof surface

Before adding production declarations, extend `Tests/Chapter_27_Interface.lean`
with `#check` entries for the six `*_monotone`, six `*_power_sandwich`, and six
`*_allInput_bigTheta` names.  Run the focused interface command and confirm it
fails because the first requested declaration is missing.  Implement one
theorem family at a time and rerun the source and interface after each green
step.

The interface will also instantiate representative monotonicity and sandwich
facts on an odd input, ensuring the public statements exercise the actual
floor/ceiling recurrences rather than only declaration names.

## Status and documentation

After the Lean surface compiles:

- update the section module's main-results and deferred-work prose;
- update `CLRSLean/Chapter_27.lean`, `CLRSLean/Status.lean`, and
  `docs/proof-map.md` with the six all-input bounds;
- update Chapter 27's progress CSV theorem count and regenerate
  `CLRSLean/Progress.lean`;
- update `docs/proof-status-board.md` so #122 is the only remaining core
  Chapter 27 proof group; and
- regenerate/check the README progress table.

Chapter 27 remains `partial` because executable P-MERGE/P-MERGE-SORT
correctness is still open.  The documentation must not imply that #121 closes
the entire chapter.

## Rejected alternatives

Direct all-input inductions with separately chosen constants would duplicate
the same floor/ceiling and adjacent-power reasoning six times and would hide
the exact CLRS sandwich argument.  A new generic recurrence-monotonicity
framework would broaden #121 and introduce an abstraction currently used only
by this chapter.  Reusing Chapter 4 gives the strongest result with the
smallest stable interface.

## Verification boundary

Development uses focused checks:

```text
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms
lake env lean Tests/Chapter_27_Interface.lean
```

Completion additionally requires the Chapter 27 forbidden-proof scan,
`#print axioms` on the six headline theorems, progress/dashboard consistency,
repository static checks, `git diff --check`, and `lake build CLRSLean.Chapter_27`.
Per the project workflow agreed for proof changes, this task does not run the
full Verso HTML build.
