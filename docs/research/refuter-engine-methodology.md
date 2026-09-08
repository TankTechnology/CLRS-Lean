# Refuter Engine Methodology

**Status:** methodology record dated 2026-08-18. The general engine has not been
implemented; only the pattern and one-off instances exist.

## Origin: the Miller–Rabin error bound in Chapter 31

The approach emerged while repairing the Miller–Rabin probability argument:

1. Express the conjecture as a decidable predicate over a finite structure: the
   strong liars form a subgroup of the units modulo `n`.
2. Exhaustively evaluate small domains at compile time. This found counterexamples
   at `n = 65, 85, 145, 185`.
3. Treat the counterexample as a result: failure of subgroup closure rejects the
   naive subgroup proof strategy and explains why the theorem is subtle.
4. Search a second claim. The `φ(n)/4` bound fails at `n = 9`, where the liar set
   is `{1, 8}` and `2 > 6/4`.
5. Characterize the cause: the bound fails when the good subgroup has index 3,
   which in the searched setting occurs at `n = 3²`.
6. State the strongest uniform correction: `liars ≤ (n-1)/4`, equivalently at
   least `3(n-1)/4` witnesses. This is stronger than the `(n-1)/2` witness bound
   in CLRS Theorem 31.39.

## Five-step method

1. **Formulate:** encode the conjecture as a decidable statement over a finite,
   enumerable domain with small witnesses.
2. **Search:** use `#eval` or compiled native code over a bounded parameter range.
3. **Verify:** turn every hit into a kernel-checked counterexample proof.
4. **Bound:** when no hit exists, record the verified search limit and structural
   observations without claiming an unbounded theorem.
5. **Classify:** identify the exact failure condition and derive a corrected,
   maximally strong statement.

## Suitable open problems

- finite first-order conjectures in combinatorial number theory, string
  combinatorics, or small graph theory;
- problems whose counterexamples are expected to be small enough to enumerate;
- predicates that compile without interactive proof search.

Candidate targets include string attractors, searches related to Lehmer's
totient problem, BPSW pseudoprimes, and computed validation of candidate semantic
differences proposed during audits.

## Relationship to semantic audits

The current semantic-fidelity adversary proposes differences through language-
model review. The target architecture is:

`candidate generation → computed refutation or confirmation → verified report`

Only computationally validated candidates would enter the final report. This
raises adversarial-review quality while reducing time spent on unsupported leads.
