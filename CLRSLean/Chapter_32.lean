import CLRSLean.Chapter_32.Section_32_1_String_Model
import CLRSLean.Chapter_32.Section_32_3_Finite_Automata
import CLRSLean.Chapter_32.Section_32_4_KMP

/-! # Chapter 32 — String Matching

Chapter 32 of CLRS covers string-matching algorithms: finding all occurrences
of a pattern `P` in a text `T`.  The chapter develops the finite-automaton
approach and the Knuth-Morris-Pratt (KMP) algorithm, both of which run in
`O(n)` time after preprocessing.

This formalization currently covers:

* **32.1 The naive string-matching algorithm** — string model, prefix/suffix
  operations, and the basic definitions needed for string matching.

* **32.3 String matching with finite automata** — the suffix function `σ`,
  the DFA construction via `δ(q,a)=σ(P_q ++ [a])`, and the proof that the
  automaton accepts exactly those texts ending with the pattern `P`.

* **32.4 The Knuth-Morris-Pratt algorithm** — the prefix function `π`,
  the `O(m)` COMPUTE-PREFIX-FUNCTION procedure, the KMP-MATCHER, and
  correctness theorems (32.5, 32.6).

## Sections

* **32.1 String model.**
  Main definitions:
  {lit}`CLRS.Chapter32.Text`,
  {lit}`CLRS.Chapter32.prefix`,
  {lit}`CLRS.Chapter32.suffix`,
  {lit}`CLRS.Chapter32.isPrefix`,
  {lit}`CLRS.Chapter32.isSuffix`,
  {lit}`CLRS.Chapter32.isProperPrefix`,
  {lit}`CLRS.Chapter32.isProperSuffix`.

* **32.3 Finite automata.**
  Main definitions:
  {lit}`CLRS.Chapter32.suffixFn`,
  {lit}`CLRS.Chapter32.delta`,
  {lit}`CLRS.Chapter32.deltaStar`,
  {lit}`CLRS.Chapter32.accepts`,
  {lit}`CLRS.Chapter32.states`,
  {lit}`CLRS.Chapter32.initialState`,
  {lit}`CLRS.Chapter32.isAcceptingState`.
  Main theorems:
  {lit}`CLRS.Chapter32.suffixFn_correct`,
  {lit}`CLRS.Chapter32.suffixFn_cons_le_succ` (Lemma 32.3),
  {lit}`CLRS.Chapter32.suffixFn_append_eq` (Lemma 32.4),
  {lit}`CLRS.Chapter32.deltaStar_eq_suffixFn`,
  {lit}`CLRS.Chapter32.accepts_iff_isSuffix`.

* **32.4 KMP algorithm.**
  Main definitions:
  {lit}`CLRS.Chapter32.prefixFunction`,
  {lit}`CLRS.Chapter32.kmpMatcher`,
  {lit}`CLRS.Chapter32.kmpSearch`.
  Main theorems:
  {lit}`CLRS.Chapter32.prefixFunction_spec` (Theorem 32.5),
  {lit}`CLRS.Chapter32.kmpMatcher_correct` (Theorem 32.6).

## Future work

* 32.2 The Rabin-Karp algorithm (rolling hash).
* Full occurrence-finding proofs (rather than just stating correctness).

## References

The DFA construction follows CLRS §32.3 closely.  The suffix function `σ(x)`
returns the length of the longest prefix of `P` that is a suffix of `x`.  The
transition `δ(q,a)=σ(P_q ++ [a])` defines the automaton, and Lemma 32.4
(`σ(xa)=σ(P_{σ(x)}a)`) is the key to the correctness proof.
-/

namespace CLRS
namespace Chapter32

end Chapter32
end CLRS
