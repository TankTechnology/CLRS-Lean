import CLRSLean.Chapter_32.Section_32_1_String_Model
import CLRSLean.Chapter_32.Section_32_1_String_Model.Naive_Matcher
import CLRSLean.Chapter_32.Section_32_2_Rabin_Karp
import CLRSLean.Chapter_32.Section_32_3_Finite_Automata
import CLRSLean.Chapter_32.Section_32_4_KMP

/-! # Chapter 32 — String Matching

Chapter 32 of CLRS covers string-matching algorithms: finding all occurrences
of a pattern `P` in a text `T`.

This chapter formalizes Sections 32.1–32.4.  Section 32.1 has fully proved
correctness theorems; Sections 32.2–32.4 (Rabin-Karp, finite automata,
Knuth-Morris-Pratt) are represented with the core correctness theorems still
in progress.

## Sections

### 32.1 The Naive String-Matching Algorithm

* `CLRS.Chapter32.Text` (`Section_32_1_String_Model`): strings as `List α` with
  prefix, suffix, `isPrefix`, and `isSuffix` predicates — 14 lemmas, all proved.
* `CLRS.Chapter32.matchesAt`, `CLRS.Chapter32.naiveMatcher`
  (`Section_32_1_String_Model/Naive_Matcher`): pattern-occurrence predicate and
  slide-and-check matcher — soundness and completeness (5 theorems, all proved).

**Status: proved** — 19 theorems, 0 sorries.

### 32.2 The Rabin-Karp Algorithm

* `CLRS.Chapter32.hash`, `CLRS.Chapter32.rollingHash`
  (`Section_32_2_Rabin_Karp`): rolling-hash fingerprint and update, with
  hash-correctness and equality theorems.

**Status: partial** — core hash algebra proved; remaining gaps recorded in the
section file.

### 32.3 String Matching with Finite Automata

* `Section_32_3_Finite_Automata`: finite-automaton string matching model.

**Status: partial** — represented; remaining gaps recorded in the section file.

### 32.4 The Knuth-Morris-Pratt Algorithm

* `CLRS.Chapter32.prefixFunction`, `CLRS.Chapter32.kmpMatcher`
  (`Section_32_4_KMP`): prefix-function computation and linear-time matcher.

**Status: proved** — `prefixFunction_spec` (Theorem 32.5) and
`kmpMatcher_correct` (Theorem 32.6) are kernel-checked, 0 sorries.

## Deferred Work

* Remaining correctness theorems in Sections 32.2–32.4 (see section files)
-/

namespace CLRS
namespace Chapter32
end Chapter32
end CLRS
