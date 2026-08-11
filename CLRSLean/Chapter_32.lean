import CLRSLean.Chapter_32.Section_32_1_String_Model
import CLRSLean.Chapter_32.Section_32_1_String_Model.Naive_Matcher
import CLRSLean.Chapter_32.Section_32_2_Rabin_Karp

/-! # Chapter 32 — String Matching

Chapter 32 of CLRS covers string-matching algorithms: finding all occurrences
of a pattern `P` in a text `T`.

This chapter formalizes Sections 32.1 and 32.2 with fully proved correctness
theorems.  Sections 32.3–32.4 (finite automata, Knuth-Morris-Pratt) are
deferred.

## Sections

### 32.1 The Naive String-Matching Algorithm

* `CLRS.Chapter32.Text` (`Section_32_1_String_Model`): strings as `List α` with
  prefix, suffix, `isPrefix`, and `isSuffix` predicates — 14 lemmas, all proved.
* `CLRS.Chapter32.matchesAt`, `CLRS.Chapter32.naiveMatcher`
  (`Section_32_1_String_Model/Naive_Matcher`): pattern-occurrence predicate and
  slide-and-check matcher — soundness and completeness (5 theorems, all proved).

### 32.2 The Rabin-Karp Algorithm

* `CLRS.Chapter32.hash`, `CLRS.Chapter32.rabinKarpMatcher`
  (`Section_32_2_Rabin_Karp`): base-`d` modular hash by Horner's rule and the
  hash-then-compare matcher — soundness, completeness, and agreement with
  `naiveMatcher` (`rabinKarp_correct`), plus the O(1) incremental update
  `hash_snoc`.

**Status: `selected-section-complete`** — Sections 32.1–32.2 are fully proved
(25 theorems, 0 sorries).

## Deferred Work

* 32.3 Finite automata (suffix-function DFA construction)
* 32.4 Knuth-Morris-Pratt (prefix-function linear-time algorithm)
* 32.5 Suffix arrays
-/

namespace CLRS
namespace Chapter32
end Chapter32
end CLRS
