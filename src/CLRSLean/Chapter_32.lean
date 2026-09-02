import CLRSLean.Chapter_32.Section_32_1_String_Model
import CLRSLean.Chapter_32.Section_32_1_String_Model.Naive_Matcher

/-! # Chapter 32 — String Matching

Chapter 32 of CLRS covers string-matching algorithms: finding all occurrences
of a pattern `P` in a text `T`.

This chapter currently formalizes Section 32.1 with fully proved correctness
theorems.  Sections 32.2–32.4 (Rabin-Karp, finite automata, Knuth-Morris-Pratt)
are deferred.

## Sections

### 32.1 The Naive String-Matching Algorithm

* `CLRS.Chapter32.Text` (`Section_32_1_String_Model`): strings as `List α` with
  prefix, suffix, `isPrefix`, and `isSuffix` predicates — 14 lemmas, all proved.
* `CLRS.Chapter32.matchesAt`, `CLRS.Chapter32.naiveMatcher`
  (`Section_32_1_String_Model/Naive_Matcher`): pattern-occurrence predicate and
  slide-and-check matcher — soundness and completeness (5 theorems, all proved).

**Status: `selected-section-complete`** — Section 32.1 is fully proved (19 theorems, 0 sorries).

## Deferred Work

* 32.2 Rabin-Karp (hash-based rolling matcher)
* 32.3 Finite automata (suffix-function DFA construction)
* 32.4 Knuth-Morris-Pratt (prefix-function linear-time algorithm)
-/

namespace CLRS
namespace Chapter32
end Chapter32
end CLRS
