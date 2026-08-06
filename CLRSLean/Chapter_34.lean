import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-! # Chapter 34 — NP-Completeness

Chapter 34 of CLRS covers NP-completeness: the complexity classes **P** and
**NP**, polynomial-time reducibility, and NP-completeness.

This chapter currently formalizes Section 34.1: the **framework** — languages,
polynomial-time computability, polynomial-time decision, and the class **P** —
built on Mathlib's `Turing.TM2ComputableInPolyTime` (machine-level
polynomial-time computability with `Polynomial ℕ` time bounds).

## Sections

### 34.1 Polynomial Time

* `CLRS.Chapter34.Language` — a set of strings over an alphabet
* `CLRS.Chapter34.PolyTimeComputable` — a function computed by a TM2 machine
  in time bounded by a polynomial in the input length
* `CLRS.Chapter34.PolyTimeDecidable` — a language decided by a
  polynomial-time decision function
* `CLRS.Chapter34.ClassP` — the class of polynomial-time decidable languages

**Status: `partial`** — the framework definitions are in place.  The following
are documented follow-ups (deliberately deferred, per the session plan):

- Concrete machine constructions: the empty/universal languages are in `P`
  (a TM2 machine must clear its input stack before halting).
- `Turing.TM2ComputableInPolyTime.comp`: composition of polynomial-time
  machines is polynomial-time (Mathlib leaves this as `proof_wanted`).
- Closure of `ClassP` under complement, union, and intersection.
- **34.2** verification / certificates / `NP`, and `P ⊆ NP`.
- **34.3** polynomial-time reducibility `≤_P`, its transitivity, and the
  definitions of NP-hard / NP-complete.

Open problems (whether `P = NP`) and the specific NP-completeness reductions
(34.4–34.5: CIRCUIT-SAT, SAT, 3-CNF-SAT, CLIQUE, VERTEX-COVER, HAM-CYCLE,
SUBSET-SUM) are intentionally out of scope for now.
-/

namespace CLRS

namespace Chapter34

end Chapter34

end CLRS
