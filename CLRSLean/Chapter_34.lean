import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility

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

### 34.2 Polynomial-Time Verification

* `CLRS.Chapter34.pairEncoding` — encode a certificate/input pair as one string
* `CLRS.Chapter34.PolyTimeVerifiable` — a language verifiable by a
  polynomial-time verifier with polynomial-size certificates
* `CLRS.Chapter34.ClassNP` — the class of polynomially verifiable languages

### 34.3 NP-Completeness and Reducibility

* `CLRS.Chapter34.PolyTimeReducible` — `L₁ ≤_P L₂`, polynomial-time
  reducibility
* `CLRS.Chapter34.NPHard` / `NPComplete` — the NP-hard / NP-complete classes
* `CLRS.Chapter34.ClassNPC` — the class of NP-complete languages

**Status: `partial`** — the complete framework (languages, polytime,
class `P`, class `NP`, reducibility, NP-hard/NP-complete) is defined.  The
following theorem layer is the documented next milestone:

- `Turing.TM2ComputableInPolyTime.comp`: composition of polynomial-time
  machines is polynomial-time (Mathlib leaves this as `proof_wanted`; the
  combined-machine construction is partially developed).  Unlocks `P ⊆ NP`
  and the transitivity of `PolyTimeReducible`.
- Concrete machine constructions (the empty/universal languages are in `P`).
- Closure of `ClassP` under complement, union, and intersection.
- `P ⊆ NP` and the NP-completeness characterization theorem.

Open problems (whether `P = NP`) and the specific NP-completeness reductions
(34.4–34.5: CIRCUIT-SAT, SAT, 3-CNF-SAT, CLIQUE, VERTEX-COVER, HAM-CYCLE,
SUBSET-SUM) are intentionally out of scope for now.
-/

namespace CLRS

namespace Chapter34

end Chapter34

end CLRS
