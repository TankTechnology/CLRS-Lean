import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification.PairProjection
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToClique
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToCliqueMachine

/-! # Chapter 34 — NP-Completeness

Chapter 34 of CLRS covers NP-completeness: the complexity classes **P** and
**NP**, polynomial-time reducibility, and NP-completeness.

This chapter formalizes the framework of Section 34.1 — languages,
polynomial-time computability, polynomial-time decision, and the class **P** —
built on Mathlib's `Turing.TM2ComputableInPolyTime` (machine-level
polynomial-time computability with `Polynomial ℕ` time bounds), along with the
polynomial-time verification model of §34.2, the reducibility and NP-completeness
classes of §34.3, and the concrete NP-completeness reductions of §34.4
(CIRCUIT-SAT, SAT, 3-CNF-SAT, and CLIQUE).

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

### 34.4 NP-Completeness Proofs

* `CLRS.Chapter34.circuitSatisfiable_iff_satisfiable_circuitToFormula` — a
  circuit is satisfiable iff the equivalent formula is (Lemma 34.6)
* `CLRS.Chapter34.cnfSatisfiable_to3CNF_iff` — a formula is satisfiable iff
  its Tseitin 3-CNF transformation is (Lemma 34.7)
* `CLRS.Chapter34.cnfSatisfiable_iff_hasClique` / `cnfSatisfiable_iff_hasClique_3CNF` —
  a 3-CNF formula is satisfiable iff its literal-occurrence graph has a clique
  of the clause-count size (Lemma 34.10)
* `CLRS.Chapter34.Turing.TMClique.threeCNFSat_reducible_to_CLIQUE` — the
  3-CNF-SAT → CLIQUE reduction is polynomial-time computable
* The TM2 machines in `SatTo3CNFMachine` and `CNFToCliqueMachine` implement the
  §34.4 reduction functions as linear-time TMs

**Status: `partial`** — the complete framework (languages, polytime,
class `P`, class `NP`, reducibility, NP-hard/NP-complete) is defined, and the
theorem layer is complete: composition, `P ⊆ NP`, transitivity of `≤_P`,
closure of `ClassP` under complement, union, and intersection, and the §34.4
reduction chain CIRCUIT-SAT → SAT → 3-CNF-SAT → CLIQUE.  The §34.5 reductions
(VERTEX-COVER, HAM-CYCLE, SUBSET-SUM) remain unrepresented.

Theorem layer:

- `Turing.TM2ComputableInPolyTime.comp` (via `Turing.TM2Comp.comp_scratch`):
  composition of polynomial-time machines is polynomial-time (Mathlib leaves
  this as `proof_wanted`; closed here).  Unlocks `P ⊆ NP` and the transitivity
  of `PolyTimeReducible`.
- `PolyTimeDecidable.compl` / `ClassP_compl`: `P` is closed under complement.
- `PolyTimeDecidable.union` / `ClassP_union` and `PolyTimeDecidable.inter` /
  `ClassP_inter`: `P` is closed under union and intersection, via the AND/OR
  machine `Turing.TM2AndOr.andOrMachine` (which duplicates the input, runs both
  deciders, and combines with AND/OR).
- `ClassP_subset_ClassNP`: `P ⊆ NP` (Theorem 34.2).
- `circuitSatisfiable_iff_satisfiable_circuitToFormula` (Lemma 34.6):
  CIRCUIT-SAT poly-reduces to SAT.
- `cnfSatisfiable_to3CNF_iff` (Lemma 34.7): SAT poly-reduces to 3-CNF-SAT.
- `cnfSatisfiable_iff_hasClique` / `cnfSatisfiable_iff_hasClique_3CNF`
  (Lemma 34.10): 3-CNF-SAT poly-reduces to CLIQUE, with the reduction computed
  by the linear-time TM of `CNFToCliqueMachine`
  (`CLRS.Chapter34.Turing.TMClique.threeCNFSat_reducible_to_CLIQUE`).

Open problems (whether `P = NP`) and the remaining NP-completeness reductions
(§34.5: VERTEX-COVER, HAM-CYCLE, SUBSET-SUM) are intentionally out of scope for
now.
-/

namespace CLRS

namespace Chapter34

end Chapter34

end CLRS
