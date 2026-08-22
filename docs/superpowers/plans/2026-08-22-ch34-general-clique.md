# Chapter 34 Honest General CLIQUE Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the specialized occurrence-language alias with a genuine serialized graph-plus-`k` CLIQUE language, prove its certificate semantics and NP membership, and give a concrete polynomial-time 3-CNF-SAT reduction.

**Architecture:** Keep the existing occurrence-CLIQUE construction intact. Build the general instance model, unique codecs, language, certificate checker, occurrence reduction, and concrete machines in focused modules under `GeneralClique/`. Change the public `CLIQUE` alias only in the final atomic migration.

**Tech Stack:** Lean 4, Mathlib finite lists/finsets, the Chapter 34 `Language`/`PolyTimeVerifiable`/`PolyTimeReducible` interfaces, existing TM2 machinery, and verified `PolyBuilder` scan/loop combinators.

---

## Invariants for every checkpoint

- Work only in `/home/ubuntu/clrs-lean-worktrees/codex/ch34-general-clique` on branch `codex/ch34-general-clique`.
- Keep new proof files focused; split a file before it becomes a mixed semantic/controller/runtime module.
- Add doc comments to every public declaration.
- Never add `sorry`, `admit`, `axiom`, or a theorem whose hypothesis merely assumes the intended conclusion.
- Run `lake env lean <changed-file>` before each commit and `git diff --check` for every checkpoint.
- Do not change the public meaning of `CLIQUE` until Tasks 1–10 are green.

## Task 1: Add a red public-contract test

**Files:**

- Create: `Tests/Chapter_34_GeneralClique_Interface.lean`

- [x] Add checks for the exact final API:

```lean
import CLRSLean.Chapter_34

namespace CLRS.Chapter34

#check CliqueSym
#check CliqueInstance
#check CliqueInstance.WellFormed
#check CliqueInstance.HasClique
#check encodeCliqueInstance
#check decodeCliqueInstance
#check decode_encodeCliqueInstance
#check encodeCliqueCertificate
#check decodeCliqueCertificate
#check decode_encodeCliqueCertificate
#check GeneralCLIQUE
#check mem_generalCLIQUE_iff
#check cliqueVerifier
#check cliqueVerifier_eq_true_iff
#check mem_generalCLIQUE_iff_exists_certificate
#check generalCLIQUE_polyTimeVerifiable
#check generalCLIQUE_mem_ClassNP
#check occurrenceCliqueInstance
#check cnfSatisfiable_iff_occurrenceCliqueInstance
#check threeCNFToGeneralCliqueMap
#check threeCNFToGeneralCliqueMap_mem_iff
#check Turing.TMClique.threeCNFSat_reducible_to_generalCLIQUE
#check CLIQUE
#check Turing.TMClique.threeCNFSat_reducible_to_CLIQUE

end CLRS.Chapter34
```

- [x] Run `lake env lean Tests/Chapter_34_GeneralClique_Interface.lean` and confirm it fails first at unknown `CliqueSym`.
- [x] Commit the red contract: `git add Tests/Chapter_34_GeneralClique_Interface.lean && git commit -m "test(ch34): specify honest general CLIQUE interface"`.

## Task 2: Define graph-plus-`k` semantics

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Instance.lean`
- Create: `Tests/Chapter_34_GeneralClique_Instance.lean`

- [x] Add executable small examples first: the triangle has a 3-clique, the three-vertex path does not, malformed oriented edges are not well formed.
- [x] Define:

```lean
structure CliqueInstance where
  vertexCount : Nat
  targetSize : Nat
  edges : List (Nat × Nat)
  deriving DecidableEq, Repr

namespace CliqueInstance

def WellFormed (I : CliqueInstance) : Prop :=
  I.targetSize ≤ I.vertexCount ∧
  I.edges.Nodup ∧
  ∀ e ∈ I.edges, e.1 < e.2 ∧ e.2 < I.vertexCount

def Adj (I : CliqueInstance) (u v : Nat) : Prop :=
  if u < v then (u, v) ∈ I.edges
  else if v < u then (v, u) ∈ I.edges
  else False

def HasClique (I : CliqueInstance) : Prop :=
  ∃ vertices : Finset Nat,
    vertices.card = I.targetSize ∧
    (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → I.Adj u v

end CliqueInstance
```

- [x] Prove `Adj` symmetry, irreflexivity, and the normalized-edge introduction/elimination lemmas used by the reduction.
- [x] Run `lake env lean Tests/Chapter_34_GeneralClique_Instance.lean` and the source file.
- [x] Commit: `git commit -am "feat(ch34): define general CLIQUE semantics"`.

## Task 3: Implement the unique instance and certificate codecs

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Encoding/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Encoding/Parser.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Encoding/RoundTrip.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Encoding/Length.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Encoding.lean`
- Create: `Tests/Chapter_34_GeneralClique_Encoding.lean`

- [x] Introduce the disjoint eight-symbol alphabet and encoders:

```lean
inductive CliqueSym
  | instanceMark | certificateMark | tick | fieldSep
  | edgeMark | vertexMark | pairSep | recordEnd
  deriving DecidableEq, Repr

def encodeCliqueEdge (e : Nat × Nat) : List CliqueSym :=
  .edgeMark :: List.replicate e.1 .tick ++ [.pairSep] ++
    List.replicate e.2 .tick ++ [.recordEnd]

def encodeCliqueInstance (I : CliqueInstance) : List CliqueSym :=
  .instanceMark :: List.replicate I.vertexCount .tick ++ [.fieldSep] ++
    List.replicate I.targetSize .tick ++ [.fieldSep] ++
    I.edges.flatMap encodeCliqueEdge

def encodeCliqueVertex (v : Nat) : List CliqueSym :=
  .vertexMark :: List.replicate v .tick ++ [.recordEnd]

def encodeCliqueCertificate (vertices : List Nat) : List CliqueSym :=
  .certificateMark :: vertices.flatMap encodeCliqueVertex
```

- [x] Implement total, complete-consumption parsers `decodeCliqueInstance` and `decodeCliqueCertificate`; reject missing markers, partial records, misplaced grammar tokens, and trailing fragments.
- [x] Prove unconditional round trips:

```lean
theorem decode_encodeCliqueInstance (I : CliqueInstance) :
    decodeCliqueInstance (encodeCliqueInstance I) = some I

theorem decode_encodeCliqueCertificate (vertices : List Nat) :
    decodeCliqueCertificate (encodeCliqueCertificate vertices) = some vertices
```

- [x] Prove encoder length formulae and the stronger combined bound `vertexCount + targetSize + 3 ≤ input.length` for successfully decoded inputs.
- [x] Test both round trips and at least six malformed cases.
- [x] Run all focused encoding source files and `Tests/Chapter_34_GeneralClique_Encoding.lean`.
- [x] Commit: `git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique Tests/Chapter_34_GeneralClique_Encoding.lean && git commit -m "feat(ch34): add exact general CLIQUE codecs"`.

## Task 4: Define the raw language and its typed bridge

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Language.lean`
- Create: `Tests/Chapter_34_GeneralClique_Language.lean`

- [x] Add tests showing an encoded clique is accepted, a decoded duplicate-edge instance is rejected by well-formedness, and a certificate-marked string is rejected.
- [x] Define the raw language and prove both characterizations:

```lean
def GeneralCLIQUE : Language CliqueSym :=
  { input | ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique }

theorem mem_generalCLIQUE_iff (input : List CliqueSym) :
    input ∈ GeneralCLIQUE ↔
      ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique

theorem encodeCliqueInstance_mem_generalCLIQUE_iff
    (I : CliqueInstance) :
    encodeCliqueInstance I ∈ GeneralCLIQUE ↔ I.WellFormed ∧ I.HasClique
```

- [x] Run source and language tests.
- [x] Commit: `git commit -am "feat(ch34): define honest general CLIQUE language"`.

## Task 5: Close Boolean certificate semantics

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Certificate/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Certificate/Semantics.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Certificate/Length.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Certificate.lean`
- Create: `Tests/Chapter_34_GeneralClique_Certificate.lean`

- [x] Define an executable list predicate and checker:

```lean
def CliqueInstance.ListRepresentsClique
    (I : CliqueInstance) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧ vertices.length = I.targetSize ∧
  (∀ v ∈ vertices, v < I.vertexCount) ∧
  ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → I.Adj u v

def cliqueVerifier (certificate input : List CliqueSym) : Bool :=
  match decodeCliqueInstance input, decodeCliqueCertificate certificate with
  | some I, some vertices => decide (I.WellFormed ∧ I.ListRepresentsClique vertices)
  | _, _ => false
```

- [x] Prove the all-input truth theorem `cliqueVerifier_eq_true_iff` by case-splitting both decoders and reducing `decide`.
- [x] Prove a nodup list represents a clique iff its `toFinset` witnesses `HasClique`; use the finite set's duplicate-free `toList` to construct the canonical certificate in the reverse direction.
- [x] Prove:

```lean
theorem mem_generalCLIQUE_iff_exists_certificate (input : List CliqueSym) :
    input ∈ GeneralCLIQUE ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        cliqueVerifier certificate input = true
```

- [x] Run source and certificate tests.
- [x] Commit: `git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Certificate* Tests/Chapter_34_GeneralClique_Certificate.lean && git commit -m "feat(ch34): prove general CLIQUE certificate semantics"`.

## Task 6: Construct the indexed occurrence graph

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Instance.lean`
- Create: `Tests/Chapter_34_GeneralClique_OccurrenceInstance.lean`

- [x] Enumerate literal positions row-major as records carrying clause index, position index, and literal; define numeric vertex lookup by list index.
- [x] Define `occurrenceCliqueEdges` by filtering all normalized numeric pairs `u < v` for different-clause and non-complementary positions, then define:

```lean
def occurrenceCliqueInstance (f : CNF) : CliqueInstance where
  vertexCount := (indexedOccurrences f).length
  targetSize := f.length
  edges := occurrenceCliqueEdges f
```

- [x] Prove edge nodup, normalized endpoints, range bounds, and `occurrenceCliqueInstance_wellFormed` under the exact hypothesis that every clause is nonempty. (`IsThreeCNF` alone permits empty clauses.)
- [x] Prove exact adjacency/indexed-occurrence lookup equivalence.
- [x] Test repeated equal literals in one or different clauses to ensure positions remain distinct.
- [x] Run source and occurrence-instance tests.
- [x] Commit: `git commit -am "feat(ch34): construct indexed occurrence clique graph"`.

## Task 7: Prove the textbook semantic reduction

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Semantics.lean`
- Create: `Tests/Chapter_34_GeneralClique_OccurrenceSemantics.lean`

- [x] Build an explicit map between old occurrence vertices `(clauseIndex, literal)` plus a membership proof and the new numeric row-major positions; use clause-position indices so repeated literals are not collapsed.
- [x] In the forward direction, transport the existing first-true-literal occurrence witness through a proved injective choice of numeric positions; preserve exact cardinality and non-complementarity.
- [x] In the reverse direction, map numeric positions back to occurrence vertices, prove injectivity from adjacency, and reuse the existing assignment-from-clique theorem.
- [x] Publish the stronger all-CNF theorem:

```lean
theorem cnfSatisfiable_iff_occurrenceCliqueInstance (f : CNF) :
    CnfSatisfiable f ↔ (occurrenceCliqueInstance f).HasClique
```

- [x] Cross-check the new theorem against the existing `cnfSatisfiable_iff_hasClique` on satisfiable, contradictory, and empty-clause formulae.
- [x] Run source and semantic tests.
- [x] Commit: `git commit -am "proof(ch34): reduce 3-CNF semantics to general CLIQUE"`.

## Task 8: Close the total raw map and cubic output bound

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Encoding.lean`
- Create: `Tests/Chapter_34_GeneralClique_RawReduction.lean`

- [ ] Define the canonical well-formed no-instance and total map:

```lean
def noCliqueInstance : CliqueInstance :=
  { vertexCount := 2, targetSize := 2, edges := [] }

def threeCNFToGeneralCliqueMap (input : List CNFSym) : List CliqueSym :=
  let f := decodeCNF input
  if IsThreeCNF f then encodeCliqueInstance (occurrenceCliqueInstance f)
  else encodeCliqueInstance noCliqueInstance
```

- [ ] Prove rejection of the fallback, then the exact raw theorem:

```lean
theorem threeCNFToGeneralCliqueMap_mem_iff (input : List CNFSym) :
    threeCNFToGeneralCliqueMap input ∈ GeneralCLIQUE ↔ input ∈ ThreeCNFSat
```

- [ ] Bound the position count by `input.length`, edge count by its square, every endpoint by the position count, and assemble:

```lean
theorem threeCNFToGeneralCliqueMap_length (input : List CNFSym) :
    (threeCNFToGeneralCliqueMap input).length ≤ 64 * (input.length + 1) ^ 3
```

- [ ] Run source and raw-reduction tests.
- [ ] Commit: `git commit -am "proof(ch34): close raw 3-CNF to CLIQUE map"`.

## Task 9: Build the concrete reduction TM2

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Machine/Core.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Machine/Semantics.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Machine/PolynomialRuntime.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/OccurrenceReduction/Machine.lean`

- [ ] Reuse the existing CNF parser phases for the `IsThreeCNF` branch and the verified row-major bounded-loop controllers for the pair enumeration; keep the controller state type local to `Turing.TMClique`.
- [ ] Define a fixed machine `threeCNFToGeneralCliqueMachine` and prove its exact output on every raw source string:

```lean
theorem threeCNFToGeneralCliqueMachine_outputs (input : List CNFSym) :
    OutputsOnInput threeCNFToGeneralCliqueMachine input
      (threeCNFToGeneralCliqueMap input)
```

- [ ] Derive a named polynomial runtime bound `threeCNFToGeneralCliqueRuntimePolynomial` from the phase bounds, rather than using only the output-length theorem.
- [ ] Assemble `threeCNFToGeneralCliqueComputableInPolyTime` and:

```lean
theorem threeCNFSat_reducible_to_generalCLIQUE :
    PolyTimeReducible ThreeCNFSat GeneralCLIQUE
```

- [ ] Run every machine submodule and a focused interface file checking the exact machine, map theorem, runtime polynomial, and reduction.
- [ ] Commit: `git commit -am "feat(ch34): add concrete 3-CNF to general CLIQUE machine"`.

## Task 10: Build the concrete verifier TM2 and NP assembly

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/Parse.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/VertexChecks.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/PairChecks.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/Semantics.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine/PolynomialRuntime.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/VerifierMachine.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/NP.lean`

- [ ] Use distinct phases for complete parsing, well-formedness, certificate nodup/range/cardinality, and pairwise edge lookup. Malformed strings share one bounded reject/cleanup path.
- [ ] Prove exact output equivalence with the previously fixed Boolean function `cliqueVerifier`; do not redefine acceptance around the machine.
- [ ] Publish a named polynomial `generalCliqueVerifierRuntimePolynomial` and prove the machine runs within it on the paired certificate/input encoding.
- [ ] Assemble:

```lean
theorem generalCLIQUE_polyTimeVerifiable :
    PolyTimeVerifiable GeneralCLIQUE := by
  refine ⟨cliqueVerifier, Polynomial.X ^ 2, ?_, ?_⟩
  · exact ⟨Turing.GeneralCliqueVerifier.cliqueVerifierComputableInPolyTime⟩
  · exact mem_generalCLIQUE_iff_exists_certificate

theorem generalCLIQUE_mem_ClassNP : GeneralCLIQUE ∈ ClassNP CliqueSym :=
  (mem_ClassNP GeneralCLIQUE).2 generalCLIQUE_polyTimeVerifiable
```

- [ ] Run every verifier submodule and a focused NP interface file.
- [ ] Commit: `git commit -am "proof(ch34): place general CLIQUE in NP"`.

## Task 11: Perform the atomic public migration

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Public.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CNFToClique.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CNFToCliqueMachine.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `Tests/Chapter_34_Interface.lean`
- Modify: `Tests/Chapter_34_GeneralClique_Interface.lean`

- [ ] Remove only the misleading legacy `abbrev CLIQUE`; retain `ThreeCNFOccurrenceCLIQUE` and `threeCNFSat_reducible_to_threeCNFOccurrenceCLIQUE` unchanged.
- [ ] In `Public.lean`, define:

```lean
abbrev CLIQUE : Language CliqueSym := GeneralCLIQUE

namespace Turing.TMClique

theorem threeCNFSat_reducible_to_CLIQUE :
    PolyTimeReducible ThreeCNFSat CLIQUE :=
  threeCNFSat_reducible_to_generalCLIQUE

end Turing.TMClique
```

- [ ] Import the ordered `GeneralClique` facade from the §34.4 and Chapter 34 facades.
- [ ] Make both public interface tests pass and search for stale prose asserting that `CLIQUE` is an occurrence-language alias.
- [ ] Run `lake build CLRSLean.Chapter_34` and `lake env lean Tests/Chapter_34_Interface.lean`.
- [ ] Commit: `git commit -am "feat(ch34): publish honest general CLIQUE"`.

## Task 12: Documentation, policy audit, and final verification

**Files:**

- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify: `docs/chapter-34-proof-map.md`
- Modify: the Chapter 34 progress CSV named by `CLAUDE.md`
- Modify: `literate.toml`

- [ ] State precisely that general CLIQUE now has an honest raw encoding, exact certificate checker, NP membership, and concrete 3-CNF-SAT reduction.
- [ ] State separately that `NPComplete CLIQUE` still depends on a fully concrete upstream reduction chain from arbitrary `L ∈ NP` through GeneralCircuitSAT/SAT/3-CNF-SAT if that chain is not already available at this checkpoint.
- [ ] Register every new literate Lean source and update proof-map ownership without counting the specialized occurrence language as the general language.
- [ ] Run fresh verification:

```text
lake env lean Tests/Chapter_34_GeneralClique_Interface.lean
lake env lean Tests/Chapter_34_Interface.lean
lake build CLRSLean.Chapter_34
python3 scripts/check_repository.py
git diff --check
rg -n "\b(sorry|admit|axiom)\b" CLRSLean/Chapter_34 Tests/Chapter_34_GeneralClique_*.lean
```

- [ ] Inspect `git status --short`, review the complete branch diff against `origin/main`, and commit only the verified documentation/audit changes:

```text
git add CLRSLean/Chapter_34 docs literate.toml
git commit -m "docs(ch34): record honest general CLIQUE closure"
```

- [ ] Do not merge or push until the user-facing checkpoint reports the exact passing commands and any remaining dependency for a full `NPComplete CLIQUE` theorem.
