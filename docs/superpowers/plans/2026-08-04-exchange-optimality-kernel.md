# Exchange Optimality Kernel Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add one generic optimality-transport kernel and make Chapter 16 activity selection and Chapter 23 MST exchange proofs consume it without changing their public theorem types or progress counts.

**Architecture:** `CLRS.ProofPatterns.Exchange` owns the algorithm-independent `Optimal` certificate and two transitivity theorems.  Chapter 16 and Chapter 23 retain their domain structures and add exact conversions to and from `Optimal`; only their final optimality-composition proof bodies delegate to the common kernel.

**Tech Stack:** Lean 4, Mathlib, Lake, CLRS-Lean interface tests, repository Python checks, Git.

---

## File Map

- Modify `CLRSLean/ProofPatterns/Exchange.lean`: define the shared `Optimal`
  proposition and the two generic transport theorems.
- Modify `Tests/Common_Proof_Infrastructure.lean`: fix the shared interface,
  exercise maximization/minimization instances, and audit axioms.
- Modify `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`: add
  `MaxCardinality` bridges and delegate the certificate-to-optimality theorem.
- Modify `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`:
  add `IsMSTExtending` bridges and delegate exchange optimality transport.
- Modify `Tests/Chapter_23_Interface.lean`: fix the Chapter 23 bridge and legacy
  exchange theorem interface.
- Modify `docs/proof-patterns/common-proof-library-decision-matrix.md`: promote
  exchange optimality from deferred to active with two consumers.
- Modify `docs/proof-patterns/geometric-proof-patterns.md`: document the split
  between generic optimality transport and domain witnesses.
- Modify `docs/proof-patterns/greedy-exchange-certificates.md`: record Chapter
  16's shared-kernel delegation.
- Modify `docs/repository-architecture.md`: classify `Exchange` as active and
  leave `Boundary` deferred.
- Do not modify `docs/clrs-proof-progress.csv`, chapter status, navigation, or
  website configuration.

### Task 1: Fix The Shared Interface In A Red Test

**Files:**
- Modify: `Tests/Common_Proof_Infrastructure.lean`

- [x] **Step 1: Import the exchange module and add the missing public checks**

Add this import with the other imports:

```lean
import CLRSLean.ProofPatterns.Exchange
```

Add these checks after the existing shared infrastructure checks:

```lean
#check CLRS.ProofPatterns.Optimal
#check CLRS.ProofPatterns.Optimal.feasible_chosen
#check CLRS.ProofPatterns.Optimal.noWorse_than
#check CLRS.ProofPatterns.Optimal.of_noWorse
#check CLRS.ProofPatterns.optimal_of_exchange
```

Add these two examples inside `namespace CLRS`, before the Chapter 22 namespace:

```lean
example {feasible : Nat → Prop} {old new : Nat}
    (hold : ProofPatterns.Optimal feasible (· ≤ ·) old)
    (hnew : feasible new) (hnewOld : new ≤ old) :
    ProofPatterns.Optimal feasible (· ≤ ·) new :=
  ProofPatterns.Optimal.of_noWorse hold hnew hnewOld Nat.le_trans

example {feasible target : List Nat → Prop} {chosen : List Nat}
    (hchosen : feasible chosen)
    (hexchange : ∀ other, feasible other →
      ∃ exchanged, target exchanged ∧
        ProofPatterns.ExchangeCertificate.NoLessScore
          List.length exchanged other)
    (htarget : ∀ exchanged, target exchanged →
      ProofPatterns.ExchangeCertificate.NoLessScore
        List.length chosen exchanged) :
    ProofPatterns.Optimal feasible
      (ProofPatterns.ExchangeCertificate.NoLessScore List.length) chosen :=
  ProofPatterns.optimal_of_exchange hchosen hexchange htarget (by
    intro a b c hab hbc
    exact Nat.le_trans hbc hab)
```

- [x] **Step 2: Run the focused test and verify the intended red failure**

Run:

```bash
lake env lean Tests/Common_Proof_Infrastructure.lean
```

Expected: nonzero exit with `Unknown constant CLRS.ProofPatterns.Optimal` and
`Unknown constant CLRS.ProofPatterns.optimal_of_exchange`.  Fix only test
syntax if a different error occurs; do not add production declarations yet.

- [x] **Step 3: Commit the red interface contract**

```bash
git add Tests/Common_Proof_Infrastructure.lean
git commit -m "test(proofs): specify exchange optimality kernel"
```

### Task 2: Implement The Shared Optimality Kernel

**Files:**
- Modify: `CLRSLean/ProofPatterns/Exchange.lean`
- Modify: `Tests/Common_Proof_Infrastructure.lean`

- [x] **Step 1: Add `Optimal` and its transport theorem**

Insert this block after the namespace declarations and before
`ExchangeCertificate`:

```lean
/-- A feasible solution that is no worse than every feasible competitor. -/
structure Optimal
    (feasible : Solution → Prop)
    (noWorse : Solution → Solution → Prop)
    (chosen : Solution) : Prop where
  feasible_chosen : feasible chosen
  noWorse_than : ∀ other, feasible other → noWorse chosen other

namespace Optimal

/-- Replacing an optimum by a feasible no-worse solution preserves optimality. -/
theorem of_noWorse
    {Solution : Type u} {feasible : Solution → Prop}
    {noWorse : Solution → Solution → Prop} {old new : Solution}
    (hold : Optimal feasible noWorse old)
    (hnew : feasible new) (hnewOld : noWorse new old)
    (htrans : ∀ {a b c}, noWorse a b → noWorse b c → noWorse a c) :
    Optimal feasible noWorse new := by
  refine ⟨hnew, ?_⟩
  intro other hother
  exact htrans hnewOld (hold.noWorse_than other hother)

end Optimal

/-- A chosen feasible solution is optimal when every competitor exchanges to a
target that lies between the chosen solution and that competitor. -/
theorem optimal_of_exchange
    {Solution : Type u} {feasible target : Solution → Prop}
    {noWorse : Solution → Solution → Prop} {chosen : Solution}
    (hchosen : feasible chosen)
    (hexchange : ∀ other, feasible other →
      ∃ exchanged, target exchanged ∧ noWorse exchanged other)
    (htarget : ∀ exchanged, target exchanged → noWorse chosen exchanged)
    (htrans : ∀ {a b c}, noWorse a b → noWorse b c → noWorse a c) :
    Optimal feasible noWorse chosen := by
  refine ⟨hchosen, ?_⟩
  intro other hother
  rcases hexchange other hother with ⟨exchanged, hexchanged, hbetter⟩
  exact htrans (htarget exchanged hexchanged) hbetter
```

- [x] **Step 2: Add permanent axiom audits to the common interface**

Add immediately after the new `#check` declarations:

```lean
#print axioms CLRS.ProofPatterns.Optimal.of_noWorse
#print axioms CLRS.ProofPatterns.optimal_of_exchange
```

- [x] **Step 3: Run the shared module and interface test**

Run:

```bash
lake build +CLRSLean.ProofPatterns.Exchange
lake env lean Tests/Common_Proof_Infrastructure.lean
```

Expected: both commands exit zero.  The axiom audit must not contain `sorryAx`
or a project-defined axiom; these two elementary theorems should print an empty
axiom list.

- [x] **Step 4: Scan the shared implementation and commit**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/ProofPatterns/Exchange.lean
git diff --check
```

Expected: no placeholder declaration and no whitespace errors.

```bash
git add CLRSLean/ProofPatterns/Exchange.lean Tests/Common_Proof_Infrastructure.lean
git commit -m "feat(proofs): add exchange optimality kernel"
```

### Task 3: Bridge Chapter 16 Activity Selection

**Files:**
- Modify: `Tests/Common_Proof_Infrastructure.lean`
- Modify: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`

- [x] **Step 1: Add the Chapter 16 bridge contract before implementation**

Add this import to `Tests/Common_Proof_Infrastructure.lean`:

```lean
import CLRSLean.Chapter_16.Section_16_1_Activity_Selection
```

Add these public checks with the other compatibility checks:

```lean
#check CLRS.ActivitySelection.MaxCardinality.toOptimal
#check CLRS.ActivitySelection.maxCardinality_of_optimal
#check CLRS.ActivitySelection.greedy_choice_optimal_from_certificate
```

- [x] **Step 2: Verify the Chapter 16 bridge contract fails for the missing names**

Run:

```bash
lake env lean Tests/Common_Proof_Infrastructure.lean
```

Expected: nonzero exit reporting missing `MaxCardinality.toOptimal` and
`maxCardinality_of_optimal`; the established
`greedy_choice_optimal_from_certificate` check must still resolve.

- [x] **Step 3: Import the shared exchange module in Chapter 16**

Add near the top of
`CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`:

```lean
import CLRSLean.ProofPatterns.Exchange
```

- [x] **Step 4: Add exact `MaxCardinality` conversions**

Insert directly after the `MaxCardinality` structure:

```lean
namespace MaxCardinality

/-- View activity-selection maximum cardinality through the generic optimality
kernel. -/
theorem toOptimal {available selected : List Activity}
    (h : MaxCardinality available selected) :
    ProofPatterns.Optimal
      (fun candidate => candidate.Sublist available ∧ Feasible candidate)
      (ProofPatterns.ExchangeCertificate.NoLessScore List.length)
      selected :=
  ⟨⟨h.sublist, h.feasible⟩,
    fun other hother => h.maximum other hother.1 hother.2⟩

end MaxCardinality

/-- Recover the chapter-facing maximum-cardinality certificate from the generic
optimality kernel. -/
theorem maxCardinality_of_optimal {available selected : List Activity}
    (h : ProofPatterns.Optimal
      (fun candidate => candidate.Sublist available ∧ Feasible candidate)
      (ProofPatterns.ExchangeCertificate.NoLessScore List.length)
      selected) :
    MaxCardinality available selected :=
  ⟨h.feasible_chosen.1, h.feasible_chosen.2,
    fun other hsub hfeasible => h.noWorse_than other ⟨hsub, hfeasible⟩⟩
```

- [x] **Step 5: Delegate `greedy_choice_optimal_from_certificate`**

Replace only that theorem's proof body with:

```lean
by
  apply maxCardinality_of_optimal
  apply ProofPatterns.optimal_of_exchange
      (target := fun candidate =>
        ∃ tail, candidate = a :: tail ∧ tail.Sublist after ∧ Feasible tail)
  · exact ⟨hcert.chosen_sublist,
      feasible_cons hopt.feasible hcert.selected_after⟩
  · intro other hother
    rcases hcert.exchange other hother.1 hother.2 with
      ⟨tail, htail_sub, htail_feasible, hle_exchange⟩
    exact ⟨a :: tail, ⟨tail, rfl, htail_sub, htail_feasible⟩,
      hle_exchange⟩
  · intro candidate hcandidate
    rcases hcandidate with ⟨tail, rfl, htail_sub, htail_feasible⟩
    exact chosen_tail_bound_of_tail_optimal hopt htail_sub htail_feasible
  · intro x y z hxy hyz
    exact Nat.le_trans hyz hxy
```

Do not modify the theorem statement, `GreedyChoiceCertificate`, or any
downstream greedy theorem.

- [x] **Step 6: Run the Chapter 16 source and public interface**

Run:

```bash
lake build +CLRSLean.Chapter_16.Section_16_1_Activity_Selection
lake env lean Tests/Common_Proof_Infrastructure.lean
```

Expected: both exit zero and the established theorem check prints its original
type.

- [x] **Step 7: Commit the Chapter 16 bridge**

```bash
git diff --check
git add CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean Tests/Common_Proof_Infrastructure.lean
git commit -m "refactor(activity): share exchange optimality transport"
```

### Task 4: Bridge Chapter 23 MST Exchange

**Files:**
- Modify: `Tests/Chapter_23_Interface.lean`
- Modify: `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`

- [x] **Step 1: Add the Chapter 23 bridge contract before implementation**

Add these checks near the start of `Tests/Chapter_23_Interface.lean`:

```lean
#check CLRS.MST.IsMSTExtending.toOptimal
#check CLRS.MST.isMSTExtending_of_optimal
#check CLRS.MST.mst_exchange_preserves_prefix
```

- [x] **Step 2: Verify the Chapter 23 bridge contract fails for the missing names**

Run:

```bash
lake env lean Tests/Chapter_23_Interface.lean
```

Expected: nonzero exit reporting missing `IsMSTExtending.toOptimal` and
`isMSTExtending_of_optimal`; the legacy exchange theorem must still resolve.

- [x] **Step 3: Import the shared exchange module in Chapter 23**

Add near the top of
`CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`:

```lean
import CLRSLean.ProofPatterns.Exchange
```

- [x] **Step 4: Add exact `IsMSTExtending` conversions**

Insert directly after the `IsMSTExtending` structure:

```lean
namespace IsMSTExtending

/-- View an optimum extending a prefix through the generic optimality kernel. -/
theorem toOptimal {P : Problem E} {w : E → Nat} {A T : Finset E}
    (h : IsMSTExtending P w A T) :
    ProofPatterns.Optimal
      (fun candidate => P.IsSpanningTree candidate ∧ A ⊆ candidate)
      (ProofPatterns.ExchangeCertificate.NoGreaterCost (weight w)) T :=
  ⟨⟨h.tree, h.includes⟩,
    fun other hother => h.optimal other hother.1 hother.2⟩

end IsMSTExtending

/-- Recover the MST-facing optimum certificate from the generic kernel. -/
theorem isMSTExtending_of_optimal {P : Problem E} {w : E → Nat}
    {A T : Finset E}
    (h : ProofPatterns.Optimal
      (fun candidate => P.IsSpanningTree candidate ∧ A ⊆ candidate)
      (ProofPatterns.ExchangeCertificate.NoGreaterCost (weight w)) T) :
    IsMSTExtending P w A T :=
  ⟨h.feasible_chosen.1, h.feasible_chosen.2,
    fun other htree hincludes =>
      h.noWorse_than other ⟨htree, hincludes⟩⟩
```

- [x] **Step 5: Delegate `mst_exchange_preserves_prefix`**

Replace only that theorem's proof body with:

```lean
by
  apply isMSTExtending_of_optimal
  exact ProofPatterns.Optimal.of_noWorse hT.toOptimal
    ⟨h_tree, h_extends⟩
    (weight_insert_erase_le w hf he h_weight)
    (by
      intro X Y Z hXY hYZ
      exact Nat.le_trans hXY hYZ)
```

Do not modify the theorem statement, the graph-specific weight lemma, or any
cut/path certificate.

- [x] **Step 6: Run the Chapter 23 focused checks**

Run:

```bash
lake build +CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
lake env lean Tests/Chapter_23_Interface.lean
lake env lean Tests/Common_Proof_Infrastructure.lean
```

Expected: all three commands exit zero.  The Chapter 23 interface prints the
legacy theorem and both bridge declarations.

- [x] **Step 7: Commit the Chapter 23 bridge**

```bash
git diff --check
git add CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean Tests/Chapter_23_Interface.lean
git commit -m "refactor(mst): share exchange optimality transport"
```

### Task 5: Document Active Exchange Infrastructure

**Files:**
- Modify: `docs/proof-patterns/common-proof-library-decision-matrix.md`
- Modify: `docs/proof-patterns/geometric-proof-patterns.md`
- Modify: `docs/proof-patterns/greedy-exchange-certificates.md`
- Modify: `docs/repository-architecture.md`

- [x] **Step 1: Promote the decision-matrix row**

Replace the deferred Exchange row with:

```markdown
| Exchange optimality transport | `CLRS.ProofPatterns.Exchange` | Chapters 16 and 23 | Activity selection keeps `MaxCardinality` / `GreedyChoiceCertificate`; MST keeps `IsMSTExtending` / `CutCertificate` | The generic kernel and exact bridges add zero textbook groups; the two chapter optimality obligations retain their existing counts | Extend only when another consumer shares the same feasible/no-worse transport; keep witness construction local | Active geometric pattern |
```

- [x] **Step 2: Update the geometric-pattern atlas**

Change the top summary to say:

```markdown
- `Exchange.lean`：通用最优性与交换传递内核，Chapter 16 和 Chapter 23
  已通过各自的领域证书实际使用。
```

In the Exchange section, add the public kernel:

```markdown
`Optimal feasible noWorse chosen` 统一表示“chosen 可行，并且不劣于每个
可行竞争者”。`Optimal.of_noWorse` 处理一次可行且不变差的替换，
`optimal_of_exchange` 处理“每个竞争者先交换到一个中间 target，再由 chosen
支配 target”的证明。

Chapter 16 保留活动 tail witness；Chapter 23 保留 cut、path 和换边 witness。
公共库只负责 noWorse 的传递组合，不选择 witness，也不引入 classical choice。
```

Change the closing classification so only `Boundary` remains a deferred
candidate; `Exchange` is active.

- [x] **Step 3: Update the greedy-exchange note**

Replace its generic-skeleton introduction with:

```markdown
The generic Lean layer is `CLRS.ProofPatterns.Optimal` together with
`Optimal.of_noWorse` and `optimal_of_exchange` in
`CLRSLean/ProofPatterns/Exchange.lean`.  Chapter-specific certificates still
construct the exchange witness; the shared kernel transports the final
optimality relation.

The older total-function `ExchangeCertificate` remains available for problems
whose exchange operation is naturally functional.  Activity selection does
not force its existential tail witness through classical choice.
```

State in the Activity Selection subsection that
`greedy_choice_optimal_from_certificate` delegates its final transitivity step
to `optimal_of_exchange`.

- [x] **Step 4: Update repository architecture**

Replace the sentence classifying `Boundary` and `Exchange` together with:

```markdown
`Fiber`, `Interval`, and the `Exchange` optimality kernel now have concrete
chapter bridges.  `Boundary` remains deferred until a real proof site can use
its trace interface without duplicating the chapter induction.
```

- [x] **Step 5: Verify documentation consistency and unchanged counts**

Run:

```bash
git diff -- docs/clrs-proof-progress.csv
rg -n "Exchange.*deferred|Exchange.*尚无章节消费者|Boundary.*Exchange.*候选" docs/proof-patterns docs/repository-architecture.md
uv run python scripts/check_repository.py
git diff --check
```

Expected: no progress CSV diff, no stale deferred-Exchange description, all
repository checks pass, and no whitespace errors.

- [x] **Step 6: Commit documentation**

```bash
git add docs/proof-patterns/common-proof-library-decision-matrix.md docs/proof-patterns/geometric-proof-patterns.md docs/proof-patterns/greedy-exchange-certificates.md docs/repository-architecture.md
git commit -m "docs(proofs): record shared exchange optimality"
```

### Task 6: Run Final Proof Verification

**Files:**
- Verify all changed files; do not modify generated website output.

- [x] **Step 1: Run all focused Lean gates freshly**

```bash
lake env lean CLRSLean/ProofPatterns/Exchange.lean
lake env lean CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean
lake env lean CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
lake env lean Tests/Common_Proof_Infrastructure.lean
lake env lean Tests/Chapter_23_Interface.lean
```

Expected: every command exits zero; the axiom prints contain no `sorryAx`.

- [x] **Step 2: Audit placeholders and actual shared consumption**

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/ProofPatterns/Exchange.lean CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean Tests/Common_Proof_Infrastructure.lean Tests/Chapter_23_Interface.lean
rg -n 'ProofPatterns\.(Optimal|optimal_of_exchange)' CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
```

Expected: no unfinished declarations; both chapter files contain real calls to
the shared kernel.

- [x] **Step 3: Run repository and root Lean verification**

```bash
uv run python scripts/check_repository.py
git diff --check
lake build CLRSLean
```

Expected: repository checks pass, no whitespace errors, and the root Lean build
completes successfully.  Do not run `lake build :literateHtml`.

- [x] **Step 4: Review branch scope and commit any verification-only cleanup**

```bash
git status --short --branch
git diff main...HEAD --stat
git diff main...HEAD -- docs/clrs-proof-progress.csv
git log --oneline --decorate main..HEAD
```

Expected: only the planned Lean, test, design/plan, and proof-documentation
files changed; the progress CSV is unchanged.  If a small verification fix was
needed, stage only its exact files and commit it with:

```bash
git commit -m "chore(proofs): finalize exchange kernel verification"
```

Otherwise do not create an empty commit.
