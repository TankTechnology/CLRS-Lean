# Ch34 Verifier Rejection Runtime Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Strengthen the exact total semantics of the concrete general-circuit verifier into a uniform polynomial-time TM2 witness, then package the existing finite-certificate theorem as `GeneralCircuitSAT ∈ NP`.

**Architecture:** Preserve the current phased verifier and its exact successful and rejecting runs. Add a bounded rejection relation alongside the existing unbounded `Rejects` relation, lift each local rejection proof without changing machine behavior, cover the canonical and malformed top-level branches with one deliberately generous quartic polynomial, and expose only the final machine witness and NP theorem through the public general-circuit facade.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `StateTransition.EvalsToInTime` and `Turing.TM2ComputableInPolyTime`, `Polynomial ℕ`, Lake focused builds, direct Lean interface tests.

---

## Current checkpoint

The following proof surface already exists and is the baseline for this plan:

- `machine` is an executable TM2 implementation of `generalCircuitVerifier`.
- `verifier_run` proves the exact halting Boolean for every certificate/input pair.
- canonical valid, canonical invalid, malformed header, malformed gate stream,
  lookup failure, invalid output, and trailing-input branches all halt cleanly.
- `generalCircuitVerifierComputable` packages the total computation without a
  time bound.
- `successfulSteps_le` gives a quadratic bound on the well-formed canonical
  execution path.
- focused executable and interface regressions are green.

The missing theorem is not semantic correctness. It is a uniform step bound
for every rejecting route, including malformed inputs, followed by the
`TM2ComputableInPolyTime` and `PolyTimeVerifiable` wrappers.

## Known failed or rejected routes

- Do not infer a time bound from `verifier_run`: its existential step count has
  intentionally forgotten the quantitative information.
- Do not use `successfulSteps_le` as the final machine bound: Mathlib's
  polynomial-time witness quantifies over every encoded input, not only
  well-formed accepting inputs.
- Do not use `runFuel` or `native_decide` as proof of a polynomial bound. Those
  examples are regression tests, not universally quantified kernel proofs.
- Do not replace malformed-input rejection with an assumption that decoding
  succeeds. The public verifier is total and the machine theorem must preserve
  that behavior.
- Do not rebuild the verifier through a second compiler abstraction. The
  current exact phase lemmas already expose the transition structure needed
  for bounded composition; rebuilding would duplicate the highest-risk work.
- Do not optimize the asymptotic constant during this milestone. A transparent
  quartic envelope is preferable to a tight but brittle quadratic arithmetic
  proof.

## Verification policy

Do not run a full-repository build in this plan. Use only these focused gates:

```text
lake env lean Tests/Chapter_34_GeneralCircuit_VerifierMachine.lean
lake env lean Tests/Chapter_34_GeneralCircuit_Verifier_Runtime_Interface.lean
lake env lean Tests/Chapter_34_CookLevin_Interface.lean
lake env lean Tests/Chapter_34_PolyBuilder_Interface.lean
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine
git diff --check
```

Every newly public declaration first appears as an unresolved `#check` in the
runtime interface test. After implementation, the same test must be green and
the headline declarations must have no `sorryAx` in `#print axioms` output.

### Task 1: Lock the bounded-runtime interface

**Files:**

- Create: `Tests/Chapter_34_GeneralCircuit_Verifier_Runtime_Interface.lean`

- [ ] **Step 1: Add the RED interface**

Create a focused test importing the internal verifier facade and checking:

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine

namespace CLRS.Chapter34

#check Turing.GeneralCircuitVerifier.RejectsIn
#check Turing.GeneralCircuitVerifier.verifierTime
#check Turing.GeneralCircuitVerifier.verifier_outputs_in_time
#check Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime

end CLRS.Chapter34
```

- [ ] **Step 2: Record the expected failure**

Run:

```text
lake env lean Tests/Chapter_34_GeneralCircuit_Verifier_Runtime_Interface.lean
```

Expected: the first new identifier is unknown. Do not add placeholders.

### Task 2: Add bounded rejection composition

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/BoundedReject.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine.lean`
- Test: `Tests/Chapter_34_GeneralCircuit_Verifier_Runtime_Interface.lean`

- [ ] **Step 1: Define the quantitative rejection relation**

```lean
def RejectsIn (start : machine.Cfg) (bound : Nat) : Prop :=
  StateTransition.EvalsToInTime step start
    (some (haltList machine [false])) bound
```

Keep the existing `Rejects` theorem API intact. Add a forgetful theorem from
`RejectsIn start bound` to `Rejects start`.

- [ ] **Step 2: Prove bounded composition helpers**

Add:

```lean
theorem rejectsIn_after_cleanup_step ...
theorem RejectsIn.before_step ...
theorem RejectsIn.before_steps ...
theorem RejectsIn.mono ...
```

`before_steps` must use `EvalsToInTime.trans`, preserving the actual sum of the
phase bound and rejection bound. `mono` is the only place that weakens an exact
or local bound to a larger envelope.

- [ ] **Step 3: Turn only `RejectsIn` green**

Run the runtime interface test. Expected: `RejectsIn` resolves; the first
top-level runtime declaration remains red.

### Task 3: Bound cleanup, header, unary parse, and lookups

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/RejectBounds.lean`
- Import: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/BoundedReject.lean`

- [ ] **Step 1: Publish exact cleanup cost**

Lift `cleanup_phase` directly to `RejectsIn`. The bound must be
`cleanupSteps input certificate values scratch gateCount index saved + 1`,
where the final `+ 1` is the reject-to-cleanup transition already proved by
`rejects_after_cleanup_step`.

- [ ] **Step 2: Mirror the header and unary parser inductions**

Add bounded counterparts of:

- `input_count_args_phase`
- `input_count_reject`
- `input_count_reject_of_decNat_none`
- `parse_nat_reject_of_decNat_none`

Each theorem must state a concrete arithmetic bound over the lengths of the
stacks it scans. Keep the semantic induction order identical to the existing
unbounded theorem so the transition rewrites are reused rather than reproved.

- [ ] **Step 3: Bound failed certificate and gate lookups**

Add bounded counterparts of `certificate_lookup_reject` and
`gate_lookup_reject`. Their local bounds are linear in the scanned certificate
or value stack plus `cleanupSteps` for the resulting configuration.

- [ ] **Step 4: Compile the new layer**

Run:

```text
lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/RejectBounds.lean
```

Expected: exit 0. Use `omega` for linear stack accounting and isolate any
nonlinear envelope weakening into named arithmetic lemmas.

### Task 4: Bound invalid and malformed circuit routes

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/MalformedBounds.lean`
- Import: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/RejectBounds.lean`

- [ ] **Step 1: Bound invalid decoded gates**

Lift these existing proofs to `RejectsIn`:

- `gate_reject_of_not_valid`
- `gate_list_reject_of_not_valid`
- `output_reject_of_not_valid`
- `circuit_body_reject_of_not_wellFormed`

Use one local size measure containing the original input length, remaining
gate stream length, certificate length, value count, and scratch-stack length.
Prove once that every recursive gate route decreases or stays below the
original encoded-pair size.

- [ ] **Step 2: Bound malformed decoding routes**

Lift these existing proofs to `RejectsIn`:

- `gate_decode_reject`
- `gate_stream_reject_of_decode_none`
- `gate_stream_reject_of_trailing`
- `malformed_circuit_reject`
- `malformed_run`

State local bounds in terms of the complete pair length
`(pairEncoding certificate input).length`; avoid exposing internal stack-size
algebra in the final public theorem.

- [ ] **Step 3: Prove a single quartic domination lemma**

Define the natural envelope:

```lean
def verifierStepBound (n : Nat) : Nat := 10000 * (n + 1) ^ 4
```

Prove that the successful bound and every rejecting local bound are at most
`verifierStepBound n`. Tighten local constants only if Lean needs a smaller
normal form; do not lower the degree in this milestone.

- [ ] **Step 4: Compile malformed bounds**

Run the new file directly. Expected: exit 0 and no `sorry`, `admit`, `axiom`,
or `proof_wanted` in either bounded-runtime file.

### Task 5: Package total polynomial-time computation

**Files:**

- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/Runtime.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine.lean`
- Test: `Tests/Chapter_34_GeneralCircuit_Verifier_Runtime_Interface.lean`

- [ ] **Step 1: Define the polynomial envelope**

```lean
noncomputable def verifierTime : Polynomial Nat :=
  10000 * (Polynomial.X + 1) ^ 4
```

Prove its evaluation lemma exactly:

```lean
@[simp] theorem verifierTime_eval (n : Nat) :
    verifierTime.eval n = verifierStepBound n
```

- [ ] **Step 2: Prove total bounded output**

```lean
noncomputable def verifier_outputs_in_time
    (certificate input : List CircuitSym) :
    TM2OutputsInTime machine (pairEncoding certificate input)
      (some (boolEncoding (generalCircuitVerifier certificate input)))
      (verifierTime.eval (pairEncoding certificate input).length)
```

Split exactly as `verifier_run` does: successful decode and verifier-true use
`successful_run` plus `successfulSteps_le`; decoded rejection uses the bounded
canonical rejection theorem; failed decode uses the bounded malformed theorem.

- [ ] **Step 3: Package Mathlib's machine witness**

```lean
noncomputable def generalCircuitVerifierComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CircuitSym × List CircuitSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => generalCircuitVerifier pr.1 pr.2)
```

Use `machine`, identity alphabet equivalences, `verifierTime`, and
`verifier_outputs_in_time`. Do not retain a second machine implementation.

- [ ] **Step 4: Audit and verify**

Add:

```lean
#print axioms Turing.GeneralCircuitVerifier.verifier_outputs_in_time
#print axioms Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime
```

Run both verifier tests and the verifier facade build from the verification
policy. Expected: all green and no `sorryAx`.

### Task 6: Export `GeneralCircuitSAT ∈ NP`

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/Verifier.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `Tests/Chapter_34_CookLevin_Interface.lean`

- [ ] **Step 1: Add the RED public checks**

```lean
#check generalCircuitVerifierComputableInPolyTime
#check generalCircuitSAT_verifiable
```

The first check is re-exported from the public verifier module; the second is
the chapter-level NP membership theorem.

- [ ] **Step 2: Package the existing certificate semantics**

```lean
theorem generalCircuitSAT_verifiable :
    PolyTimeVerifiable GeneralCircuitSAT := by
  refine ⟨generalCircuitVerifier, Polynomial.X, ?_, ?_⟩
  · exact ⟨Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime⟩
  · intro input
    simpa using mem_generalCircuitSAT_iff_exists_certificate input
```

Adjust only namespace qualification or `Polynomial.X.eval`; do not change the
certificate language or weaken the exact membership theorem.

- [ ] **Step 3: Run the focused public gates**

Run the Cook--Levin interface test, verifier runtime interface test, verifier
executable regression, and `git diff --check`. Expected: exit 0 for all.

- [ ] **Step 4: Commit the completed verifier milestone**

Commit only after all focused gates pass and the axiom scan is clean.

## Exit criteria and next attack order

This plan is complete only when all of the following are true:

- every certificate/input pair has a kernel-checked bounded TM2 run;
- the bound is the evaluation of an explicit `Polynomial Nat`;
- `generalCircuitVerifierComputableInPolyTime` is public and axiom-clean;
- `generalCircuitSAT_verifiable : PolyTimeVerifiable GeneralCircuitSAT` is
  public and protected by the Ch34 interface test;
- malformed and rejecting routes remain covered by executable regressions;
- no full-repository build was needed to establish the checkpoint.

After this verifier milestone, resume the remaining Ch34 chain in this order:

1. implement the concrete Cook--Levin generator TM from Task 10 of
   `docs/superpowers/plans/2026-08-13-ch34-cook-levin.md`;
2. package `polyTimeVerifiable_reducible_to_generalCircuitSAT`;
3. prove `generalCircuitSAT_npHard` and `generalCircuitSAT_npComplete`;
4. run the Ch34 trust/axiom gate and only then update chapter status prose;
5. defer the general graph-plus-`k` CLIQUE/Section 34.5 issue to its separately
   approved milestone rather than mixing it into Cook--Levin closure.
