# Chapter 15.4 FIF Optimality Completion Design

Date: 2026-08-12

## Objective

Complete the main theorem of CLRS Fourth Edition Section 15.4: the
farthest-in-future eviction policy incurs no more cache misses than any
offline policy.

The section is complete only when the following theorem is public through
`S3_Optimality.lean` and has no proof-specific assumptions:

```lean
theorem fifo_optimal
    (π : Policy) (C₀ : Finset Page) (σ : List Page)
    (hC₀ : C₀.Nonempty) :
    misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ
```

The nonempty-cache hypothesis is part of the project cache model. No
`hB1`, `hB2`, `hAone`, slack-supply, hQ-supply, or other bridge hypothesis
may appear in the public theorem.

## Selected approach

Use legal cache traces and a local one-page coupling exchange argument.
Preserve the stable cache model, farthest-in-future definitions, and useful
local S3 lemmas. Replace the B7--B14 global iteration state machine as the
final proof architecture.

The proof follows the textbook exchange argument directly:

1. Convert an arbitrary policy run into a legal cache trace.
2. At the first transition that differs from FIF, replace the evicted page
   by FIF's farther-in-the-future choice.
3. Couple the old and new suffix traces while their caches differ by one
   page.
4. Show that the new trace incurs no more misses and agrees with FIF for one
   additional transition.
5. Iterate the exchange finitely until the entire trace agrees with FIF.

## Proof architecture

### Layer 1: legal cache traces

Introduce a trace abstraction containing a cache at every request boundary.
A trace is legal when:

- its cache at time zero is `C₀`;
- a hit leaves the cache unchanged;
- a fault removes a resident page and inserts the request;
- the transition laws are required only at request positions below
  `σ.length`.

Define the miss indicator and total miss count from trace cache membership.

Required results:

- `policyTrace`: the trace induced by a `Policy`;
- `policyTrace_valid`: every policy trace is legal;
- `traceMisses_policyTrace`: trace misses equal `misses`;
- `fifoTrace`: the trace induced by `fifoPolicy σ`;
- `validTrace_card`: legal traces preserve the initial cache cardinality;
- direct transition elimination lemmas for hit and fault cases.

Trace legality, rather than a separate reducedness bound, ensures that every
fault evicts a resident page. Bare schedules that can grow the cache through
no-op evictions are not used by the new iteration.

### Layer 2: exact one-page cache coupling

Define an exact cache-difference relation. For caches `A` and `B`,
`OnePageDiff A B a b` means:

- `a` is resident only in `A`;
- `b` is resident only in `B`;
- all other page memberships agree.

Equivalent erase/insert or set-difference characterizations may be added as
private helper lemmas, but the public proof surface should expose one stable
relation.

The suffix coupling has two phases.

#### Ordered phase

The transformed trace has page `q`; the source trace has page `p`; and the
next request of `q` occurs strictly before the next request of `p`, or `p` is
never requested again. No miss credit has yet been earned.

Before either differing page is requested:

- common hits preserve both caches;
- common faults are mirrored by evicting the same common resident page;
- if the source evicts its unique page `p`, the transformed trace evicts its
  unique page `q`, and the caches become equal.

When `q` is requested, the transformed trace hits while the source trace
faults. The transformed trace gains one miss of credit and enters the
credited phase unless the source transition makes the caches equal.

FIF's maximal-next-use theorem supplies the ordering. If both next uses are
concrete, equality of their positions is impossible for distinct pages, so
the non-strict `Farther` result yields the required strict request order.

#### Credited phase

The caches still differ by one page, but no next-use ordering is required.
The transformed trace has accumulated one miss of credit.

For each request:

- requests common to both caches preserve the relation;
- a common fault is mirrored, or the unique pages are evicted to merge the
  caches;
- a request of the transformed-only page creates another source miss and
  preserves a nonnegative credit;
- a request of the source-only page causes one transformed miss, consumes
  the available credit, and permits the traces to merge.

The main result of this layer constructs a legal transformed suffix and
proves its miss count is no greater than the source suffix's miss count.
Credit is local to this coupling theorem. It is not stored in a global
iteration state.

### Layer 3: one-step exchange

For a legal trace agreeing with FIF through boundary `t`, find the first
transition where its next cache differs from the FIF cache.

At that request:

- both traces have the same pre-request cache;
- both fault;
- the source trace evicts a resident page `q`;
- FIF evicts a distinct resident page `p`;
- `p` is at least as far in the future as `q`.

Apply the ordered and credited coupling results to construct a new legal
trace. The required theorem shape is:

```lean
theorem exchange_trace
    (hvalid : ValidTrace C₀ σ T)
    (hagree : AgreesWithFIF C₀ σ T t)
    (hdisagree : T.cache (t + 1) ≠ fifoTrace.cache (t + 1)) :
    ∃ T',
      ValidTrace C₀ σ T' ∧
      AgreesWithFIF C₀ σ T' (t + 1) ∧
      traceMisses σ T' ≤ traceMisses σ T
```

The exact representation of `T` and agreement may change during Lean
statement shaping, but the conclusion and absence of bridge hypotheses may
not be weakened.

### Layer 4: finite iteration and public theorem

Use strong induction on `σ.length - t`, or an equivalent finite measure, to
repeatedly apply `exchange_trace`.

Required results:

- a trace agreeing with FIF through `σ.length` has the same miss count as
  FIF;
- every valid trace can be transformed into a fully agreeing valid trace
  without increasing misses;
- applying the transformation to `policyTrace π` yields `fifo_optimal`.

The public theorem is added to `S3_Optimality.lean`, its section and chapter
facades, and a Chapter 15.4 interface test.

## Development layout

Develop the new proof in focused files under a new `Dev/Trace` subtree:

- `A1_LegalTrace.lean`;
- `A2_OnePageDiff.lean`;
- `A3_OrderedCoupling.lean`;
- `A4_CreditedCoupling.lean`;
- `A5_Exchange.lean`;
- `A6_Iteration.lean`.

The exact split may be adjusted to keep files focused. During development,
the files may import S3. After the proof closes, move or merge the theorem
stack into the public S3 source without an import cycle.

Do not move B7--B14 while the replacement proof is incomplete. Once the
public theorem and all gates pass, move the old state-machine files into
`Dev/Legacy` and ensure no public module imports them.

## Known failed approaches

Create `Dev/Legacy/FAILED_APPROACHES.md` before declaring completion. Each
entry must contain the attempted invariant, failure evidence, reusable local
results, and a rule preventing the same false completion criterion.

The initial entries are:

1. **Conditional final wrapper.** The private `fifo_optimal` in B7 accepts
   `hB1`, `hB2`, and `hAone`; kernel checking proves only a conditional
   theorem.
2. **Full-history hQ.** The bound is false once a pair's nop has passed; the
   local search reached 988 B2 steps from broken-hQ states.
3. **Plain natural-number slack.** `bad ≤ slack` has 492 searched
   counterexamples.
4. **Per-page/candidate-C credit as currently designed.** The identified
   credits still leave 164 residual two-consecutive-B1-bad windows and do not
   supply a closed global invariant.
5. **Skipping the case-one branch-1 position with `hnb`.** The next
   disagreement can land exactly at that position; raising the bound does not
   remove the required transition.
6. **Build-based completion.** No `sorry`, kernel checking, or a successful
   full build is sufficient when the intended public theorem is absent or
   conditional.
7. **Migration ledger collision.** Fourth-edition greedy Chapter 15.4 status
   was written into the third-edition Dynamic Programming Chapter 15 row.

Search counts are evidence against those exact invariant designs, not a
claim that every searched state is reachable. The source-level theorem
interfaces and explicit counterexamples remain the authoritative blockers.

## Verification gates

The following gates are cumulative. Passing an earlier gate cannot be
reported as completion of a later gate.

### G1: legal trace

- policy and FIF traces are legal;
- trace and policy miss counts agree;
- cache cardinality is preserved.

### G2: coupling

- ordered coupling compiles without assumptions beyond trace legality,
  one-page difference, and next-use order;
- credited coupling compiles with a local one-miss credit;
- focused examples cover merge-on-eviction, request-of-transformed-only,
  and request-of-source-only branches.

### G3: exchange

- `exchange_trace` compiles;
- its type has no B7--B14 bridge predicates;
- it increases FIF agreement by one transition and does not increase total
  misses.

### G4: public theorem

- `CLRS.Caching.fifo_optimal` is public through S3;
- its type is exactly the approved theorem up to harmless argument order;
- `#print axioms CLRS.Caching.fifo_optimal` shows no project-specific axiom.

### G5: repository integration

Run fresh checks:

```bash
lake env lean Tests/Chapter_15_4_Interface.lean
lake build CLRSLean.FourthEdition.Chapter_15
lake build CLRSLean
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching \
  Tests/Chapter_15_4_Interface.lean -g '*.lean'
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
git diff --check
```

Use the repository's actual checker names if they differ; record the exact
commands and outputs in the completion handoff.

The interface test must contain at least:

```lean
#check CLRS.Caching.fifo_optimal
#print axioms CLRS.Caching.fifo_optimal
```

It must also instantiate the theorem at its public type, so an accidentally
conditional theorem cannot satisfy the test.

Only after G5 passes may the section guide, Chapter 15 guide,
`CLRSLean/Status.lean`, README, and progress ledgers change from an explicit
optimality gap to complete.

## Completion rule

Chapter 15.4 is complete only when all of the following are true:

- the public unconditional `fifo_optimal` theorem exists;
- all G1--G5 checks pass freshly;
- no public source imports the legacy state machine;
- known failed approaches are recorded;
- third- and fourth-edition status ledgers describe the correct chapters;
- documentation claims match the public Lean interface.

No PR title, commit message, local supply lemma, placeholder scan, or build
result may override this rule.
