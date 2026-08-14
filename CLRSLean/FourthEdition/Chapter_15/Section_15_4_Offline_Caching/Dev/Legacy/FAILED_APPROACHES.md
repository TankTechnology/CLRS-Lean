# Failed approaches to the Chapter 15.4 optimality proof

This file is the negative-results ledger for the abandoned schedule-state-machine
proof of farthest-in-future optimality.  The archived sources are under
`StateMachine/`; the accepted public proof instead uses legal cache traces and
a local one-page coupling under `Optimality/Trace/`.

The search counts below refute the stated invariant designs.  They are not
claims that every enumerated state is reachable.  Explicit theorem interfaces,
concrete counterexamples, and Lean proofs remain the authoritative evidence.

## 1. Conditional final wrapper (`hB1` / `hB2` / `hAone`)

- **Attempted invariant.**  `IterateState` tracked agreement, reducedness,
  natural-number slack, historical page pairs, and repair windows.  The B7
  iteration theorem delegated its remaining transitions to three supply
  hypotheses `hB1`, `hB2`, and `hAone`.
- **Failure evidence.**  The private theorem originally named `fifo_optimal`
  (renamed `fifo_optimal_conditional_legacy` during archival) in
  `StateMachine/B7_Iteration.lean` accepts all three supplies as arguments.
  Kernel checking therefore establishes only a conditional implication, not
  CLRS Theorem 15.5.  B8--B14 refine pieces of the supplies but never eliminate
  the conditional public boundary.
- **Reusable results.**  The schedule/cache algebra in S3, first-disagreement
  lemmas, exchange/repair transition calculations, exact miss accounting, and
  next-use lemmas remain useful mathematical facts.  They informed the trace
  proof's statement shaping and local transition split.
- **Recurrence-prevention rule.**  Completion requires an interface test that
  instantiates `CLRS.Caching.fifo_optimal` at the approved unconditional type.
  A theorem with any state-machine supply hypothesis cannot pass G4.

## 2. Full-history `hQ`

- **Attempted invariant.**  Store every historical repair pair in `Q` and
  require every live pair's first future request (its nop position) to remain
  strictly after the current disagreement.  The reverse-difference chain was
  then bounded by `Q.image`.
- **Failure evidence.**  Once a pair's nop has passed, the strict bound is
  arithmetically impossible.  `search_hq.py` found 10,236 B1 and 688 B2 steps
  with an old nop at or before the step, 212 B1 and 312 B2 boundary cases with
  the nop exactly at `t₂ + 1`, and **988 B2 steps entered from an already
  broken-`hQ` state**.  Pruning expired pairs also loses pages needed by the
  reverse-difference chain.
- **Reusable results.**  `b2_ehit_ne_per_page`, `last_pair_page_stays`,
  `creditedPage`, and `HQPerPageHyp` in `StateMachine/B14_PerPageHQ.lean`
  isolate valid consulted-pair and page-stays facts.  The reverse-difference
  lemmas remain valid with their explicit premises.
- **Recurrence-prevention rule.**  Never quantify a future-position bound over
  unpruned full history without proving preservation across the boundary where
  each stored position expires.  Test the extension step, not only consumers
  of the invariant.

## 3. Plain natural-number slack

- **Attempted invariant.**  Maintain
  `schedMisses d + slack ≤ initialMisses`, credit an exchange by one when its
  bad event does not occur, and pay each B1 repair from the same scalar slack;
  the key supply was `bad ≤ slack`.
- **Failure evidence.**  Exact enumeration in `search_slack.py` found
  **492 negative-slack executions**.  A minimal recorded counterexample is
  `σ = [1,1,3,2,4,1,2,4]`, `C₀ = {1,2}`, with the largest-resident source:
  an A step at 2 produces no credit, a free B2 step occurs at 4, then a real
  B1 bad at 5 requires one unit while slack is zero.  Of 3,836 B1 bads, 1,040
  are outside the directly covered `q₀'` case and 492 of those have zero
  slack.
- **Reusable results.**  `b1_exchange_no_bad_q0` and
  `b1_bad_le_slack_q0` correctly cover the `d t₂ = q₀'` subcase.
  `repair_step_swap_exact_net` and the exact B2 good/bad accounting are also
  sound local results.
- **Recurrence-prevention rule.**  A global natural-number potential must be
  proved nonnegative at every consumer.  Aggregate miss inequalities and a
  handful of locally credited cases do not establish a supply theorem.

## 4. Per-page credit and candidate-C credit

- **Attempted invariant.**  Replace scalar slack by pending-good balances per
  page, drawing a B1 bad first from the repaired page's balance; a candidate-C
  variant sends alive-alive B2 net savings to a global pool.
- **Failure evidence.**  The per-page design reduces the 492 failures only to
  336; candidate-C reduces them to **164**, not zero.  All 164 residual cases
  contain two consecutive B1 bads in one window.  The second required page has
  no pending good under any identified credit, so the proposed balance can go
  negative and no closed global invariant results.
- **Reusable results.**  The arithmetic lemmas
  `b1_bad_le_slack_credit`, `b1_draw_credit`, `b1_draw_slack`, and
  `b2_good_accrues` in `StateMachine/B13_PerPageCredit.lean` are correct under
  their explicit supply premises.  They document how a future proof could
  consume a genuinely established page credit.
- **Recurrence-prevention rule.**  A refined credit system is not accepted
  until exhaustive transition preservation closes every producer/consumer
  case and the initial/final potentials are connected to misses.  Reducing a
  counterexample count is diagnostic progress, not a proof.

## 5. Skipping the case-one branch-1 position with `hnb`

- **Attempted invariant.**  After a case-one exchange, raise the reducedness
  boundary `hnb'` past the unique branch-1 no-op position, expecting the next
  disagreement to occur after that boundary and return to case A.
- **Failure evidence.**  `search_caseone.py` found 7,384 branch-1 spots and
  zero multiple spots, but in every applicable trace the next disagreement
  lands **exactly at the branch-1 spot**, hence below `hnb' = s₁ + 1`.
  Example: `σ = [1,1,3,4,1]`, `C₀ = {1,2}`, exchange at 2, spot and next
  disagreement at 3.  Raising `hnb` relabels the required transition as case
  B; it does not remove it.  Unbounded junk positions also forced a vacuous
  `σ.length + 2` boundary rather than a finite reduced tail.
- **Reusable results.**  `case_one_D_minus_E_subset_q'`,
  `case_one_exchange_fault_imp_d_fault`, `case_one_branch1_once`, and the
  no-window B1 construction in B10--B12 are kernel-checked and precisely
  describe this exceptional transition.
- **Recurrence-prevention rule.**  A boundary shift is valid only after proving
  the next disagreement is on the permitted side.  Always test equality at
  the proposed boundary; do not infer progress from at-most-once alone.

## 6. Build-based false completion

- **Attempted criterion.**  Treat absence of `sorry`, kernel checking of every
  local file, or a successful repository build as evidence that §15.4 is
  complete.
- **Failure evidence.**  The legacy tree compiled while the only final wrapper
  was private and conditional on `hB1`, `hB2`, and `hAone`; the public section
  did not export an unconditional `fifo_optimal`.  A build checks declarations
  that exist, not the intended theorem that is missing.
- **Reusable results.**  Kernel checking and unfinished-marker scans remain
  necessary lower-level gates.  They become meaningful when combined with a
  public interface typecheck and `#print axioms`.
- **Recurrence-prevention rule.**  Completion is conjunctive: exact public
  theorem type, public import reachability, acceptable axiom report, focused
  interface instantiation, and repository checks must all pass freshly.

## 7. Third-/fourth-edition migration ledger collision

- **Attempted criterion.**  Reuse the existing `Chapter 15` progress row for
  the newly migrated §15.4 work without distinguishing editions or source
  paths.
- **Failure evidence.**  In CLRS third edition, Chapter 15 is Dynamic
  Programming; in the fourth edition, Chapter 15 is Greedy Algorithms and
  contains offline caching.  FIF progress was written into the legacy Dynamic
  Programming row, making a status claim that referred to the wrong chapter.
- **Reusable results.**  The compatibility map and explicit fourth-edition
  module hierarchy provide stable identities during migration.
- **Recurrence-prevention rule.**  Every progress entry must name the edition,
  chapter title, and canonical source path.  Never join migration ledgers by
  chapter number alone.

## Non-mathematical implementation incident

Deriving `Repr` for a coupling state containing `Finset` triggered a Lean
compiler panic on the project's release-candidate toolchain.  The instance was
unused, so removing the derivation restored compilation without changing any
definition or theorem.  This was a toolchain/diagnostic-surface issue, not a
failed mathematical route; avoid deriving runtime representations for proof
states unless a test actually needs them.
