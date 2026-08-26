import CLRSLean.FourthEdition.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.FourthEdition.Chapter_34.Section_34_2_Polynomial_Time_Verification
import CLRSLean.FourthEdition.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility
import CLRSLean.FourthEdition.Chapter_34.Section_34_4_NP_Completeness_Proofs
import CLRSLean.FourthEdition.Chapter_34.Section_34_5_NP_Complete_Problems

/-!
# Chapter 34 — NP-Completeness

Chapter 34 develops the proof language of polynomial-time computation,
verification, and reduction, then uses it to establish the textbook's main
NP-completeness chain.  The canonical reader is organized into the five CLRS
sections below; implementation-heavy support modules remain available through
the compatibility source links on each section page.

## Chapter map

- [34.1 Polynomial Time](CLRSLean/FourthEdition/Chapter_34/Section_34_1_Polynomial_Time/)
  introduces the deterministic polynomial-time machine model and closure
  properties of {lit}`P`.
- [34.2 Polynomial-Time Verification](CLRSLean/FourthEdition/Chapter_34/Section_34_2_Polynomial_Time_Verification/)
  formalizes bounded certificates, verifiers, and {lit}`P ⊆ NP`.
- [34.3 NP-Completeness and Reducibility](CLRSLean/FourthEdition/Chapter_34/Section_34_3_NP_Completeness_And_Reducibility/)
  proves reduction transitivity and the transport rules for NP-hardness and
  NP-completeness.
- [34.4 NP-Completeness Proofs](CLRSLean/FourthEdition/Chapter_34/Section_34_4_NP_Completeness_Proofs/)
  contains Cook--Levin and the reductions through SAT, 3-CNF-SAT, and CLIQUE.
- [34.5 NP-Complete Problems](CLRSLean/FourthEdition/Chapter_34/Section_34_5_NP_Complete_Problems/)
  continues the chain through VERTEX-COVER, HAM-CYCLE, decision-TSP, and
  SUBSET-SUM.

## Main theorem chain

The formalization packages the textbook argument in four layers:

1. Polynomial-time functions compose, {lit}`P ⊆ NP`, and polynomial-time
   many-one reductions are transitive.
2. Cook--Levin gives a fixed polynomial-time reduction from every NP language
   to a well-formed general-circuit satisfiability instance, establishing
   {lit}`generalCircuitSAT_npComplete`.
3. Concrete total reduction machines establish
   {lit}`CIRCUIT-SAT ≤_P SAT ≤_P 3-CNF-SAT ≤_P CLIQUE`; the public CLIQUE
   target is the honest serialized graph-plus-{lit}`k` language.
4. The selected §34.5 chain closes strict NP-completeness for VERTEX-COVER,
   HAM-CYCLE, decision-TSP, and SUBSET-SUM.

## Coverage boundary

Status: main-proof-complete.  Every represented section has an explicit
reader page, concrete polynomial-time machines where the reduction or verifier
claim requires one, exact all-input semantic bridges, and the corresponding
public NP-completeness theorem.  A standalone direct SAT verifier is retained
as an optional refinement because SAT membership in NP already follows through
the proved reduction chain.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level ledger,
{lit}`docs/migrations/clrs4.md` for compatibility policy, and
{lit}`CLRSLean.Chapter_34`, rendered as
[the complete compatibility chapter](CLRSLean/Chapter_34/), for the full
implementation module tree.
-/
