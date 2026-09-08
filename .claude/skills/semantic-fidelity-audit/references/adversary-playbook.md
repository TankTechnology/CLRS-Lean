# Adversary Playbook

The goal is to maximize detection of semantic drift that appears correct on a
superficial reading. Review only entries initially classified as MATCH.

Check for:

- representation traps such as `Nat` versus `Int`, zero-based versus one-based
  indices, and immutable lists versus mutable arrays;
- silent behavioral changes involving commutativity, associativity, sort order,
  or loop direction;
- theorem-strength changes in quantifier order, implicit parameters, strengthened
  premises, or conclusions weaker than the textbook;
- cost models attached to the wrong primitive operation;
- names that suggest a textbook concept while implementing different semantics.

Each challenge must cite the textbook item's key point in at most two or three
lines, identify the Lean location, and give a concrete counterexample or precise
difference. For every MATCH entry, state which dimensions were checked and why no
discrepancy was found.
