# Chapter 25 costed bipartite-flow implementation plan

1. Add a failing interface test naming the cost-model, run, refinement, and
   final `O(VE)` theorem.
2. Implement graph/network counts and prove the per-attempt linear budget.
3. Implement the BFS-selected augmentation step and prove no-path stability,
   integrality, and value progress.
4. Implement the costed fixed-fuel run; prove erasure to the flow iteration,
   exact accumulated work, and no augmenting path after `|G.L|` attempts.
5. Recover a matching at every state; prove active-step size progress and a
   maximum final matching with the total work bound.
6. Export the facade, update the section/root documentation and progress
   ledgers, then run focused builds, trust checks, and repository audits.
7. Commit and push each independently verifiable stage; close issue #339 only
   after all acceptance checks pass.
