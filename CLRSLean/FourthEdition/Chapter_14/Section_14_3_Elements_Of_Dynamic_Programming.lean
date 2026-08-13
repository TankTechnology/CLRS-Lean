import Mathlib

/-!
# Section 14.3 — Elements of dynamic programming

This section packages the reusable, algorithm-independent core of dynamic
programming: a generic memo-cache consistency invariant and a distinct-state
cost bridge.  The section examples (§14.1, §14.2, §14.4, §14.5) instantiate
these interfaces with their own optimal-substructure proofs.

Main results:

- Definition {lit}`MemoCacheConsistent`: a cache is consistent when every stored
  value agrees with the ground-truth value function.
- Definition {lit}`distinctCacheStates`: the number of distinct cached states in
  a finite list.
- Theorem {lit}`distinctCacheStates_le_length`: a pass over a list of states
  caches at most one entry per distinct state, the distinct-state cost bridge.

Status: `proved` for the generic cache invariant and the distinct-state bound.
The algorithm-specific optimal-substructure and reconstruction theorems remain
in the sibling sections.

Notation conventions used in this section:

- `State` : the type of subproblem states
- `Value` : the type of subproblem answers
- `cache` : the memoization table {lit}`State → Option Value`
-/

namespace CLRS
namespace Chapter15

/-! ## The generic memo-cache invariant -/

/--
A memoization cache is consistent when every stored value agrees with the
ground-truth value function {lit}`correct`.  This is the reusable
"cache invariant" that each dynamic-programming example discharges for its own
Bellman value function.
-/
def MemoCacheConsistent {State Value : Type} (correct : State → Value)
    (cache : State → Option Value) : Prop :=
  ∀ s v, cache s = some v → v = correct s

/-- A consistent cache that stores a value at a state agrees with the
    ground-truth value at that state. -/
theorem MemoCacheConsistent_eq {State Value : Type} {correct : State → Value}
    {cache : State → Option Value} (h : MemoCacheConsistent correct cache)
    {s : State} {v : Value} (hstore : cache s = some v) : v = correct s :=
  h s v hstore

/-! ## The distinct-state cost bridge -/

/--
The number of distinct states that a cache stores among a finite list of states.
This is the "distinct subproblem" count that bounds the work of a memoized
pass: each distinct state is computed (and cached) once, and every later
occurrence is a cache hit.
-/
def distinctCacheStates {State : Type} [DecidableEq State]
    (cache : State → Option Value) (states : List State) : Nat :=
  ((states.filter (fun s => (cache s).isSome)).toFinset).card

/--
**Distinct-state cost bridge.**  The number of distinct cached states among a
list of states is at most the list length.  Hence a memoized traversal that
computes each state at most once performs `O(#distinct states)` value
computations regardless of how many times the states recur.
-/
theorem distinctCacheStates_le_length {State : Type} [DecidableEq State]
    (cache : State → Option Value) (states : List State) :
    distinctCacheStates cache states ≤ states.length := by
  unfold distinctCacheStates
  calc
    ((states.filter (fun s => (cache s).isSome)).toFinset).card
        ≤ (states.filter (fun s => (cache s).isSome)).length :=
          List.toFinset_card_le _
    _ ≤ states.length := List.length_filter_le (fun s => (cache s).isSome) states

end Chapter15
end CLRS
