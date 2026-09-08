import Mathlib

/-!
# Section 14.3 — Elements of dynamic programming

This section defines cache-value consistency and a finite set-cardinality
inequality. Neither property alone proves that an algorithm computes a state
only once.

The {lit}`Execution` companion supplies a separate executable guarantee:
{lit}`DPExecution.buildLayers` appends stored rows in dependency order. Its
invariant lifts any cell property whose premises concern earlier rows. Actual
cell-write and candidate counters are accumulated during filling. Matrix-chain
and optimal-BST executions instantiate this builder with their own stored cells
and recurrence proofs; those are the concrete once-per-state clients.

The historical {lit}`distinctCacheStates_le_length` remains a cardinality fact,
not an execution or cache-miss bound. {lit}`MemoCacheConsistent` describes value
correctness only; its use does not silently assume memoized runtime.

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
cache-value invariant. Execution and cache-miss bounds require separate proofs.
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

/-! ## Cardinality of the cached states -/

/--
The number of distinct states with a stored value among the supplied list.
This definition inspects a completed cache; it says nothing about how often
those states were evaluated while constructing that cache.
-/
def distinctCacheStates {State : Type} [DecidableEq State]
    (cache : State → Option Value) (states : List State) : Nat :=
  ((states.filter (fun s => (cache s).isSome)).toFinset).card

/--
The distinct cached-state count is at most the supplied list length.
This elementary cardinality inequality does not establish any once-per-state
execution guarantee.
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
