# Sorted + ChildBounded Battle Notes

## Current status (all complete ✅)

File: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`

| Theorem | Sorries |
|------|---------|
| `splitChild_preserves_sameDepth` | 0 ✅ |
| `splitChild_preserves_occupancy` | 0 ✅ |
| `splitChild_preserves_sorted` | 0 ✅ |
| `splitChild_preserves_childBounded` | 0 ✅ |

`#print axioms splitChild_preserves_childBounded` →
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Final proof structure of ChildBounded

Key lemmas (all stated before the main theorem):

- `keysOf_node_subset {ks ks' cs cs'} (hk : ks ⊆ ks') (hc : cs ⊆ cs')`:
  `keysOf (node ks cs) ⊆ keysOf (node ks' cs')` (the subset lemma suggested by the user).
- `childBounded_node_nil`: a node without children is trivially ChildBounded.
- `keysOf_take_le_pivot` / `keysOf_drop_ge_pivot`: the median key sandwiches the left and right halves
  (this is the sortedness part that needs `Sorted`/`Pairwise`, combined with the children's own ChildBounded bounds).
- `childBounded_take_of_full` / `childBounded_drop_of_full`: ChildBounded is preserved when
  taking the prefix/suffix of a full node.

The main theorem has three conjuncts:
1. **count**: `simp [length_*]; omega`.
2. **parent bounds**: do a four-case analysis on the child index `j` (`j<i`, `j=i`, `j=i+1`,
   `j≥i+2`). In each case compute `newChildren.get ⟨j⟩` with `getElem_append_left/right`,
   and compute `newKeys[·]?` with `hNK_lt/eq/gt`. For `j=i` (left) use `keysOf_take_le_pivot`,
   and for `j=i+1` (right) use `keysOf_drop_ge_pivot`; for the two subset cases, use
   `keysOf_node_subset` + `revert h; cases keys[·]?` to carry the bounds along the option.
3. **recursive**: split via `mem_append` + `take/drop_subset`; the new left/right children use
   `childBounded_take/drop_of_full`.

## Pitfalls encountered (for future session reference)

- **`rw [List.length_take] at h` when `h` mentions the Fin variable `n`** → "motive is not type
  correct". Instead use `Nat.lt_of_lt_of_le n.isLt (List.length_take_le ..)` or do
  `rw [← List.length_drop]` on the **goal** (rather than the hyp).
- **`rw [h_A_len]` / index rewriting inside the `getElem` subscript** → motive error. Instead use
  `simp only [...]` (simp automatically handles the proof in the getElem subscript).
- **Inlining `(by rw [...]; omega)` as the subscript proof for `getElem_append_left`** →
  `as` is a metavar, so the pattern cannot be found. Instead, first `have hlt_AB : j < (...).length := ...`
  and pass it in (a concrete type eliminates the metavar).
- **`simp only [append_assoc, cons_append]` cannot reassociate inside `.get ⟨j, hj⟩`**
  (hj depends on length), leaving the original `++ [nl,nr] ++` form; instead, apply nested
  `getElem_append` directly to the original double-append form.
- **Auxiliary `match_*_of_subset` lemmas**: `exact` fails to typecheck because the matcher becomes
  dependent (`match o, h with ...`); instead, inline `revert h; cases o` in the main proof.

## Completed infrastructure

### The `pairwise_get_mono` lemma (0 sorries)

```lean
lemma pairwise_get_mono {l : List Nat} (hp : List.Pairwise (· ≤ ·) l) {j k : Nat}
    (hjk : j ≤ k) (hj : j < l.length) (hk : k < l.length) : l.get ⟨j, hj⟩ ≤ l.get ⟨k, hk⟩
```

### Other auxiliary lemmas (all 0 sorries)
- `occupancy_of_child`, `child_children_len_of_full_cb`, `splitAt_first/second_half_length`
- `heightOf_uniform_children`, `heightOf_split_parts_eq`
- `sameDepth_take`, `sameDepth_drop`, `sameDepth_children_eq_height`

## Key lemmas quick reference

The signature of `List.pairwise_append`:
```lean
List.pairwise_append : List.Pairwise R (l₁ ++ l₂) ↔
  List.Pairwise R l₁ ∧ List.Pairwise R l₂ ∧ (∀ a ∈ l₁, ∀ b ∈ l₂, R a b)
```

The match unfolding pattern for ChildBounded:
```lean
unfold ChildBounded at h_cb; rcases h_cb with ⟨_, h_cb_bounds, _⟩
rcases h_cb_bounds i h_lt with ⟨h_lo, h_hi⟩
```
