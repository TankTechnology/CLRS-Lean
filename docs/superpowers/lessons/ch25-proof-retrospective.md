# Ch25 Proof Retrospective — Mistakes & Lessons

This document captures the key mistakes and successful patterns from the
Ch25.2 (Floyd-Warshall) and Ch25.3 (Johnson reweighting) proof efforts.
It is meant as a reference for future agents working on CLRS-Lean proofs.

## Mistakes

### 1. `rw` fails on hypotheses with implicit vs explicit coercions

**Problem**: `rw [hd_eq] at h_lower` where `hd_eq : d = (d' : WithTop ℝ)` and
`h_lower : d ≤ walkWeight G.w p`. The `walkWeight G.w p` uses an **implicit**
coercion (ℝ → WithTop ℝ via `≤`), while `hd_eq` uses an **explicit** coercion
(`(d' : WithTop ℝ)`). `rw` operates on syntactic equality and cannot match
across these different coercion forms.

**Symptom**: `Tactic rewrite failed: Did not find an occurrence of the pattern`.

**Fix**: Use `simpa [hd_eq] using h_lower` to create a new hypothesis with the
rewritten type, or use `have h_lower' : ... := by simpa [hd_eq] using h_lower`.

### 2. `let` bindings make type inference opaque

**Problem**: Using `let h_u := (h u : WithTop ℝ)` to abbreviate a term. The
`let` definition is NOT unfolded by `dsimp` or during typeclass search. This
breaks `simp`, `rw`, and `apply` when they need to match against `h_u - h_v`.

**Symptom**: `dsimp made no progress` on `dsimp [h_u, h_v]`.

**Fix**: Either:
- Use `(h u : WithTop ℝ)` directly everywhere (no `let`), OR
- Use `set h_u := (h u : WithTop ℝ) with hh_u` and `rw [hh_u]` to unfold, OR
- Use `simpa [h_u, h_v]` to rewrite in each usage.

### 3. `le_antisymm` unavailable as a function

**Problem**: `le_antisymm (le_top _) h_lower` gives `Function expected at`.
This lemma cannot be used as a function/term in this Mathlib version.

**Fix**: Instead of `le_antisymm`, use one of:
- `.antisymm` method: `(le_top _).antisymm h_lower` (if available)
- `simpa using h_lower` when the goal is `w = ⊤` and `h_lower : ⊤ ≤ w`
- Case analysis: `by_cases hw : w = ⊤`

### 4. `subst` fails on `Option.ne_none_iff_exists'` results

**Problem**: `rcases Option.ne_none_iff_exists'.mp ha with ⟨a', rfl⟩` uses
`rfl` pattern matching which internally calls `subst`. `subst` fails on
`WithTop ℝ = Option ℝ` equations.

**Symptom**: `Tactic subst failed: invalid equality proof`.

**Fix**: Use explicit `rw` instead: `rcases ... with ⟨a', ha_eq⟩; rw [ha_eq]`.

### 5. `add_le_add_right` missing for `WithTop ℝ`

**Problem**: `add_le_add_right h_lower c` fails because the
`AddRightMono (WithTop ℝ)` typeclass instance is missing in Mathlib v4.32.0-rc1.

**Symptom**: `Application type mismatch: The argument`.

**Fix**: Use `gcongr; exact h_lower` — `gcongr` bypasses the typeclass by using
a generalized congruence tactic that works on the goal structure directly.

### 6. Using the wrong `h_lower` — function vs applied

**Problem**: `gcongr; exact h_lower` failed because `h_lower : ∀ p, ...` (a
function from `IsShortestDist`) rather than `h_lower p hp` (applied to a
specific walk `p`). The `gcongr` reduces `d + c ≤ w + c` to `d ≤ w`, which
matches `h_lower p hp` but NOT the function `h_lower`.

**Fix**: `gcongr; exact h_lower p hp`.

### 7. Over-investing in case analysis when `gcongr` suffices

**Problem**: Spent hours writing 30-line case analyses (⊤/finite/ℝ-lifting)
for `d + c ≤ w + c` from `d ≤ w` in `WithTop ℝ`. The entire proof is one line.

**Fix**: Try `gcongr` FIRST before writing manual case analysis for `WithTop`
inequalities. `gcongr` handles the `+` congruence, `⊤` cases, and
coercion lifting automatically.

## Successful Patterns

### 1. `Through` predicate for walk-splitting (Floyd-Warshall)

Defined `Through (S : Finset V) (i j : V) (p : List V) := ∀ v ∈ p, v = i ∨ v = j ∨ v ∈ S`.
This cleanly captures "all intermediate vertices are in S" and makes the
induction hypotheses easy to state and apply.

### 2. `List.Nodup` disjointness via `List.nodup_append`

When splitting a Nodup walk `p = l₁ ++ k :: l₂`:
```lean
have hNodup_app := (List.nodup_append.mp hNodup)
-- gives: l₁.Nodup ∧ (k::l₂).Nodup ∧ ∀ a ∈ l₁, ∀ b ∈ k::l₂, a ≠ b
```
The disjointness `∀ a ∈ l₁, ∀ b ∈ k::l₂, a ≠ b` is exactly what's needed
to prove sub-walk interior vertices don't contain endpoints.

### 3. Pattern matching on `WithTop ℝ = Option ℝ`

For lemmas like `add_sub_assoc` where `b ≠ ⊤` and `c ≠ ⊤`:
```lean
have ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hb
have ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hc
rw [hb', hc']  -- now b = some b', c = some c'
```
This converts `WithTop ℝ` values to `ℝ` for arithmetic reasoning.

### 4. `calc` + `simp` for coercion distribution

Lifting ℝ equalities to `WithTop ℝ`:
```lean
calc
  (a' : WithTop ℝ) + (b' : WithTop ℝ) = ((a' + b' : ℝ) : WithTop ℝ) := by simp
  _ = ((a' + (b' - c') : ℝ) : WithTop ℝ) := by rw [hℝ]
  _ = (a' : WithTop ℝ) + ((b' : WithTop ℝ) - (c' : WithTop ℝ)) := by simp
```
Each `simp` step handles one direction of `WithTop.coe_add` / `WithTop.coe_sub`.

### 5. `gcongr` for `WithTop` inequality monotonicity

When you need `a + c ≤ b + c` from `a ≤ b` and `add_le_add_right` is
unavailable, use `gcongr`.

### 6. `revert` + `induction` + `intro` for complex inductions

For inductions where the IH must apply to DIFFERENT `i`, `j`, `p`:
```lean
revert i j p hp_walk hNodup hp_through
induction ks with
| nil => intro i j p ...; ...
| cons k ks ih => intro i j p ...; ... (ih works for any i j p)
```
This avoids `generalizing` syntax issues.

### 7. `IsWalkFrom_reweighted_iff` via `h_adj_eq`

For proving walks are equivalent in two graphs with same edge sets:
```lean
have h_adj_eq : (G.reweightedGraph h).Adj = G.Adj := by
  ext x y; simp [WeightedGraph.Adj, edges_reweightedGraph]
-- Then deconstruct/reconstruct IsWalkFrom using h_adj_eq
```

### 8. Isolating problems into minimal standalone tests

When a lemma works in one context but not another, create a minimal test
file that replicates the EXACT conditions (imports, namespace, variable
bindings). This was critical for diagnosing the `WithTop` coercion issues.

### 9. `exact_mod_cast` and `mod_cast` for ℝ ↔ WithTop ℝ

- `exact_mod_cast h` — lifts `h : a ≤ b` in ℝ to `(a : WithTop ℝ) ≤ (b : WithTop ℝ)`
- `exact_mod_cast h` — also works for equalities
- NOTE: only works when the goal uses explicit coercions `(x : WithTop ℝ)`,
  not implicit ones

## Recommendations for Future Proofs

1. **Try `gcongr` first** for any `a + c ≤ b + c` goal.
2. **Avoid `let`** — use `(h u : WithTop ℝ)` directly.
3. **Avoid `rw` on hypotheses with mixed coercions** — use `simpa` instead.
4. **Use `Option.ne_none_iff_exists'`** to extract ℝ values from `WithTop ℝ`.
5. **Use `calc` with `simp` steps** for coercion distribution.
6. **Test minimal repros** when a lemma doesn't type-check.
7. **Check `.mp` vs `.mpr`** — if one direction doesn't work, the typeclass
   for the other direction might be missing. Use alternative approaches.
