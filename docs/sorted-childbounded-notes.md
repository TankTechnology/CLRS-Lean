# Sorted + ChildBounded 攻坚笔记

## 当前状态 (已全部完成 ✅)

文件: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`

| 定理 | Sorries |
|------|---------|
| `splitChild_preserves_sameDepth` | 0 ✅ |
| `splitChild_preserves_occupancy` | 0 ✅ |
| `splitChild_preserves_sorted` | 0 ✅ |
| `splitChild_preserves_childBounded` | 0 ✅ |

`#print axioms splitChild_preserves_childBounded` →
`[propext, Classical.choice, Quot.sound]`（无 `sorryAx`）。

## ChildBounded 的最终证明结构

关键引理（都在主定理之前）：

- `keysOf_node_subset {ks ks' cs cs'} (hk : ks ⊆ ks') (hc : cs ⊆ cs')`:
  `keysOf (node ks cs) ⊆ keysOf (node ks' cs')`（用户建议的 subset 引理）。
- `childBounded_node_nil`: 无孩子节点平凡 ChildBounded。
- `keysOf_take_le_pivot` / `keysOf_drop_ge_pivot`: median key 夹住左右两半
  （这是需要 `Sorted`/`Pairwise` 的排序内容，配合子节点自身的 ChildBounded 边界）。
- `childBounded_take_of_full` / `childBounded_drop_of_full`: ChildBounded 在
  截取 full 节点的前缀/后缀时保持。

主定理三个 conjunct：
1. **count**: `simp [length_*]; omega`。
2. **parent bounds**: 对孩子下标 `j` 做四段 case 分析（`j<i`、`j=i`、`j=i+1`、
   `j≥i+2`）。每段用 `getElem_append_left/right` 计算 `newChildren.get ⟨j⟩`，
   用 `hNK_lt/eq/gt` 计算 `newKeys[·]?`。`j=i`（左）用 `keysOf_take_le_pivot`，
   `j=i+1`（右）用 `keysOf_drop_ge_pivot`；两侧 subset 情形用 `keysOf_node_subset`
   + `revert h; cases keys[·]?` 沿 option 搬运边界。
3. **recursive**: `mem_append` 拆分 + `take/drop_subset`，新左右孩子用
   `childBounded_take/drop_of_full`。

## 踩过的坑（供后续 session 参考）

- **`rw [List.length_take] at h` 当 `h` 提到 Fin 变量 `n`** → "motive is not type
  correct"。改用 `Nat.lt_of_lt_of_le n.isLt (List.length_take_le ..)` 或对
  **目标**（而非 hyp）做 `rw [← List.length_drop]`。
- **`rw [h_A_len]` / index 重写在 `getElem` 下标里** → motive 错误。改用
  `simp only [...]`（simp 会自动处理 getElem 下标的 proof）。
- **内联 `(by rw [...]; omega)` 作为 `getElem_append_left` 的下标证明** →
  `as` 是 metavar，pattern 找不到。改成先 `have hlt_AB : j < (...).length := ...`
  再传入（具体类型消除 metavar）。
- **`simp only [append_assoc, cons_append]` 无法在 `.get ⟨j, hj⟩` 内重结合**
  （hj 依赖 length），会留下原始 `++ [nl,nr] ++` 形式；直接对原始双 append 形式
  用嵌套 `getElem_append` 即可。
- **辅助 `match_*_of_subset` 引理**：`exact` 会因 matcher 变成 dependent
  (`match o, h with ...`) 而类型不匹配；改为在主证明里 `revert h; cases o` 内联。

## 已完成的基础设施

### `pairwise_get_mono` 引理 (0 sorries)

```lean
lemma pairwise_get_mono {l : List Nat} (hp : List.Pairwise (· ≤ ·) l) {j k : Nat}
    (hjk : j ≤ k) (hj : j < l.length) (hk : k < l.length) : l.get ⟨j, hj⟩ ≤ l.get ⟨k, hk⟩
```

### 其他辅助引理 (全部 0 sorries)
- `occupancy_of_child`, `child_children_len_of_full_cb`, `splitAt_first/second_half_length`
- `heightOf_uniform_children`, `heightOf_split_parts_eq`
- `sameDepth_take`, `sameDepth_drop`, `sameDepth_children_eq_height`

## 关键引理速查

`List.pairwise_append` 的签名:
```lean
List.pairwise_append : List.Pairwise R (l₁ ++ l₂) ↔
  List.Pairwise R l₁ ∧ List.Pairwise R l₂ ∧ (∀ a ∈ l₁, ∀ b ∈ l₂, R a b)
```

ChildBounded 的 match 展开模式:
```lean
unfold ChildBounded at h_cb; rcases h_cb with ⟨_, h_cb_bounds, _⟩
rcases h_cb_bounds i h_lt with ⟨h_lo, h_hi⟩
```

