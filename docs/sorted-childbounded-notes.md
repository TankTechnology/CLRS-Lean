# Sorted + ChildBounded 攻坚笔记

## 当前状态

文件: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`

| 定理 | Sorries |
|------|---------|
| `splitChild_preserves_sameDepth` | 0 ✅ |
| `splitChild_preserves_occupancy` | 0 ✅ |
| `splitChild_preserves_sorted` | 1 (line ~808) |
| `splitChild_preserves_childBounded` | 1 (line ~826) |

## 已完成的基础设施

### `pairwise_get_mono` 引理 (0 sorries, line ~710)

```lean
lemma pairwise_get_mono {l : List Nat} (hp : List.Pairwise (· ≤ ·) l) {j k : Nat}
    (hjk : j ≤ k) (hj : j < l.length) (hk : k < l.length) : l.get ⟨j, hj⟩ ≤ l.get ⟨k, hk⟩
```

这个引理说: 如果 Nat 列表是 pairwise ≤ 的, 则元素是索引单调的. 证明只需 18 行, 通过对 `k` 做归纳.

### 其他辅助引理 (全部 0 sorries)
- `occupancy_of_child`, `child_children_len_of_full_cb`, `splitAt_first/second_half_length`
- `heightOf_uniform_children`, `heightOf_split_parts_eq`
- `sameDepth_take`, `sameDepth_drop`, `sameDepth_children_eq_height`

## 两个 sorries 的精确位置和内容

### 1. Sorted (line ~808): keys pairwise

```lean
-- 需要填充的块在 line ~808:
have h_keys_ok : List.Pairwise (· ≤ ·) (take i keys ++ medianKey :: drop i keys) := by
  sorry
```

**要证明**: 在 `keys` 中插入 `medianKey` 后, 列表仍然是 pairwise ≤ 的.

**证明路径**:
1. 从 ChildBounded 提取两个边界不等式:
   - `keys[i-1] ≤ medianKey` (当 `i > 0`)
   - `medianKey ≤ keys[i]` (当 `i < keys.length`)
2. 用 `pairwise_get_mono` 将这两个点边界升级为全称条件:
   - `∀ a ∈ take i keys, a ≤ medianKey`
   - `medianKey ≤ ∀ b ∈ drop i keys`
3. 用 `List.pairwise_append` 装配最终结果

**剩余的战术障碍** (各需约 5 行):

**(a)** 从 ChildBounded 提取 `keys[i-1] ≤ medianKey`:
ChildBounded 用 `match keys[i-1]? with ...` 表示边界. 需要用 `simp [hi_sub_bound]` 展开 match, 其中 `hi_sub_bound : i-1 < keys.length`.

**(b)** 从 ChildBounded 提取 `medianKey ≤ keys[i]`: 同上.

**(c)** `a ∈ take i keys` → `∃ j < i, keys[j] = a`:
用 `List.mem_iff_get` 作用于 `take i keys` 本身 (而非 `keys`), 得到 `j < (take i keys).length`.
由于 `(take i l).length = min i l.length ≤ i`, 有 `j < i`.
再用 `(take i keys).get j = keys.get j` (by `simp`) 得到 `keys[j] = a`.

**(d)** `b ∈ drop i keys` → `∃ k, i ≤ k ∧ keys[k] = b`:
用 `List.mem_iff_get` 作用于 `drop i keys`, 得到 `k < (drop i keys).length`.
`(drop i keys).get k = keys.get (i + k)` (by `simp`), 原始索引是 `i + k ≥ i`.

### 2. ChildBounded (line ~826): 整个定理

```lean
theorem splitChild_preserves_childBounded ... := by
  sorry
```

**要证明** ChildBounded 的三个 conjunct 在 split 后保持.

**证明路径**:
1. **Count relation**: `simp` 即可 (`newChildren.length = newKeys.length + 1`)
2. **Recursive ChildBounded**: 与 occupancy sub-node 证明相同的 `.mp` + `.subset` 模式
3. **Key-range bounds**: 同样用 `pairwise_get_mono` + ChildBounded 边界

**剩余障碍**: key-range bounds 部分需要与 Sorted 相同的 `List.get?` match 展开和 take/drop 成员-索引转换.

## 推荐的新 session 工作顺序

1. **写 `List.get?` match 展开的 helper lemma** (5 min):
   ```lean
   lemma get?_eq_some_of_lt {l : List α} {i : Nat} (h : i < l.length) : l[i]? = some (l.get ⟨i, h⟩) := by
     simp [h]
   ```
   然后用它展开 ChildBounded 的 match.

2. **完成 Sorted keys pairwise** (15 min):
   - 按上述路径 (a)→(d) 填充 `h_keys_ok` 的 `sorry`
   - 预计最终代码约 60 行

3. **完成 ChildBounded** (20 min):
   - 仿照 occupancy 的 sub-node 证明写 count relation 和 recursive 部分
   - key-range bounds 复用步骤 2 中的技巧
   - 预计最终代码约 50 行

## 关键引理速查

`List.pairwise_append` 的签名:
```lean
List.pairwise_append : List.Pairwise R (l₁ ++ l₂) ↔
  List.Pairwise R l₁ ∧ List.Pairwise R l₂ ∧ (∀ a ∈ l₁, ∀ b ∈ l₂, R a b)
```

`List.mem_iff_get` 的用法:
```lean
-- 对 take i keys 用, 直接得到 j < i:
rcases List.mem_iff_get.mp ha with ⟨j, hj_take, rfl⟩
-- hj_take : j < (take i keys).length
-- 且有 (take i keys).get ⟨j, hj_take⟩ = keys.get ⟨j, hj_len⟩ (by simp)
```

ChildBounded 的 match 展开模式:
```lean
unfold ChildBounded at h_cb; rcases h_cb with ⟨_, h_cb_bounds, _⟩
rcases h_cb_bounds i h_lt with ⟨h_lo, h_hi⟩
-- h_lo : (i = 0 ∨ match keys[i-1]? with | some lo => ∀ k ∈ keysOf child, lo ≤ k | none => True)
-- h_hi : match keys[i]? with | some hi => ∀ k ∈ keysOf child, k ≤ hi | none => True
```

## 已提交的 commit

```
77eb8a1 feat(ch18.1): complete Sorted children subproof, occupancy 0 sorries
7790c7f feat(ch18.1): prove splitChild_preserves_occupancy (0 sorries)
250cec5 feat(ch18.1): add pairwise_get_mono lemma (0 sorries)
bac3160 feat(ch18.1): add documented stubs for occupancy, sorted, childBounded
5488c9e feat(ch18.1): prove splitChild_preserves_sameDepth, add occupancy stub
```
