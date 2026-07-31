# AFP B 树删除证明架构调研（Niels Mündler）——2026-07-27 历史快照

> **时间定位。** 本文记录的是 2026-07-27 当日的调查。文中的旧 blocker
> 数量和“攻坚顺序”只描述当时状态；Chapter 18 现已达到 **134/134**。保留这份
> AFP 对照是为了说明架构来源与证明工程脉络，而不是列出当前 backlog。

调研对象：Isabelle/HOL 的 AFP 条目 **A Verified Imperative Implementation of
B-Trees**。AFP 官方条目元数据列出的作者是 **Niels Mündler**，entry date 是
**2021-02-24**。

- 条目页：https://isa-afp.org/entries/BTree.html
- 函数式核心理论：
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree.html
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree_Set.html
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree_Height.html

调研动机：在 2026-07-27 的快照中，Ch18.3 `composedDelete` 良构性已是全项目
持续时间最长的攻坚之一（约 30 天；相关历史案例见
[`stuck-points-retrospective-2026-07-24.md`](../proof-patterns/stuck-points-retrospective-2026-07-24.md)），
当时剩余约 11 个 `sorry`，集中在 `mergeNodes_childBounded`、key-bound transfer
和非根叶子 Occupancy。本文档保留 AFP 侧的证明架构、关键技巧，以及到
CLRS-Lean 的历史映射；最终实现结果回填在 §5。

---

## 1. 架构总览

### 1.1 Datatype 与表示差异

```isabelle
datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"
```

键和子树**交错存储**：`Node ts t` 中 `ts` 是 `(子树, 分隔键)` 对的列表，`t` 是最右子树；
`Leaf` 是空树。CLRS-Lean 的表示是 `node (keys : List Nat) (children : List BTree)`
（keys/children 平行列表，空 children 即叶子）。结构不同；下表比较的是相近的
证明责任，不把两边的谓词视为同一个逻辑断言：

| AFP | CLRS-Lean | 差异 |
|---|---|---|
| `bal t`（所有子树同高 + 递归 bal） | `SameDepth` + `heightOf` | 都承担等叶深与高度相关责任，编码接口不同 |
| `order k t`（非根 `k ≤ len ts ≤ 2k`）/ `root_order k` | `Occupancy t isRoot` | 占用率区间近似；pair 数对应 key 数，但根接口和递归组织不同 |
| `sorted_less (inorder t)`（全局 inorder 有序） | `Sorted + ChildBounded` | 共同承担节点内排序与跨子树顺序责任；AFP 的 `del_inorder` 另给出精确 inorder 等式 |

### 1.2 删除函数分解（后修复式，非 CLRS 预修复式）

```
delete k x t = reduce_root (del k x t)
```

- `del k x`：递归下降；命中分隔键时若左子是 `Leaf` 直接摘掉该 pair，否则用
  `split_max`（取左子树最大键替换分隔键，而非 CLRS 的前驱/合并子树）；返回后用
  `rebalance_middle_tree` / `rebalance_last_tree` 重组装。
- `rebalance_middle_tree k ls sub sep rs t`：**统一构造函数**，吸收"sub 可能欠满"
  的情况——sub 与兄弟都 ≥ k 个 pair 则直接装回；否则整体合并后交给 `nodeᵢ`。
- `nodeᵢ`：**与插入共用的规范化构造器**，`len ≤ 2k` 则直接构造，否则对半劈开返回
  `Upᵢ l a r`。删除侧复用插入的 split 逻辑与全套已证引理——全架构最省力的设计。
- `split_max k`：沿最右 spine 摘下最大键，返回（修复后的树, 最大键）。
- `reduce_root`：根若 0 个 pair 则塌缩为唯一子树——**高度降一只发生在这里**，
  `del` 本身高度不变（`del_height: height (del k x t) = height t`）。
- 中间态不变量 `almost_order k`：**只保留上界 `len ≤ 2k` + 子树 `order`，放弃下界**。
  欠满只在 `rebalance_*` 处被合并修复。

终止性：Isabelle `fun` 自动终止，靠一条 `[termination_simp]`：
`split ts y = (ls,(sub,sep)#rs) ⟹ size sub < size (Node ts …)`。
CLRS-Lean 则使用 `termination_by heightOf` + `heightOf_mem_lt`。两边共享
“递归参数严格下降”的证明形态，但使用的度量与生成机制并不相同。

### 1.3 定理分解

每个函数 × 每个不变量各一条引理，归纳全部用**函数自身的归纳原理**
`induction k x t rule: del.induct`：

- `nodeᵢ`：`_height`（高度不变）、`_bal`、`_order`（前提 `len ≤ 4k+1`）、
  `_inorder`（**inorder 精确相等**）
- `rebalance_middle_tree`：`_height` / `_bal` / `_order`（+ `_last_order`）/ `_inorder`
- `split_max`：`_height` / `_bal` / `_order` / `_inorder`，都需辅助谓词
  `nonempty_lasttreebal`（spine 上每层 ts 非空且末子树同高），由
  `order_bal_nonempty_lasttreebal` 从 order+bal 推出
- `del`：`del_height` / `del_bal` / `del_order`（结论 `almost_order`）/ `del_inorder`
- `delete`：`delete_order` / `delete_bal` / `delete_inorder`，经
  `reduce_root_order/bal/inorder` 三条一行小引理封口

---

## 2. 四个核心技巧

### 技巧 A：欠满用"弱化不变量"建模，下界在合并处恢复

```isabelle
fun almost_order where
  "almost_order k Leaf = True" |
  "almost_order k (Node ts t) =
    (length ts ≤ 2*k ∧ (∀s ∈ set (subtrees ts). order k s) ∧ order k t)"
```

`del_order` 的结论就是 `almost_order`——归纳过程中**从不需要在中间节点证下界**。
下界只在 `rebalance_middle_tree_order` 里恢复：不合并分支前提 `length mts ≥ k`，
合并分支交给 `nodeᵢ_order`。
这与 CLRS-Lean 红黑树删除的 Okasaki 模式（S8，NoRedRed2 + baldL/baldR）
共享“中间态弱化、修复点恢复”的局部证明形态；具体谓词和算法分支并非同构。

### 技巧 B：merge 后键数界 = 纯长度算术 + 构造器吸收溢出

```isabelle
lemma nodeᵢ_order:
  assumes "length ts ≥ k" "length ts ≤ 4*k+1"
    and "∀x ∈ set (subtrees ts). order k x" "order k t"
  shows "order_upᵢ k (nodeᵢ k ts t)"
```

证明就是 cases `length ts ≤ 2*k`：是则直接 `order`；否则 `split_half` 后两边各
`≥ k ∧ ≤ 2k`（由 `4k+1` 上界做算术）。**键的内容完全不参与**——order 只数长度。
CLRS-Lean 的 merge 情形更简单：合并两个 `t-1` 键节点得 `2t-1`，根本不溢出。

### 技巧 C：内容正确性靠 inorder 等式而非子集推理

```isabelle
lemma nodeᵢ_inorder: "inorder_upᵢ (nodeᵢ k ts t) = inorder (Node ts t)"
lemma rebalance_middle_tree_inorder:
  assumes "height t = height sub" (…)
  shows "inorder (rebalance_middle_tree k ls sub sep rs t)
       = inorder (Node (ls@(sub,sep)#rs) t)"
```

重平衡**逐字保持 inorder**（证明 `cases sub; cases t` 后基本自动）。于是
`del_inorder` 只需对列表层的 `del_list_split` 等引理做重写，
**全程没有"结果键 ⊆ 原键"式的子集引理**。

### 技巧 D：bal 的替换引理族

`bal_substitute` / `bal_substitute_subtree` / `bal_substitute_separator` /
`bal_split_last/left/right`——"换一个同高 bal 子树/换一个分隔键，bal 保持"，
各自是 2–5 行小引理，`del_bal` 靠它们组装。
CLRS-Lean 当时已有相近基础引理（`sameDepth_keys_irrel` /
`sameDepth_of_uniform`），但在 2026-07-27 的快照中尚缺“换 child 保持
SameDepth”的直接替换接口。

---

## 3. 到 CLRS-Lean 的映射

### 3.1 排序责任的逻辑边界：全局 inorder 与局部分解

AFP 的全局 `sorted_less (inorder tree)` 与本项目 `Sorted + ChildBounded`
共同承担的排序责任相对应。AFP 没有单独命名的逐子树 `ChildBounded` 谓词，
但这不表示 AFP 省略了跨子树顺序义务，也不支持“CLRS-Lean 的不变量严格更强”
这一结论。

区别在于证明接口：CLRS-Lean 把节点内 `Sorted` 与逐 child 区间界
`ChildBounded` 分开保持，AFP 则在全局 inorder 序列上表达有序性，并用
`del_inorder` 的精确等式贯穿删除证明。2026-07-27 当时列出的两个实现选项是：

- **选项 1（推荐，改动小）**：保留 `ChildBounded`，但按技巧 C 的思路先证成员资格刻画引理：

  ```lean
  k ∈ keysOf (mergeNodes l sep r) ↔ k ∈ keysOf l ∨ k = sep ∨ k ∈ keysOf r
  ```

  纯 List 成员性展开（`keysOf` 是 `keys ++ flatMap keysOf`，merge 后
  `lKeys ++ sep :: rKeys ++ (lCh ++ rCh).flatMap keysOf`，用 `List.mem_append`、
  `List.mem_flatMap` 即可，预计 < 30 行）。有了它，`mergeNodes_childBounded` 的每个
  child 界直接由前提和两边的 `ChildBounded` 析取拼出；证明分解与已证的
  `mergeNodes_sorted` 相近。
- **选项 2（大改，对齐 AFP）**：把 `Sorted` + `ChildBounded` 换成单一全局不变量
  `SortedInorder t := List.Sorted (· ≤ ·) (keysOf 的 inorder 版本)`，删除正确性直接证
  `keysOf (composedDelete …) = del_list 风格的等式`。消灭所有 key-bound transfer，
  但要重写 Ch18 全部已有引理，不建议在收口阶段做。

### 3.2 2026-07-27 当时的逐条映射表

| CLRS-Lean 当时的 `sorry` / 卡壳 | AFP 对应 | 当时拟借鉴的技巧 |
|---|---|---|
| `mergeNodes_childBounded` | `nodeᵢ_order` + `bal_list_merge` | 键数部分用长度算术（技巧 B）；child 区间界用 §3.1 的局部成员分解 |
| `keysOf_composedDelete_subset` | AFP 以更强的 `del_inorder` 等式提供相关内容语义 | 复用递归骨架 + merge 成员刻画引理 |
| `composedDelete_key_bound_lo` / `_hi` | `del_inorder` 的全局序列语义承担对应顺序责任 | 从 key subset 推导局部上下界 |
| 四个 merge 分支中的证明洞 | `del` 的命中分支（AFP 用 `split_max` + rebalance） | 用 `mergeNodes_*` 保持引理 + IH |
| 非根叶子 `Occupancy t false` | `del_order` 的 Leaf 基例 + `almost_order` | 见 §3.4；当时判断需要补预修复守卫 |

### 3.3 当时规划的 key subset 与局部边界证明

- `keysOf_composedDelete_subset`：当时计划让强归纳复用
  `composedDelete_childBounded`
  的骨架，三处新东西：(1) merge 分支用 §3.1 的成员刻画引理 + IH；(2) 直接递归分支用
  `List.mem_or_eq_of_mem_set`；(3) 叶子分支用 `mem_of_sortedRemove`。
- `composedDelete_key_bound_lo`（及对称的 hi 版）：当时规划为 subset 的短推论
  （`intro k' hk'; exact hlo k' (keysOf_composedDelete_subset … hk')`）。
  目标是让多处局部上下界证明统一从内容包含关系导出。

### 3.4 当时判断的非根叶子 Occupancy 障碍

2026-07-27 当时，删除后叶子可能只剩 `t-2` 个键，而当时版本的
`composedDelete` 尚无对应修复逻辑；因此该版本下的目标不可由既有前提推出。
当时从 AFP 架构对照中整理出两条路：

- **路 A（AFP 路线，后修复式）**：引入 `AlmostOccupancy`（去掉下界，只留 `≤ 2t-1`
  上界 + 递归），归纳证 `composedDelete` 保持 `AlmostOccupancy`，再另写 `rebalance`
  恢复下界——即把算法改成后修复式，改动大。
- **路 B（CLRS 预修复路线，推荐）**：递归进 child 前加守卫：若目标 child 只有 `t-1`
  键，先 `rotateRight`（当时已有 `rotateRight_preserves`）或补 `rotateLeft` + merge
  使其 ≥ t 键再递归。这样 IH 直接在满足下界的 child 上用，叶子基例 `t-2` 的情况被
  守卫排除。当时文件头注释已规划这一方向，缺口是 `rotateLeft` 及其保持引理。

最终实现采用了 CLRS 预修复路线；§5 记录已完成的 rotation repair 和重组结果。

### 3.5 工程性建议：切换到函数自身的归纳原理

AFP 所有 del 定理都用 `induction k x t rule: del.induct`——函数自身的归纳原理，
case 自动对齐函数分支。在 2026-07-27 的 CLRS-Lean 快照中，四个
`composedDelete_*` 组件引理曾手工搭了四遍 `Nat.strongRecOn` + motive，
同一份分支展开样板抄了 4 遍，当时每一遍都留有 merge 证明洞。
Lean 4 对 `termination_by` 定义的函数自动生成 `composedDelete.induct`，
`induction tr using composedDelete.induct` 可得到按分支组织的 IH（包括 merge 分支
对 merged 节点的 IH）。这一建议后来落实为围绕 `NodeWF` 的 bundled induction，
见 §5。

### 3.6 2026-07-27 当时建议的攻坚顺序

当时拟按以下依赖顺序推进：

1. `mem_keysOf_mergeNodes`（成员刻画，纯 List）→
2. `mergeNodes_childBounded`（参照 `mergeNodes_sorted` 的分解）→
3. `keysOf_composedDelete_subset`（既有骨架 + 成员刻画）→
4. `composedDelete_key_bound_lo` / `_hi`（subset 推论）→
5. 四个 merge 分支（用前述 merge 保持引理 + IH）→
6. `rotateLeft` + 预修复守卫 → 非根叶子 Occupancy。

当时估计前四步无需算法改动、第五步依赖前两步、第六步需要修改
`composedDelete`。这份顺序现在只是历史执行记录，不是未完成事项列表。

---

## 4. 备注与诚实声明

- 本文档的 AFP 技巧描述基于 2026-07-27 对理论源码的远程阅读；CLRS-Lean
  一侧现以模块名和定理名定位，不再保留易失效的源码行号。
- AFP 的删除是**后修复式 + split_max**，CLRS-Lean 刻意走 CLRS 教科书的预修复
  （下降前借/合并）路线以保持 textbook-faithful，因此不能整体照搬其算法结构；
  可迁移的是**证明组织方式**（技巧 A–D、归纳原理、inorder 等式思想），而非函数定义。
- 文中的工作量估算和“缺口”判断都属于 2026-07-27 快照；判断其后续是否落实，
  应以 §5 的实现结果和当前 Chapter 18 章节说明为准。

---

## 5. 后续实现结果（截至 2026-07-31）

| 2026-07-27 的问题面 | 后续落地结果 |
|---|---|
| merge 内容与边界 | `mem_keysOf_mergeNodes` 给出精确成员分解；`mergeNodes_childBounded`、`mergeNodes_nodeWF` 与 `spliceMerged_packet` 等 merge child-bounded / parent reassembly 引理完成局部保持和父节点重组。 |
| rotation 排序修复 | `rotateLeft` / `rotateRight` 的 `Sorted`、`ChildBounded`、`NodeWF` 与 repaired-`DeleteReady` 结果均已建立，并由 `rotateLeft_reassembly_packet` / `rotateRight_reassembly_packet` 完成递归结果重组。 |
| bundled 递归不变量 | `NodeWF` 打包 `Sorted`、`ChildBounded`、`Occupancy`、`SameDepth`；`composedDelete_packet` 在一次递归证明中同时交付 key subset、结构结果与原始高度保持。 |
| 归纳与函数分支对齐 | 核心递归证明使用 Lean 为函数生成的 `composedDelete.induct`，IH 与 predecessor、successor、merge、rotation 和直接下降分支对齐。 |
| 精确删除 | `composedDelete_keyBag` 证明 `keyBag (composedDelete t x tr) = (keyBag tr).erase x`，即恰好删除请求键的一个出现，而不只是证明结果键是输入键的子集。 |
| 高度 | `composedDelete_sameDepth_height` 给出 same-depth 与 raw height 保持；`composedDeleteRoot_height` 证明根规范化后的高度不变或恰好减少一层。 |

这些结果随后与搜索、插入以及最小键数/对数高度界一起把 Chapter 18 推进到
**134/134**。当前功能式 B 树模型中，**没有剩余的 Chapter 18 核心证明项**。
