# CLRS-Lean 证明技巧、策略与计划

这份文档是项目内积累的“活页手册”。
它的作用是：把反复出现的 Lean 证明技巧、章节推进策略和当前阶段计划固定下来，避免每次从零开始讨论。

---

## 1. 当前阶段目标

**第一阶段：完成 CLRS 前 26 章的主要证明。**

已经动工的章节：2–20、23。  
尚未开始的章节：21（并查集）、22（基础图算法）、24（单源最短路）、25（全源最短路）、26（最大流）。

对于尚未开始的章节，采用“规范层 → 实现层 → 证明层”的三层打法：

1. **规范层**：先定义图的顶点/边集、路径、割、流等数学谓词。
2. **实现层**：写出可执行的算法函数（Union-Find、BFS/DFS、Dijkstra/Bellman-Ford、Floyd-Warshall、Edmonds-Karp 等）。
3. **证明层**：证明算法满足规范（连通性、最短路径、最大流 = 最小割等）。

---

## 2. 核心设计原则

### 2.1 规范与实现分离

- 用 `Prop` 谓词描述“应该满足什么”：
  - 排序：`Sorted`、`Permuted`
  - 树：`InTree`、`RedBlackShape`、`NoRedRed`、`BalancedBlackHeight`
  - 图：路径、割、流值
- 用可执行的 Lean 函数实现算法。
- 定理连接两者：`algorithm input` 满足 `Spec`。

### 2.2 不变式优先于复杂类型

不要把所有约束都压进一个 inductive type。
像 Chapter 13 的 `WeakRB` 用 `∨` 组合三种形状，比定义复杂的 indexed family 更容易证明。

### 2.3 先局部、后组合

- 把算法拆成对称的局部情况（如红黑树的 left-left / left-right / right-left / right-right）。
- 每个局部情况单独证一个小定理。
- 最后用一个 dispatcher/组合定理把它们包起来。
- **不要过早抽象**：三个相似引理就直接写三遍，等至少两个章节需要时再提取公共工具。

---

## 3. Lean 战术速查

### 3.1 日常三件套

| 战术 | 用途 | 示例 |
|---|---|---|
| `simp [a, b, c]` | 用显式引理展开/化简 | `simp [RedBlackShape, NoRedRed]` |
| `omega` | 自然数/整数不等式、高度、索引 | 高度相等、分支大小界 |
| `linarith` | 线性不等式链 | 代价上界、势能非负 |
| `rcases` | 拆 `∧`、`∨`、`∃`、积类型 | `rcases h with ⟨h1, h2⟩` |
| `cases t` / `cases c` | 对树/颜色等归纳类型分情况 | `cases c with \| black \| red` |
| `split` | 处理 `match` 生成的分支和否定假设 | `balanceLeft` 的 impossible branch |

### 3.2 处理 `match` 的 impossible branch

带默认分支的函数（如 `balanceLeft`）用 `split` 后，Lean 会生成否定假设：

```lean
hneg : ∀ a b c x y, ¬ (l = node red (node red a x b) y c)
```

处理模式：

```lean
exfalso
apply hneg a b c x y; rfl
```

### 3.3 自动化边界

- `aesop` / `tauto`：适合 trivial 的命题组合，但关键分支仍需手工 `rcases`。
- `ring` / `norm_num` / `positivity`：代数化简和正数证明。
- `omega` 对 `Nat` 高度最有效；涉及实数/对数时回到 `linarith` 或 `gcongr`。

### 3.4 控制 `simp`

- 优先用 `simp [lemma1, lemma2]`，避免裸 `simp` 在大文件里变慢。
- 如果 `simp` 把目标展开得太大，改用 `simp only [MyDef]` 或手动 `unfold MyDef`。
- 证明稳定后，可以建立一个局部的 `attribute [simp]` 集合，但不要随意给全局定义加 `@[simp]`。

---

## 4. 常见证明模式

### 4.1 排序算法

1. `Sorted`：按定义归纳。
2. `Permuted` / membership：通常用 `List.Perm` 或 `InTree`/`InList` 等价。
3. 循环不变式：先写 `LoopInvariant` 谓词，再证初始化、保持、终止。

### 4.2 递归数据结构（树、堆）

1. 定理的递归结构跟函数定义对齐。
2. 对树 `cases t`，子树假设直接作为 `ih`。
3. 平衡/高度性质通常需要辅助引理：`blackHeight_rotateLeft` 等。

### 4.3 贪心算法

1. **交换论证**：证明任意最优解都能逐步转换成贪心解而不变差。
2. 常用 `GreedyChoiceSafe` + `OptimalSubstructure` 两个引理。

### 4.4 图算法

1. **不变式**：如 Dijkstra 的“已确定集合到源距离最短”。
2. **割/路径证书**：证明某条边是轻边，或某条路径存在。
3. **交换引理**：MST 证明里把非贪心边换进最优解。

### 4.5 摊还分析

1. 定义 `potential` 函数。
2. 证 `potential` 非负、 telescoping。
3. 对每个操作证 `actual cost + Δpotential ≤ amortized cost`。

---

## 5. 文件与模块约定

### 5.1 目录结构

```
CLRSLean/
  Chapter_XX.lean                 # 章节导览 + namespace
  Chapter_XX/
    Section_XX_Y_Short_Name.lean  # 具体节
Tests/
  Chapter_XX_Interface.lean       # 可选的公共 API 检查
```

### 5.2 模块 doc 约定

- 模块顶部用 `/-! # Chapter/Section Title -/`。
- 内部节注释不要用 `##`，doc-gen 可能报 header nesting 错误；改用 `/-! **Section Title** -/`。
- 行内代码引用用 `{name}` 或 `{lit}` 角色：
  - `{name}`RBTree.insert``：引用 Lean 定义/定理。
  - `{lit}`RB-INSERT-FIXUP``：非 Lean 标识符的字面文本。

### 5.3 状态词

章节/定理状态统一用这几个词：

- `proved`
- `partial`
- `statement`
- `blocked-design`
- `blocked-mathlib`
- `deferred-implementation`
- `future-work`
- `out-of-scope`

---

## 6. 验证清单

每次改动后必须跑：

```bash
# 1. 当前文件
lake build CLRSLean.Chapter_XX.Section_XX_Y_Zzz

# 2. 接口测试（如果有）
lake env lean Tests/Chapter_XX_Interface.lean

# 3. 整个库
lake build CLRSLean
```

> 注意：不要只跑单个文件。上游/下游依赖经常会在全量构建时暴露问题。

---

## 7. 下一步计划（前 26 章）

| 优先级 | 章节 | 核心目标 |
|---|---|---|
| 高 | 21 | 并查集：集合划分、Find/Union 规范、Kruskal 所需的 oracle 接口 |
| 高 | 22 | 基础图算法：BFS/DFS 可达性、拓扑序、强连通分量 |
| 高 | 23 | MST：Prim 算法、自动路径/割交换边提取 |
| 中 | 24 | 单源最短路：Dijkstra、Bellman-Ford 正确性 |
| 中 | 25 | 全源最短路：Floyd-Warshall 正确性 |
| 中 | 26 | 最大流：Ford-Fulkerson/Edmonds-Karp，最大流最小割定理 |
| 低 | 1–20 打磨 | 只处理明确的 bug 或接口缺口，不主动重构 |

---

## 8. 更新记录

- **2026-07-01**：创建本文档，整合 Chapter 13 RB-INSERT 完成后的证明经验和前 26 章计划。

---

> 这份手册应该随项目演化。每当你发现一个新的常用模式、常见坑或阶段目标变化时，直接修改此文件。
