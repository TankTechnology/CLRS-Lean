# CLRS-Lean 证明技巧、策略与计划

这份文档是项目内积累的“活页手册”。
它的作用是：把反复出现的 Lean 证明技巧、章节推进策略和当前阶段计划固定下来，避免每次从零开始讨论。

---

## 1. 当前阶段目标

**第一阶段：完成 CLRS 前 26 章的主要证明。**

已经动工的章节：2–20、22、23。  
尚未开始的章节：21（并查集）、24（单源最短路）、25（全源最短路）、26（最大流）。
Chapter 22 目前部分完成：22.1 图模型、22.2 BFS 可达性正确性（soundness + completeness）、
22.3 DFS 基本颜色不变量、22.4 拓扑排序、22.5 Kosaraju SCC 结构划分已完成；
22.3 的括号定理/白路径定理/边分类、22.5 的 SCC 强连通/极大核心仍待补充。

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

本节是短版速查；跨章节的“几何形状”总览见
[`geometric-proof-patterns.md`](geometric-proof-patterns.md)。已经抽出的轻量
Lean 骨架位于 `CLRSLean/ProofPatterns/`。

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

### 4.6 函数式图搜索（BFS / DFS）

Chapter 22 的 BFS/DFS 采用**燃料（fuel）+ `Finset.toList`**的函数式模型：

- 用 `fuel : Nat` 给递归搜索定界，避免在非结构化的图上依赖 Lean 的递归判定。
- `Finset.toList` 使遍历顺序非计算性（`noncomputable`），但 Lean 的归纳证明仍然适用。
- 状态（颜色、发现/完成时间、父节点）用 record + 函数表示；对只改一个字段的更新，给每个字段写 `@[simp]` 引理，例如：
  - `setColor_color`、`setDiscovery_color`、`setFinish_color`、`setParent_color`。
- `dfsVisit` 处理邻接表时用 `List.foldl` 顺序访问邻居。证明 foldl 不变式时：
  1. 把 `foldl` 的 step 函数用 `let step := ...` 命名，方便重写。
  2. 对列表用 `induction vs generalizing s0`，归纳假设已经是“对任意 accumulator 成立”。
  3. 用 `List.foldl` 的定义把 `v :: vs` 的情况写成 `foldl step (step s0 v) vs`，再用 `by_cases` 处理 `step` 里的 `if color v = white`。
- DFS 颜色不变式（“不引入新的灰色顶点”）的经验：
  - 对固定顶点 `w` 做燃料归纳，而不是把 `w` 也泛化；这样外层 IH 直接关于 `w`，在 foldl 子引理中不需要再次实例化 `w`。
  - 先证单步 `dfsVisit` 的不变式，再证 `dfsFromList` 保持“无灰色”和“所有顶点变黑”。

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

## 7. 质量保证与数据集准备

### 7.1 章节完成审计

每完成一章并宣称“主要证明完成”，必须跑 `docs/proof-audits/chapter-completion-audit.md` 的检查清单：

- `lake build CLRSLean` 通过；
- 无 `sorry` / `admit` / `axiom`；
- 公共定理用 `#print axioms` 检查；
- 文档、章节导览、`literate.toml`、`docs/proof-map.md` 同步更新。

### 7.2 网站结构一致性

`docs/proof-audits/site-consistency-audit.md` 记录了当前网站结构、一致性问题及修复建议：

- `docs/chapters/chapter-XX.md` 部分章节有、部分没有，需要统一处理；
- Chapter 17 的 `literate.toml` 标题/排序需要核对；
- 三个状态来源（CSV、proof-status-board、Status.lean）需要保持一致。

### 7.3 数据集准备

未来若把本项目抽象成 agent Lean 证明能力评测数据集，参见
`docs/proof-audits/dataset-readiness-checklist.md`：

- 每个公共定理作为一个 task；
- 隐藏测试桩只暴露定理声明，不暴露 gold proof；
- 按章节/难度打标签；
- 用 `lake build` 作为通过标准。

---

## 8. 下一步计划（前 26 章）

阶段目标是**让第 1–26 章都有完整的主要证明**。已经动工但仍有中心缺口的章节放在最后集中收尾；优先补全完全空白的图算法章节，因为它们互相依赖。

### Sprint 1：图论基础（Chapter 22）

这是所有后续图算法的公共依赖，必须先做。

**已完成：**

- 22.1 有限图模型：顶点集 `V`、邻接函数、walk/path/cycle、reachable、connected component、无向图对称性。
- 22.2 BFS：函数式队列 BFS，证明 `bfs_sound`（访问到的顶点均从源点可达）和
  `bfs_complete`（所有可达顶点都会被访问）。
- 22.3 DFS：函数式 fuel 模型，白/灰/黑颜色、发现/完成时间、父指针；证明基本颜色不变量
  `dfsVisit_blackens_u`、`dfsVisit_preserves_black`、`dfsVisit_no_new_gray`，以及全局结论
  `dfs_all_black`（`dfs` 后所有顶点为黑色）。

**仍待完成：**

- 22.3 括号定理、白路径定理、边分类（tree/back/forward/cross）。
- 22.5 强连通分量核心：将 Kosaraju 每个输出块证为强连通且极大，依赖于 DFS 完成时间序的
  SCC 源点引理（当前以 `sorry` 隔离）。

**已完成（Kahn 算法版本）：**

- 22.4 拓扑排序：定义 `IsDAG`（无非平凡自环路径）、入度、拓扑序；实现 Kahn 算法；证明
  `topologicalSort_isTopologicalOrder`（对任意 DAG 返回合法拓扑序）。
  关键引理：`finite_DAG_wellFoundedOn`（有限 DAG 上的邻接关系良基），用于保证每一步都存在源点。

**已完成（Kosaraju 结构层）：**

- 22.5 强连通分量：实现 `transpose`、`StronglyConnected`、`IsSCC`、`IsSCCPartition`、
  `dfsFromListCollect`、`kosarajuComponents`；证明 Kosaraju 返回的每个分量都是非空顶点子集、
  分量两两不交、所有顶点都被覆盖，即 `kosarajuComponents_isSCCPartition` 的结构部分。
  强连通性与极大性核心已归约为 `kosarajuComponent_scc_core`，并进一步隔离为
  `scc_finish_order`（DFS 完成时间序的 SCC 源点引理），当前用 `sorry` 占位。

**交付文件（状态）：**

- `CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean` ✅
- `CLRSLean/Chapter_22/Section_22_2_BFS.lean` ✅（soundness + completeness; shortest-path distances remain）
- `CLRSLean/Chapter_22/Section_22_3_DFS.lean` ✅（partial）
- `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean` ✅
- `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean` ✅（partial，SCC 核心 deferred）

### Sprint 2：并查集（Chapter 21）

为 MST 的 Kruskal 提供具体实现，替换当前的 `ComponentOracle` 接口。

- 定义集合划分 `Partition` 和等价关系。
- 实现 `makeSet` / `find` / `union`。
- 证明：
  - `find` 返回元素所在集合的代表元；
  - `union` 合并两个集合；
  - 按秩合并 + 路径压缩的规范（可先不做复杂摊还，只证功能正确性）。
- 可选：把 Chapter 23 的 Kruskal 从 `ComponentOracle` 细化到并查集实现。

### Sprint 3：最小生成树收尾（Chapter 23）

当前 MST 已有 cut property 和 Kruskal 框架，缺 Prim 和自动交换边提取。

- 证明具体的路径/割交换边引理（path/cycle boundary-edge extraction）。
- 实现 Prim 算法（函数式优先队列版本）。
- 证明 Prim 返回 MST。
- 更新 `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`。

### Sprint 4：单源最短路（Chapter 24）

- 定义带权图、最短路径权重、松弛操作 `relax`。
- 实现 Dijkstra（优先队列 + 非负权假设）。
- 实现 Bellman-Ford，包括负环检测。
- 证明：
  - Dijkstra 的最优性（三角不等式 + 已确定集合不变式）；
  - Bellman-Ford 在无负环时正确；
  - Bellman-Ford 可检测负环。

### Sprint 5：全源最短路（Chapter 25）

- 实现 Floyd-Warshall（矩阵/函数式 `n × n` 数组）。
- 证明：
  - 动态规划递推正确；
  - 最终矩阵给出所有顶点对最短路径权重。
- 可选：矩阵乘法快速幂路径计数 / 传递闭包。

### Sprint 6：最大流（Chapter 26）

- 定义流网络、容量约束、守恒条件、流值。
- 定义残差网络 `residualNetwork` 和增广路径。
- 实现 Ford-Fulkerson / Edmonds-Karp。
- 证明：
  - 增广保持合法流；
  - 最大流最小割定理；
  - Edmonds-Karp 终止（可选：多项式轮数）。

### Sprint 7：已有章节的中心缺口收尾

按“补完主要证明即可”的标准处理：

| 章节 | 收尾目标 |
|---|---|
| 4 | Master Theorem case-3 的 comparison-scale 包装 |
| 11.2 | 从 finite-uniform bucket 模型升级到 random-key/hash-function 期望模型（如时间不够可先标记 `blocked-design`） |
| 12.1 | 若课本“主要证明”接受函数式 BST，则保持现状；否则加 parent-pointer/transplant 层 |
| 13.1 | `RB-DELETE` / `RB-DELETE-FIXUP`、对数高度定理 |
| 14.1 | 把 size-preserving 旋转接到红黑树平衡上 |
| 15 | 可执行的 matrix-chain / LCS 表格重建 |
| 17 | 可选：array-level dynamic-table 摊还模型 |
| 18–20 | 若时间不够，保持当前数学模型并明确标记为 `partial`；它们不是前 26 章的主要阻塞项 |

### 当前推荐立即启动的 Sprint

**Sprint 1（Chapter 22）**。它为 21、23、24、25、26 提供图论公共语言，做完后其余 sprint 可以并行或按顺序快速推进。

---

## 9. 更新记录

- **2026-07-01**：创建本文档，整合 Chapter 13 RB-INSERT 完成后的证明经验和前 26 章计划。
- **2026-07-01**：细化下一步计划为 7 个 Sprint，优先启动 Chapter 22 图论基础。
- **2026-07-01**：完成 Chapter 22 的 22.1–22.3，补充函数式图搜索的燃料/foldl 不变式经验，并更新 Sprint 1 进度。
- **2026-07-01**：完成 Section 22.4 Kahn 拓扑排序，并记录“有限 DAG 的邻接关系良基 → 源点存在”这一证明路径。
- **2026-07-01**：完成 Section 22.5 Kosaraju SCC 算法及结构划分性质（子集、不交、覆盖、非空），将强连通/极大核心归约为 DFS 完成时间引理并以 `sorry` 占位。
- **2026-07-05**：完成 Section 22.2 BFS 完备性证明，通过暴露内部队列并建立闭包/终止测度不变式。
- **2026-07-05**：将 SCC 核心进一步隔离为命名的 `scc_finish_order` 引理（DFS 完成时间序的 SCC 源点性质），为后续补全 DFS 理论提供明确目标。

---

> 这份手册应该随项目演化。每当你发现一个新的常用模式、常见坑或阶段目标变化时，直接修改此文件。
