# CLRS 与 TCS 形式化执行方案

本文档整理一个分阶段执行方案。核心目标是先用人类研究者和现成大模型 agent
推进 CLRS 经典算法证明，再逐步扩展到 CLRS proof map 和 TCS 论文形式化。

当前阶段：Synthesis。

也就是说，我们已经有 Huffman V2 和 MST cut-property 起点，但还没有到“形式化
整本 CLRS”或“训练专用 Lean 模型”的阶段。当前最重要的是形成稳定的执行节奏、
证明资产和可审计的失败记录。

## 1. 总体原则

主线不是训练模型，而是建设形式化证明资产。

短中期优先顺序：

1. 用人类 + 现成大模型 agent 完成 CLRS 经典算法证明；
2. 建立 CLRS proof map，逐步覆盖主要章节的重要定理；
3. 在 CLRS 资产稳定后，挑选适合的 TCS 论文做形式化试点；
4. 模型训练暂不作为早期目标，只保留数据记录和未来可选接口。

这意味着，早期不自训 Qwen-7B，不把 RL 作为推进 CLRS 的必要条件。我们尽量使用
已经训好的大模型，通过更好的 theorem interface、proof-pattern catalog、任务拆解
和验证工作流来提高证明效率。

## 2. 当前资产

已经完成或开始的核心资产：

```text
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
docs/clrs-lean-research-plan.md
docs/proof-map.md
docs/huffman-optimality-v2.md
docs/proof-patterns-catalog.md
```

当前代表性定理：

```lean
HuffmanV2.optimum_huffman_freqs
CLRS.MST.safe_edge_of_lightest_crossing
CLRS.MST.mst_exchange_step
```

它们分别代表两类重要证明模式：

- Huffman：exchange argument / local tree transformation；
- MST：cut property / safe edge / exchange step。

这已经足够作为 CLRS 形式化路线的起点，但还不足以支撑“全书证明”或“TCS 论文
形式化”的强叙事。下一步需要扩大算法样本，并同步整理证明模式。

## 3. 阶段一：经典算法核心证明

目标：先完成一批 CLRS 中最能代表不同证明模式的算法。

建议优先队列：

1. Huffman coding；
2. MST/Kruskal；
3. Dijkstra；
4. LCS 或 edit distance；
5. Bellman-Ford 或 BFS shortest path；
6. Matrix-chain multiplication 或 amortized analysis 样本。

每个算法都应产出四件东西：

- 数学 specification；
- 算法定义或抽象算法接口；
- correctness / optimality theorem；
- proof-pattern note。

### 3.1 Huffman

状态：已有 V2 单文件完整证明。

短期策略：

- 冻结主证明结构；
- 不为了极限压行数破坏可读性；
- 整理 theorem chain、关键 lemma 和证明模式；
- 把 Huffman 作为 greedy exchange 的旗舰 case study。

### 3.2 MST/Kruskal

状态：已有 cut property / safe edge 证明核。

当前文件：

```text
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
```

下一步：

1. 定义有限图、边权、生成树、连通性或等价的 spanning-tree spec；
2. 将 `CutCertificate` 落到具体有限图；
3. 证明 cut property 的图论证书；
4. 推进 Kruskal 数学版最优性；
5. 暂缓 union-find 性能实现。

验收标准：

```lean
theorem kruskal_optimal :
  IsMST (kruskal G)
```

早期可以先证明数学版 Kruskal，不要求证明高性能并查集实现。

### 3.3 Dijkstra

证明模式：loop invariant / settled set / relaxation。

建议先做数学状态版，而不是 priority queue 实现版。

核心对象：

- 非负权图；
- source；
- distance map；
- settled set；
- relaxation invariant；
- shortest-path specification。

验收标准：

```lean
theorem dijkstra_correct :
  ShortestPathDistances G source (dijkstra G source)
```

降级方案：

- 如果 Dijkstra 状态机过重，先做 Bellman-Ford；
- 如果 weighted graph 过重，先做 BFS shortest path；
- 保留 Dijkstra theorem interface 和 invariant 草案。

### 3.4 DP 样本

证明模式：optimal substructure / recurrence correctness。

建议优先 LCS 或 edit distance。

原因：

- specification 清晰；
- 和教材连接强；
- 能补足 greedy / graph 之外的证明模式。

验收标准：

```lean
theorem lcs_correct :
  IsLongestCommonSubsequence xs ys (lcs xs ys)
```

如果时间不足，可以先用已有 DP 小题作为 proof-pattern 证据，但最终最好完成一个
教材级 DP 样本。

## 4. 阶段二：CLRS proof map

目标：从“几个经典算法证明”扩展到“CLRS 主要证明地图”。

这里不要求证明全书，也不承诺全部定理都解决。关键是把全书主要证明分成状态清楚
的 buckets。

建议状态分类：

| 状态 | 含义 |
|------|------|
| `proved` | 主库中已有 sorry-free Lean theorem |
| `statement` | theorem interface 已写出，但证明未完成 |
| `partial` | 有关键 lemma 或局部证明，但主定理未完成 |
| `blocked-mathlib` | 卡在 Mathlib 缺口或基础库缺失 |
| `blocked-design` | 卡在表示层设计，例如图、路径、数组、概率模型 |
| `out-of-scope` | 当前阶段不做，例如复杂实现细节或低收益章节 |

主构建路径必须保持 `sorry-free`。未完成的 theorem 不应作为 `axiom` 混进主库。

推荐组织方式：

```text
docs/proof-map.md
docs/chapters/
docs/status/
CLRSLean/
  Chapter_16/
  Chapter_23/
  Blueprint/
```

其中：

- `CLRSLean/Chapter_*/*` 只放可构建、可维护的正式证明；
- `CLRSLean/Blueprint/` 可后续放 theorem statement 或探索性接口，但默认不进入完成状态；
- 未解决问题优先记录在 docs，而不是用不可靠公理伪装成完成。

阶段二的成功标准不是“全书都证明”，而是：

- 主要章节有 proof map；
- 每个重要 theorem 有状态；
- 未解决项有清楚原因；
- 已完成 theorem 能通过 `lake build`；
- proof-pattern catalog 能解释重复出现的证明套路。

## 5. 阶段三：TCS 论文形式化试点

TCS 论文形式化不宜过早全面展开。

启动条件：

- Huffman、MST、Dijkstra、DP 至少三个 case study 稳定；
- 有基本的图、路径、权重、最优性、递推等 proof infrastructure；
- proof map 能展示我们不是在做孤立例子；
- agent 工作流已经能稳定辅助 Lean 证明。

优先选择的论文类型：

- 和 CLRS 资产相邻的图算法论文；
- 贪心、交换论证、cut property 相关论文；
- 动态规划或近似算法；
- 摊还分析；
- 随机算法的基础部分。

暂不建议一开始选：

- 依赖大型概率论背景的论文；
- 需要复杂代数、范畴或测度基础的论文；
- 定义体系过重但和 CLRS 资产无明显复用关系的现代 TCS 论文；
- 需要证明大规模工程系统实现正确性的论文。

阶段三的第一个目标不是“形式化一篇完整 TCS 论文”，而是做一个 narrow pilot：

- 选择一篇论文中的一个核心 theorem；
- 写出 Lean statement；
- 证明核心 lemma 或给出 blocked reason；
- 记录它复用了哪些 CLRS proof infrastructure；
- 评估是否值得扩展为完整论文形式化项目。

## 6. 模型与 Agent 策略

早期不自训模型。

原因：

- 训练 Qwen-7B 或做 RL 和当前 CLRS 证明主线耦合较弱；
- 数据集、reward、环境、算力和评估都需要单独工程投入；
- 在证明资产不足时训练，容易得到只能做局部 tactic 的模型；
- 使用现成强模型可以更快推进算法证明本身。

当前策略：

1. 使用现成大模型 agent 完成人类可审阅的证明任务；
2. 把任务拆成 theorem statement、lemma、proof pattern、verification command；
3. 每次失败记录 blocked reason，而不是只保留成功证明；
4. 把 proof attempts 转化为未来可用的 benchmark 数据。

可记录的数据：

- theorem statement；
- imports；
- proof state；
- 失败尝试；
- 最终证明；
- 构建命令；
- 人类介入点；
- proof-pattern 标签。

未来如果要训练模型，建议顺序是：

1. 先做 eval benchmark；
2. 再做 supervised fine-tuning；
3. 最后才考虑 RL；
4. reward 先用 Lean 编译通过与否，不先设计复杂过程奖励。

也就是说，模型训练是远期增强，不是早期依赖。

## 7. 人类与 Agent 分工

人类主要负责：

- 选择证明目标；
- 判断 theorem statement 是否有数学意义；
- 决定表示层设计；
- 审查证明是否匹配教材叙事；
- 判断 blocked reason 是否真实。

Agent 主要负责：

- 搜索现有 lemma；
- 起草 Lean definitions；
- 分解 proof obligations；
- 完成局部证明；
- 跑 `lake env lean` 和 `lake build`；
- 维护 proof-pattern notes 和 proof map。

对复杂算法，推荐工作循环：

1. 人类和 agent 先定 theorem interface；
2. agent 写最小定义和接口检查；
3. 人类确认 statement 没有偷换目标；
4. agent 证明局部 lemma；
5. 每完成一层就跑构建；
6. 同步更新 proof-pattern catalog；
7. 卡住时记录 blocked reason，而不是硬塞公理。

## 8. 近期里程碑

### 里程碑 A：MST 核心闭环

目标：

- 从当前 `safe_edge_of_lightest_crossing` 推进到 Kruskal 数学版最优性。

交付物：

- finite graph specification；
- spanning tree specification；
- cut exchange certificate；
- Kruskal theorem statement；
- Kruskal optimality proof 或明确 blocked reason。

### 里程碑 B：Dijkstra theorem interface

目标：

- 先不急着证明完整实现，先冻结 statement 和 invariant。

交付物：

- nonnegative weighted graph；
- path weight；
- shortest distance；
- Dijkstra state；
- settled-set invariant；
- `dijkstra_correct` statement。

### 里程碑 C：CLRS proof map 初版

目标：

- 把 CLRS 主要章节的重要证明列出来并分类。

交付物：

- `docs/proof-map.md`；
- 状态分类表；
- 每个章节 3-10 个候选 theorem；
- 每个 theorem 的 status / priority / blocked reason。

### 里程碑 D：Proof-pattern catalog 升级

目标：

- 从 Codeforces proof patterns 升级到 CLRS proof patterns。

新增模式：

- exchange argument；
- cut property；
- loop invariant；
- relaxation invariant；
- optimal substructure；
- recurrence completeness；
- amortized potential。

## 9. 投稿和产出路径

短期产出：

- Huffman V2 技术说明；
- MST/Kruskal proof note；
- CLRS proof map；
- proof-pattern catalog；
- technical blog 或 workshop note。

中期产出：

- 形式化 CLRS 经典算法证明 artifact；
- proof-pattern methodology paper；
- Lean proof-agent benchmark；
- ITP/CPP 风格论文或 artifact paper。

长期产出：

- CLRS 主要证明的持续扩展；
- TCS 论文形式化试点；
- 证明 agent 数据集和评测；
- 可选的模型微调或 RL 实验。

不建议短期承诺：

- 完整形式化 CLRS 全书；
- 自训模型超过现成大模型；
- 形式化高难 TCS 论文全集；
- 用 agent 全自动完成复杂算法证明。

## 10. 下一步

最直接的下一步是继续 MST。

建议执行顺序：

1. 在 `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
   中继续补 cut exchange 的具体有限图证明；
2. 证明当前 `CutCertificate` 可以从具体 cut exchange 构造出来；
3. 在 `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean` 中强化
   `kruskal_optimal`，去掉 sorted-order 和 final spanning tree 的外部假设；
4. 若完整 Kruskal 太重，先完成数学版 safe-edge induction；
5. 同步维护 `docs/proof-map.md`，记录 MST、Dijkstra、DP 的状态。

这条路线能保持早期工作聚焦：不用先训练模型，也不用立刻形式化全书，而是一步步
把 CLRS 的关键证明变成可构建、可复用、可投稿的 Lean artifact。
