# CLRS 算法证明 Lean 化研究计划

本文档给出一个 3 个月左右的研究推进计划。目标不是把 CLRS 全书形式化，
而是围绕一组有代表性的算法证明，建立可复用的 Lean 证明模式，并形成可投稿
的 artifact 和方法论叙事。

当前阶段：Synthesis。

也就是说，我们已经有一些可用材料，尤其是 Huffman V2 最优性证明，但还不能
直接进入投稿包装阶段。接下来最重要的是把研究问题、算法样本、验收标准和失败
降级路径固定下来。

## 1. 核心判断

只证明一批基础贪心小题，不足以支撑强投稿。

更合理的目标是：

> 证明一组 CLRS 风格的非平凡算法正确性，并从中提炼可复用的 Lean 证明模式。

这个方向的价值不在于“Lean 里又有几个算法定理”，而在于回答：

- 经典算法教材里的证明套路，能否被组织成稳定的形式化模式；
- 哪些证明模式可以复用，哪些地方会被 Lean 的数据结构和不变量逼出新设计；
- 对后续大规模形式化算法教材，有哪些可迁移的工程与证明经验。

## 2. 当前基线

已经具备的旗舰样本：

```text
CfProofs/Greedy/HuffmanV2/Optimality.lean
```

当前 Huffman V2 的特点：

- 与旧版 `CfProofs.Greedy.Huffman.*` 路径隔离；
- 一个文件内包含完整 Huffman 最优性证明；
- 证明主线是 split-leaf / exchange；
- 当前规模约 2971 行；
- 对外暴露频率表级别最终定理：

```lean
HuffmanV2.optimum_huffman_freqs
```

Huffman V2 可以作为论文里的第一个核心 case study，因为它包含真正的最优性
交换论证，而不是只验证一个程序返回值。

## 3. 候选研究问题

下面的问题按高度分层。最终不建议同时主打全部问题，而是选一个 headline
question，再配 1-2 个支撑问题。

### Q1. 能否把 CLRS 风格算法证明组织成 Lean 中可复用的证明模式？

高度：结构性问题。

这个问题适合作为主问题。它高于单个算法，又可以用 3-5 个算法样本来回答。

主要风险是：如果每个算法都只是一次性证明，缺少共享接口和模式总结，这个问题会
退化成 case-study collection。

### Q2. 贪心算法的 exchange / cut / local transformation 证明能否统一？

高度：机制问题。

这个问题适合作为支撑问题。Huffman 使用 split-leaf / exchange，MST 使用 cut
property，活动选择或区间类问题使用 exchange argument。它们有共同的局部替换
味道，但 Lean 中是否能共享同一套抽象，需要通过实际形式化检验。

### Q3. 循环不变量类算法在 Lean 中应该用执行程序证明，还是数学状态关系证明？

高度：机制问题。

这个问题适合覆盖 Dijkstra、BFS、Bellman-Ford 这类算法。关键不是代码执行本身，
而是 settled set、distance map、relaxation invariant 这些状态不变量怎样表达。

### Q4. DP 最优子结构证明能否形成稳定模板？

高度：机制问题。

这个问题适合用 LCS、edit distance、matrix-chain multiplication 或已有
CutRibbon/Boredom 经验扩展。DP 的难点通常是 recurrence、可达性、最优下界和
数组/列表实现之间的桥接。

### Q5. 单文件证明和模块化证明各自适合什么阶段？

高度：工程问题。

Huffman V2 展示了单文件证明更利于阅读和投稿 artifact 展示；但多算法推进时，
完全单文件会降低复用性。这个问题适合放在经验总结中，不适合作为主问题。

### Q6. 形式化教材算法时，真正的瓶颈是数学证明，还是表示层设计？

高度：结构性问题。

这个问题很有价值，但容易过宽。可以作为讨论章节中的横向发现：很多困难不是算法
思想本身，而是频率表、图、路径、森林、不变量这些对象的 Lean 表示选择。

### Q7. 能否用小型 proof-pattern catalog 降低后续算法证明成本？

高度：方法问题。

这个问题可以变成 artifact 贡献：每个 case study 都输出 theorem interface、
proof skeleton、关键 lemma 类型和复用记录。

### Q8. 现有 Mathlib 对算法教材证明的支撑缺口在哪里？

高度：生态问题。

这个问题适合做补充贡献。不要把它作为主问题，因为 3 个月内很难系统评价整个
Mathlib，只能从样本中归纳局部缺口。

## 4. 审稿式自查结论

最适合的主问题：

> CLRS 风格的非平凡算法正确性证明，能否在 Lean 中被组织成可复用的证明模式，
> 而不是彼此孤立的一次性形式化？

支撑问题：

1. Greedy optimality 中的 exchange / cut / local transformation 如何形式化？
2. Loop invariant 和 DP optimal substructure 如何转化成稳定的 theorem interface？

不建议主打的问题：

- “形式化整个 CLRS”：3 个月不现实，容易显得承诺过大；
- “突破数学难题”：与当前 repo 资产不连续，短期风险过高；
- “证明很多基础算法”：数量多但深度不够，投稿时容易被看成教学练习；
- “只做 Huffman”：深度不错，但样本单一，很难支撑方法论贡献。

## 5. 目标算法组合

建议 3 个月内完成或接近完成下面四类核心样本。

### A. Huffman coding

证明模式：exchange argument / local tree transformation。

当前状态：V2 已是核心基线。

目标：

- 保持单文件证明可读；
- 继续压缩局部冗余，但不牺牲主线结构；
- 为论文写出证明路线图和 LOC / lemma 分布记录。

### B. MST: Kruskal 或 Prim

证明模式：cut property / safe edge。

建议优先 Kruskal。

理由：

- CLRS 代表性强；
- cut property 和 Huffman 的 exchange 可以形成对照；
- 并查集实现可以先抽象成 relation / component spec，不必一开始证明高性能
  union-find。

最低验收：

```lean
theorem kruskal_optimal :
  IsMST (kruskal G)
```

可以先证明数学版 Kruskal，再逐步连接到可执行实现。

### C. Dijkstra shortest paths

证明模式：loop invariant / settled set / relaxation。

理由：

- 比基础贪心题更有含金量；
- 与 MST 同属图算法，但证明结构不同；
- 能展示 Lean 中状态不变量的表达能力。

最低验收：

```lean
theorem dijkstra_correct :
  ShortestPathDistances G source (dijkstra G source)
```

可以先限制非负权重、有限节点、简单 map 表示，避免一开始陷入堆实现。

### D. 一个 DP 算法

证明模式：optimal substructure / recurrence completeness。

候选：

- LCS；
- edit distance；
- matrix-chain multiplication。

建议优先 LCS 或 edit distance，因为 specification 更直观，适合和教材叙事连接。

最低验收：

```lean
theorem lcs_correct :
  IsLongestCommonSubsequence xs ys (lcs xs ys)
```

如果时间不足，可以用已有 CutRibbon/Boredom 作为预实验，再完成一个更教材化的
DP 样本。

## 6. 不做什么

为了保持论文目标清晰，建议明确以下 non-goals：

- 不试图在 3 个月内形式化 CLRS 全书；
- 不把高性能数据结构实现作为第一目标；
- 不以 Codeforces 小题数量作为主要贡献；
- 不追求所有算法都 executable-first；
- 不承诺证明复杂度界，除非主正确性证明已经稳定。

复杂度证明可以作为加分项，但不应阻塞主线。

## 7. 3 个月里程碑

### 第 1-2 周：研究问题与接口冻结

交付物：

- 固定本文档中的 headline question；
- 建立 `docs/clrs-proof-patterns/` 或同等目录；
- 为 Huffman、MST、Dijkstra、DP 各写一页 theorem interface 草案；
- 记录 Huffman V2 的 theorem chain、LOC、核心 lemma 分类。

验收标准：

- 每个目标算法都有明确 spec；
- 每个 spec 都能说清楚“证明什么”和“不证明什么”；
- 不再用“证明很多算法”作为目标描述。

### 第 3-5 周：MST/Kruskal

交付物：

- 图、边权、生成树、cut、safe edge 的数学定义；
- cut property；
- Kruskal 数学版最优性证明；
- 记录哪些 lemma 可复用到其他 greedy proofs。

验收标准：

- `lake build` 通过；
- 有一个公开 theorem 表达 MST 最优性；
- 文档中能解释 Kruskal 和 Huffman 交换证明的共同点与差异。

### 第 6-8 周：Dijkstra

交付物：

- 非负权图和距离 specification；
- relaxation invariant；
- settled nodes invariant；
- Dijkstra 正确性主定理。

验收标准：

- 可以清楚区分算法状态、数学最短路定义、循环不变量；
- 不依赖具体 priority queue 性能实现；
- 文档中记录 invariant 证明模式。

### 第 9-10 周：DP 样本

交付物：

- LCS 或 edit distance 的 specification；
- recurrence 正确性；
- 算法返回值的 optimality theorem；
- 与已有 DP 小题证明做对照。

验收标准：

- 有一个教材级 DP theorem；
- proof pattern catalog 中新增 DP optimal-substructure 模式。

### 第 11 周：横向整理

交付物：

- 证明模式 taxonomy；
- 每个算法的 theorem interface 表；
- LOC、lemma 数量、复用点、失败尝试记录；
- Mathlib / Lean 表示层缺口记录。

验收标准：

- 可以回答“这不是四个孤立证明，而是一套方法”的审稿问题；
- 可以回答“为什么这些算法足够代表 CLRS 证明模式”的审稿问题。

### 第 12 周：投稿材料初稿

交付物：

- 论文 outline；
- artifact README；
- case study 表格；
- reproducibility commands；
- intro 的问题陈述和贡献列表。

验收标准：

- 形成 ITP/CPP 风格 submission skeleton；
- 如果结果更强，再考虑 CAV 风格 framing；
- 如果算法数不足，降级为 workshop / artifact / technical report 也仍然成立。

## 8. 文件结构建议

短期已经将 CLRS 方向从 `CfProofs` 拆到独立的 `CLRSLean` repository。Huffman V2
成为第 16.3 节的正式章节文件：

```text
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
```

新增 CLRS 方向时，按 CLRS 章节和小节组织，而不是按算法主题组织：

```text
CLRSLean/
  Chapter_16/
    Section_16_3_Huffman_Codes.lean
  Chapter_23/
    Section_23_1_Growing_Minimum_Spanning_Trees.lean
    Section_23_2_Kruskal_And_Prim.lean
  Blueprint/
```

注意：`Patterns/` 不要一开始过度抽象。更稳妥的做法是先完成两个 case study，
再把重复出现的结构抽出来。

## 9. 论文贡献形态

推荐贡献列表：

1. 一个 Lean 4 artifact，覆盖 Huffman、MST、Dijkstra 和一个 DP 算法；
2. 一套 CLRS proof-pattern taxonomy；
3. 每类证明模式的 theorem interface 和 proof skeleton；
4. 对 Lean/Mathlib 表示层选择的经验总结；
5. 一个可复现实验表：每个算法的 LOC、关键 lemma、复用点、构建命令。

不要把贡献写成：

- “我们证明了很多算法”；
- “Lean 可以证明算法正确性”；
- “形式化 CLRS 是可行的”。

这些说法太宽或太弱。更好的表述是：

> We identify and mechanize reusable proof patterns for textbook algorithm
> correctness in Lean, using representative CLRS algorithms as case studies.

## 10. 风险与降级路径

### 风险 1：Dijkstra 证明拖太久

降级：

- 保留 Dijkstra 的 specification 和 invariant 草案；
- 用 BFS shortest path 或 Bellman-Ford 的数学版替代；
- 论文中把 Dijkstra 作为 ongoing extension，而不是核心结果。

### 风险 2：MST 陷入图表示和 union-find 实现

降级：

- 先证明数学版 Kruskal；
- union-find 只作为 future executable refinement；
- 主贡献聚焦 cut property 和 safe edge。

### 风险 3：DP 样本无法在时间内完成

降级：

- 用已有 CutRibbon/Boredom 作为 DP pattern 证据；
- 同时保留 LCS 的 spec 和部分 lemma；
- 不把 DP 放在核心贡献第一位。

### 风险 4：证明模式抽象不够统一

降级：

- 不强行做通用 framework；
- 把贡献改成 “design study + reusable interfaces”；
- 用表格展示哪些部分可复用、哪些部分不可复用。

## 11. 验收标准

3 个月后，一个强版本应该满足：

- Huffman V2 保持完整、可构建、可解释；
- MST 和 Dijkstra 至少各有一个主正确性 theorem；
- DP 至少有一个教材级样本或清楚的替代证据；
- 每个算法都有文档化的 theorem interface；
- 有 proof-pattern catalog，而不是只堆 Lean 文件；
- `lake build` 是 artifact 的基本复现入口。

一个可接受的降级版本应该满足：

- Huffman V2 + MST 完整；
- Dijkstra 或 DP 至少一个完整；
- 另一个有 spec、partial proof 和明确风险记录；
- 论文目标降为 ITP/CPP workshop、artifact paper 或 technical report。

## 12. 下一步

立即建议做三件事：

1. 冻结 Huffman V2，不再为了极限压行数破坏主线可读性；
2. 新建 CLRS 隔离目录，先写 MST/Kruskal 的 specification 和 theorem statement；
3. 同步维护一个 `proof-patterns` 表格，每完成一个 lemma 就记录它属于 exchange、
   cut、loop invariant 还是 optimal substructure。

第一段真正的新增证明，建议从 Kruskal 的 cut property 开始。它和 Huffman 一样有
贪心最优性味道，但证明形态不同，能最快把项目从“一个强 Huffman 证明”推进到
“一组 CLRS 证明模式”的方向。
