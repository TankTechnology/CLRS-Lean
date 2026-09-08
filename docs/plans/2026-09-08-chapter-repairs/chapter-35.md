# 第 35 章修复与验证

对应 [#375](https://github.com/TankTechnology/CLRS-Lean/issues/375)。历史审查快照保持不变，集成状态由本目录 index 记录。

- `TSP.GraphAdapter.graphTour` 从完整的 `Fin n` 自然权重图及根开始，调用第 21 章 Prim frontier 构造，建立分量查询精确性和生成树证明，再用最短跳数前驱将选定边根化。父边到选定边的单射及竞争树的边集合转换建立成本比较。`graphTour_two_approx` 无需调用者提供 MST 或 parent adapter，只要求对称、三角不等式、零自环和竞争巡回。根参数意味着非空顶点域；根化与分量查询为经典有限构造，没有运行时间声明。
- `greedySetCover_card_eq_cost` 对同一选取递归证明实际返回集合族的基数等于旧 pick count；`greedySetCover_card_approx` 与 `greedySetCover_card_ln_approx` 将两种近似界应用于返回值。
- `RandomizedLP.VertexCoverLP.program` 由图构造边约束、非负与上界约束，以负权重目标调用第 29 章 `initializedSimplex`。全一向量证明可行，非负权重排除无界分支，保留实际返回的最优向量。竞争覆盖的指示向量可行，由最优性推出目标下界；在半阈值舍入后，`execute_correct` 直接证明输出覆盖及对任意竞争覆盖的二倍权重界。没有输入 fractional optimum 或 `hLP` 前提。
- LP 输入权重为非负有理数，返回的分数向量属于实数；这是经典精确实数求解组合，未声称可计算有理最优解、SIMPLEX 多项式时间或位复杂度。自环给出 `2x≥1`，半阈值仍包括该顶点；零权重与空边集均被覆盖。
- 明确 MAX-3-CNF 为无权 `Finset` 子句，重复子句会合并，每个子句有三个不同变量。保留并突出已经闭合的实际计数 SUBSET-SUM FPTAS，不再把它描述为仅有中间表长界。

验证：第 35 章构建成功（8,649 项）。`Chapter_35_Adapters` 回归包括空集合覆盖、单一覆盖集、单顶点与零权重 TSP，以及正权二顶点图和实际存在的竞争巡回。`Chapter_35_VertexCoverLP` 回归包括零向量不可行、端点指示向量可行、实际求解输出的覆盖/比率、自环、零权重、空边集与空顶点域。所有新增旗舰接口公理断言通过。图根化、集合族桥和 LP 组合经过源码复核，LP 另有独立审查；没有发现待处理问题。

最终全库构建与全部章节信任检查以 [统一验收记录](verification.md) 为准。
